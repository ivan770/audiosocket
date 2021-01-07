//! AudioSocket is a simple TCP-based protocol for sending and receiving real-time audio streams.
//!
//! This crate is a port of a [Go library](https://github.com/CyCoreSystems/audiosocket).
//!
//! ```
//! use std::{convert::TryFrom, str::FromStr};
//!
//! use audiosocket::{Message, RawMessage, Type};
//! use uuid::Uuid;
//!
//! let recv = [
//!     // Message contains a stream identifier.
//!     1u8,
//!
//!     // Payload length is 16 bytes.
//!     0,
//!     16,
//!
//!     // Payload with UUID.
//!     4,
//!     54,
//!     67,
//!     12,
//!     43,
//!     2,
//!     98,
//!     76,
//!     32,
//!     50,
//!     87,
//!     5,
//!     1,
//!     33,
//!     43,
//!     87
//! ];
//!
//! let raw_message = RawMessage::try_from(&recv[..]).unwrap();
//! assert_eq!(*raw_message.message_type(), Type::Identifier);
//!
//! let message = Message::try_from(raw_message).unwrap();
//! assert_eq!(message, Message::Identifier(Uuid::from_str("0436430c-2b02-624c-2032-570501212b57").unwrap()))
//! ```

use std::{
    array::TryFromSliceError,
    convert::{TryFrom, TryInto},
};

use num_enum::{TryFromPrimitive, TryFromPrimitiveError};
use thiserror::Error;
use uuid::{Error as UuidError, Uuid};

/// Library errors.
///
/// Note that this list doesn't contain Asterisk errors,
/// that are sent via AudioSocket messages (use [`ErrorType`] for that purpose).
#[derive(Error, Debug)]
pub enum AudioSocketError {
    #[error("Message contains empty payload, despite having type that doesn't support it")]
    EmptyPayload,

    #[error("UUID provided in payload is invalid")]
    InvalidIdentifier(UuidError),

    #[error("Payload contained invalid message type")]
    IncorrectMessageType(TryFromPrimitiveError<Type>),

    #[error("Payload contained invalid error code")]
    IncorrectErrorCode(TryFromPrimitiveError<ErrorType>),

    #[error("Provided slice doesn't contain correct AudioSocket message")]
    InvalidRawMessage,

    #[error("AudioSocket message contains invalid length")]
    IncorrectLengthProvided(TryFromSliceError),
}

/// AudioSocket message type.
#[repr(u8)]
#[derive(Copy, Clone, Debug, PartialEq, Eq, TryFromPrimitive)]
pub enum Type {
    /// Message indicates that a connection was closed.
    ///
    /// Closing socket also works.
    Terminate = 0x00,

    /// Payload of current message contains UUID of the stream.
    Identifier = 0x01,

    /// Message indicates presence of silence on the line.
    Silence = 0x02,

    /// Payload of current message contains audio itself.
    Audio = 0x10,

    /// Current message possibly contains error in payload.
    Error = 0xff,
}

/// Type of error, that message may contain.
#[repr(u8)]
#[derive(Copy, Clone, Debug, PartialEq, Eq, TryFromPrimitive)]
pub enum ErrorType {
    /// No error is present.
    None = 0x00,

    /// Call has hung up.
    Hangup = 0x01,

    /// Asterisk had an error trying to forward an audio frame.
    FrameForwarding = 0x02,

    /// Asterisk had a memory error.
    Memory = 0x04,
}

/// AudioSocket raw message.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct RawMessage<'s> {
    /// Type of current message.
    message_type: Type,

    /// Message payload, with `length` max size.
    ///
    /// May be empty, in case if message is an error.
    payload: Option<&'s [u8]>,
}

impl RawMessage<'_> {
    /// Get [`RawMessage`] type.
    pub fn message_type(&self) -> &Type {
        &self.message_type
    }

    /// Get [`RawMessage`] payload.
    pub fn payload(&self) -> &Option<&[u8]> {
        &self.payload
    }
}

impl<'s> TryFrom<&'s [u8]> for RawMessage<'s> {
    type Error = AudioSocketError;

    fn try_from(value: &'s [u8]) -> Result<Self, Self::Error> {
        let message_type = value
            .get(0)
            .ok_or(AudioSocketError::InvalidRawMessage)
            .map(|message_type| Type::try_from_primitive(*message_type))?
            .map_err(AudioSocketError::IncorrectMessageType)?;

        let length = value
            .get(1..=2)
            .ok_or(AudioSocketError::InvalidRawMessage)
            .map(|length| -> Result<u16, TryFromSliceError> {
                Ok(u16::from_be_bytes(length.try_into()?))
            })?
            .map_err(AudioSocketError::IncorrectLengthProvided)?;

        Ok(RawMessage {
            message_type,
            payload: value.get(3..usize::from(length + 3)),
        })
    }
}

/// AudioSocket message.
///
/// You may use [`RawMessage`] to obtain one.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Message<'r> {
    /// Message indicates that a connection was closed.
    ///
    /// Closing socket also works.
    Terminate,

    /// Message contains UUID of current stream.
    Identifier(Uuid),

    /// Message indicates presence of silence on the line.
    Silence,

    /// Message contains signed linear, 16-bit, 8kHz, mono PCM (little-endian) audio payload.
    Audio(&'r [u8]),

    /// Message indicates Asterisk error, and possibly contains [`ErrorType`].
    Error(Option<ErrorType>),
}

impl<'s> TryFrom<RawMessage<'s>> for Message<'s> {
    type Error = AudioSocketError;

    fn try_from(raw: RawMessage<'s>) -> Result<Self, <Message as TryFrom<RawMessage>>::Error> {
        match raw.message_type {
            Type::Terminate => Ok(Message::Terminate),
            Type::Identifier => {
                let id = raw.payload.ok_or(AudioSocketError::EmptyPayload)?;

                Ok(Message::Identifier(
                    Uuid::from_slice(&id).map_err(AudioSocketError::InvalidIdentifier)?,
                ))
            }
            Type::Silence => Ok(Message::Silence),
            Type::Audio => Ok(Message::Audio(
                raw.payload.ok_or(AudioSocketError::EmptyPayload)?,
            )),
            Type::Error => {
                if let Some(code) = raw.payload.map(|payload| -> Result<u8, TryFromSliceError> {
                    Ok(u8::from_be_bytes(payload.try_into()?))
                }) {
                    Ok(Message::Error(Some(
                        ErrorType::try_from_primitive(
                            code.map_err(AudioSocketError::IncorrectLengthProvided)?,
                        )
                        .map_err(AudioSocketError::IncorrectErrorCode)?,
                    )))
                } else {
                    Ok(Message::Error(None))
                }
            }
        }
    }
}
