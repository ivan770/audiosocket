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
    mem::size_of,
    num::TryFromIntError,
};

use num_enum::{IntoPrimitive, TryFromPrimitive, TryFromPrimitiveError};
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

    #[error("Unable to cast payload length to 16-bit integer")]
    LengthIsTooLarge(TryFromIntError),
}

/// AudioSocket message type.
#[repr(u8)]
#[derive(Copy, Clone, Debug, PartialEq, Eq, IntoPrimitive, TryFromPrimitive)]
pub enum Type {
    /// Message indicates that a connection was closed.
    ///
    /// Closing socket also works.
    Terminate = 0x00,

    /// Payload of current message contains UUID of the stream.
    Identifier = 0x01,

    /// Message indicates presence of silence on the line.
    Silence = 0x02,

    /// Payload of current message possibly contains audio itself.
    Audio = 0x10,

    /// Current message possibly contains error in payload.
    Error = 0xff,
}

/// Type of error, that message may contain.
#[repr(u8)]
#[derive(Copy, Clone, Debug, PartialEq, Eq, IntoPrimitive, TryFromPrimitive)]
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

impl<'s> RawMessage<'s> {
    /// Create [`RawMessage`] from raw parts.
    ///
    /// You have to ensure that payload size is <= `length`.
    pub fn from_parts(message_type: Type, payload: Option<&'s [u8]>) -> Self {
        RawMessage {
            message_type,
            payload
        }
    }

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

        Ok(RawMessage::from_parts(message_type, value.get(3..usize::from(length + 3))))
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

    /// Message possibly contains signed linear, 16-bit, 8kHz, mono PCM (little-endian) audio payload.
    Audio(Option<&'r [u8]>),

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
                raw.payload,
            )),
            Type::Error => {
                if let Some(code) = raw
                    .payload
                    .map(|payload| payload.first())
                    .flatten()
                    .copied()
                {
                    Ok(Message::Error(Some(
                        ErrorType::try_from_primitive(code)
                            .map_err(AudioSocketError::IncorrectErrorCode)?,
                    )))
                } else {
                    Ok(Message::Error(None))
                }
            }
        }
    }
}

impl TryFrom<Message<'_>> for Vec<u8> {
    type Error = AudioSocketError;

    fn try_from(message: Message<'_>) -> Result<Self, Self::Error> {
        match message {
            Message::Terminate => Ok(Vec::from([Type::Terminate.into(), 0x00, 0x00])),
            Message::Identifier(id) => {
                let mut buf =
                    Vec::with_capacity(size_of::<u8>() + size_of::<u16>() + size_of::<u128>());

                buf.push(Type::Identifier.into());
                buf.extend_from_slice(&u16::try_from(size_of::<u128>()).unwrap().to_be_bytes());
                buf.extend_from_slice(id.as_bytes());

                Ok(buf)
            }
            Message::Silence => Ok(Vec::from([Type::Silence.into(), 0x00, 0x00])),
            Message::Audio(a) => {
                let len = a.as_ref().map(|audio| audio.len()).unwrap_or(0);
                let mut buf = Vec::with_capacity(size_of::<u8>() + size_of::<u16>() + len);

                buf.push(Type::Audio.into());
                buf.extend_from_slice(
                    &u16::try_from(len)
                        .map_err(AudioSocketError::LengthIsTooLarge)?
                        .to_be_bytes(),
                );

                if let Some(audio) = a {
                    buf.extend_from_slice(audio);
                }

                Ok(buf)
            }
            Message::Error(e) => match e {
                Some(error) => Ok(Vec::from([Type::Error.into(), 0x00, 0x01, error.into()])),
                None => Ok(Vec::from([Type::Error.into(), 0x00, 0x00])),
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use std::{
        convert::{TryFrom, TryInto},
        str::FromStr,
    };

    use uuid::Uuid;

    use crate::{ErrorType, Message, RawMessage};

    #[test]
    fn terminate_cast_test() {
        let terminate = [0u8, 0u8, 0u8];

        let msg: Message = RawMessage::try_from(&terminate[..])
            .unwrap()
            .try_into()
            .unwrap();

        assert_eq!(msg, Message::Terminate);
        assert_eq!(
            TryInto::<Vec<u8>>::try_into(msg).unwrap(),
            terminate.to_vec()
        );
    }

    #[test]
    fn identifier_cast_test() {
        let identifier = [
            1u8, 0, 16, 4, 54, 67, 12, 43, 2, 98, 76, 32, 50, 87, 5, 1, 33, 43, 87,
        ];

        let msg: Message = RawMessage::try_from(&identifier[..])
            .unwrap()
            .try_into()
            .unwrap();

        assert_eq!(
            msg,
            Message::Identifier(Uuid::from_str("0436430c-2b02-624c-2032-570501212b57").unwrap())
        );
        assert_eq!(
            TryInto::<Vec<u8>>::try_into(msg).unwrap(),
            identifier.to_vec()
        );
    }

    #[test]
    fn silence_cast_test() {
        let silence = [2u8, 0u8, 0u8];

        let msg: Message = RawMessage::try_from(&silence[..])
            .unwrap()
            .try_into()
            .unwrap();

        assert_eq!(msg, Message::Silence);
        assert_eq!(TryInto::<Vec<u8>>::try_into(msg).unwrap(), silence.to_vec());
    }

    #[test]
    fn audio_cast_test() {
        let audio = [
            0x10, 0u8, 8u8,
            // Though those are not valid sound bytes, we can still use them,
            // as we don't check for audio validity.
            0, 1, 2, 3, 4, 5, 6, 7,
        ];

        let msg: Message = RawMessage::try_from(&audio[..])
            .unwrap()
            .try_into()
            .unwrap();

        assert_eq!(msg, Message::Audio(Some(&[0, 1, 2, 3, 4, 5, 6, 7])));
        assert_eq!(TryInto::<Vec<u8>>::try_into(msg).unwrap(), audio.to_vec());
    }

    #[test]
    fn audio_silence_test_cast() {
        let audio = [0; 320];

        let mut silence = Vec::with_capacity(323);

        silence.push(0x10);
        silence.extend_from_slice(
            &u16::try_from(320)
                .unwrap()
                .to_be_bytes(),
        );
        silence.extend_from_slice(&audio);

        let msg: Message = RawMessage::try_from(&silence[..])
            .unwrap()
            .try_into()
            .unwrap();

        assert_eq!(msg, Message::Audio(Some(&audio)));
        assert_eq!(TryInto::<Vec<u8>>::try_into(msg).unwrap(), silence.to_vec());
    }

    #[test]
    fn error_cast_test() {
        let error = [0xffu8, 0, 1, 1];

        let msg: Message = RawMessage::try_from(&error[..])
            .unwrap()
            .try_into()
            .unwrap();

        assert_eq!(msg, Message::Error(Some(ErrorType::Hangup)));
        assert_eq!(TryInto::<Vec<u8>>::try_into(msg).unwrap(), error.to_vec());
    }
}
