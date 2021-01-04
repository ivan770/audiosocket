//! References:
//! https://github.com/CyCoreSystems/audiosocket/blob/master/audiosocket.go
//! https://wiki.asterisk.org/wiki/display/AST/AudioSocket

use std::{array::TryFromSliceError, convert::{TryFrom, TryInto}, io::{Cursor, Error as IoError, Read}};

use num_enum::{TryFromPrimitive, TryFromPrimitiveError};
use thiserror::Error;
use uuid::{Error as UuidError, Uuid};

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
    InvalidRawMessage(IoError),
}

/// AudioSocket message type
#[repr(u8)]
#[derive(TryFromPrimitive)]
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
    ///
    /// Note that [reference](https://wiki.asterisk.org/wiki/display/AST/AudioSocket) doesn't contain any info
    /// about error codes
    Error = 0xff,
}

/// Type of error, that message may contain.
#[repr(u8)]
#[derive(TryFromPrimitive)]
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
pub struct RawMessage<'s> {
    /// Type of current message.
    message_type: Type,

    /// Message payload, with `length` max size.
    ///
    /// May be empty, in case if message is an error.
    payload: Option<&'s [u8]>,
}

impl<'s> TryFrom<Cursor<&'s [u8]>> for RawMessage<'s> {
    type Error = AudioSocketError;

    fn try_from(mut value: Cursor<&'s [u8]>) -> Result<Self, Self::Error> {
        let mut buf = [0; 1];
        value
            .read_exact(&mut buf)
            .map_err(AudioSocketError::InvalidRawMessage)?;
        let message_type = Type::try_from_primitive(u8::from_be_bytes(buf))
            .map_err(AudioSocketError::IncorrectMessageType)?;

        let mut buf = [0; 2];
        value
            .read_exact(&mut buf)
            .map_err(AudioSocketError::InvalidRawMessage)?;
        let length = u16::from_be_bytes(buf);

        Ok(RawMessage {
            message_type,
            payload: value.into_inner().get(3..usize::from(length + 3)),
        })
    }
}

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
            Type::Audio => {
                Ok(Message::Audio(raw.payload.ok_or(AudioSocketError::EmptyPayload)?))
            }
            Type::Error => {
                if let Some(Ok(code)) = raw.payload.map(|payload| -> Result<u8, TryFromSliceError> {
                    Ok(u8::from_be_bytes(payload.try_into()?))
                }) {
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
