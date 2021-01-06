# AudioSocket
**AudioSocket is a simple TCP-based protocol for sending and receiving real-time audio streams.**

## Usage
```rust
use std::{convert::TryFrom, str::FromStr};

use audiosocket::{Message, RawMessage, Type};
use uuid::Uuid;

// You may replace this with bytes from TCP socket, test file, etc.
let recv = [
    // Message contains a stream identifier.
    1u8,

    // Payload length is 16 bytes.
    0,
    16,

    // Payload with UUID.
    4,
    54,
    67,
    12,
    43,
    2,
    98,
    76,
    32,
    50,
    87,
    5,
    1,
    33,
    43,
    87
];

let raw_message = RawMessage::try_from(&recv[..]).unwrap();
assert_eq!(*raw_message.message_type(), Type::Identifier);

let message = Message::try_from(raw_message).unwrap();
assert_eq!(message, Message::Identifier(Uuid::from_str("0436430c-2b02-624c-2032-570501212b57").unwrap()))
```