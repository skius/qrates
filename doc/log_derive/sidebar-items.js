initSidebarItems({"attr":[["logfn","Logs the result of the function it's above. # Examples ``` rust  # #[macro_use] extern crate log_derive; # use std::{net::*, io::{self, Write}}; #[logfn(err = \"Error\", fmt = \"Failed Sending Packet: {:?}\")] fn send_hi(addr: SocketAddr) -> Result<(), io::Error> {     let mut stream = TcpStream::connect(addr)?;     stream.write(b\"Hi!\")?;     Ok( () ) }"],["logfn_inputs","Logs the inputs of the function # Examples ``` rust  # #[macro_use] extern crate log_derive; # use std::{net::*, io::{self, Write}}; #[logfn_inputs(INFO, fmt = \"Good morning: {:?}, to: {:?}\")] fn good_morning(msg: &str, addr: SocketAddr) -> Result<(), io::Error> {     let mut stream = TcpStream::connect(addr)?;     stream.write(msg.as_bytes())?;     Ok( () ) }"]]});