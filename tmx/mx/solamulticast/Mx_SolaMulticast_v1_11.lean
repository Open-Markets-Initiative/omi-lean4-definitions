import Wire

/-!
# TMX Group Sola Multicast v1.11

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.

Note: Strike Price Instrument Fraction Pair is 8 bytes whichever arm the model names: its arms lay
their bytes out alike and differ only in what they are called and what they mean, which Strike Price
Fraction Indicator says (Strike Price Instrument Negative Whole Pair, Strike Price Instrument
Negative Ten Pair, Strike Price Instrument Negative Hundred Pair, Strike Price Instrument Negative
Thousand Pair, Strike Price Instrument Negative Ten Thousand Pair, Strike Price Instrument Negative
Hundred Thousand Pair, Strike Price Instrument Negative Million Pair, Strike Price Instrument
Numeric Pair). It is read as Strike Price Instrument Negative Whole Pair's fields, so which arm
applies is left to what is built on the definition.

Note: Trade Price Fraction Pair is 7 bytes whichever arm the model names: its arms lay their bytes
out alike and differ only in what they are called and what they mean, which Trade Price Fraction
Indicator says (Trade Price Negative Whole Pair, Trade Price Negative Ten Pair, Trade Price Negative
Hundred Pair, Trade Price Negative Thousand Pair, Trade Price Negative Ten Thousand Pair, Trade
Price Negative Hundred Thousand Pair, Trade Price Negative Million Pair, Trade Price Numeric Pair).
It is read as Trade Price Negative Whole Pair's fields, so which arm applies is left to what is
built on the definition.

Note: Net Change Fraction Pair is 7 bytes whichever arm the model names: its arms lay their bytes
out alike and differ only in what they are called and what they mean, which Net Change Fraction
Indicator says (Net Change Negative Whole Pair, Net Change Negative Ten Pair, Net Change Negative
Hundred Pair, Net Change Negative Thousand Pair, Net Change Negative Ten Thousand Pair, Net Change
Negative Hundred Thousand Pair, Net Change Negative Million Pair, Net Change Numeric Pair). It is
read as Net Change Negative Whole Pair's fields, so which arm applies is left to what is built on
the definition.

Note: Net Change Future Options Trade Message Fraction Pair is 7 bytes whichever arm the model
names: its arms lay their bytes out alike and differ only in what they are called and what they
mean, which Net Change Fraction Indicator says (Net Change Future Options Trade Message Negative
Whole Pair, Net Change Future Options Trade Message Negative Ten Pair, Net Change Future Options
Trade Message Negative Hundred Pair, Net Change Future Options Trade Message Negative Thousand Pair,
Net Change Future Options Trade Message Negative Ten Thousand Pair, Net Change Future Options Trade
Message Negative Hundred Thousand Pair, Net Change Future Options Trade Message Negative Million
Pair, Net Change Future Options Trade Message Numeric Pair). It is read as Net Change Future Options
Trade Message Negative Whole Pair's fields, so which arm applies is left to what is built on the
definition.

Note: Net Change Futures Trade Message Fraction Pair is 7 bytes whichever arm the model names: its
arms lay their bytes out alike and differ only in what they are called and what they mean, which Net
Change Fraction Indicator says (Net Change Futures Trade Message Negative Whole Pair, Net Change
Futures Trade Message Negative Ten Pair, Net Change Futures Trade Message Negative Hundred Pair, Net
Change Futures Trade Message Negative Thousand Pair, Net Change Futures Trade Message Negative Ten
Thousand Pair, Net Change Futures Trade Message Negative Hundred Thousand Pair, Net Change Futures
Trade Message Negative Million Pair, Net Change Futures Trade Message Numeric Pair). It is read as
Net Change Futures Trade Message Negative Whole Pair's fields, so which arm applies is left to what
is built on the definition.

Note: Fixed Rate Fraction Pair is 6 bytes whichever arm the model names: its arms lay their bytes
out alike and differ only in what they are called and what they mean, which Fixed Rate Fraction
Indicator says (Fixed Rate Negative Whole Pair, Fixed Rate Negative Ten Pair, Fixed Rate Negative
Hundred Pair, Fixed Rate Negative Thousand Pair, Fixed Rate Negative Ten Thousand Pair, Fixed Rate
Negative Hundred Thousand Pair, Fixed Rate Negative Million Pair, Fixed Rate Numeric Pair). It is
read as Fixed Rate Negative Whole Pair's fields, so which arm applies is left to what is built on
the definition.

Note: Strike Price Schedule Notice Fraction Pair is 8 bytes whichever arm the model names: its arms
lay their bytes out alike and differ only in what they are called and what they mean, which Strike
Price Fraction Indicator says (Strike Price Schedule Notice Negative Whole Pair, Strike Price
Schedule Notice Negative Ten Pair, Strike Price Schedule Notice Negative Hundred Pair, Strike Price
Schedule Notice Negative Thousand Pair, Strike Price Schedule Notice Negative Ten Thousand Pair,
Strike Price Schedule Notice Negative Hundred Thousand Pair, Strike Price Schedule Notice Negative
Million Pair, Strike Price Schedule Notice Numeric Pair). It is read as Strike Price Schedule Notice
Negative Whole Pair's fields, so which arm applies is left to what is built on the definition.

Note: Bid Price Quote is 7 bytes whichever arm the model names: its arms lay their bytes out alike
and differ only in what they are called and what they mean, which Bid Price Quote Opening says (Bid
Price Quote Opening Pair, Bid Price Quote Numeric Negative Whole Pair, Bid Price Quote Numeric
Negative Ten Pair, Bid Price Quote Numeric Negative Hundred Pair, Bid Price Quote Numeric Negative
Thousand Pair, Bid Price Quote Numeric Negative Ten Thousand Pair, Bid Price Quote Numeric Negative
Hundred Thousand Pair, Bid Price Quote Numeric Negative Million Pair, Bid Price Quote Numeric Pair).
It is read as Bid Price Quote Numeric Negative Whole Pair's fields, so which arm applies is left to
what is built on the definition.

Note: Ask Price Quote is 7 bytes whichever arm the model names: its arms lay their bytes out alike
and differ only in what they are called and what they mean, which Ask Price Quote Opening says (Ask
Price Quote Opening Pair, Ask Price Quote Numeric Negative Whole Pair, Ask Price Quote Numeric
Negative Ten Pair, Ask Price Quote Numeric Negative Hundred Pair, Ask Price Quote Numeric Negative
Thousand Pair, Ask Price Quote Numeric Negative Ten Thousand Pair, Ask Price Quote Numeric Negative
Hundred Thousand Pair, Ask Price Quote Numeric Negative Million Pair, Ask Price Quote Numeric Pair).
It is read as Ask Price Quote Numeric Negative Whole Pair's fields, so which arm applies is left to
what is built on the definition.

Note: Bid Price Quote Futures Quote Message is 7 bytes whichever arm the model names: its arms lay
their bytes out alike and differ only in what they are called and what they mean, which Bid Price
Quote Opening says (Bid Price Quote Futures Quote Message Opening Pair, Bid Price Quote Numeric Bid
Price Quote Futures Quote Message Numeric Pair Negative Whole Pair, Bid Price Quote Numeric Bid
Price Quote Futures Quote Message Numeric Pair Negative Ten Pair, Bid Price Quote Numeric Bid Price
Quote Futures Quote Message Numeric Pair Negative Hundred Pair, Bid Price Quote Numeric Bid Price
Quote Futures Quote Message Numeric Pair Negative Thousand Pair, Bid Price Quote Numeric Bid Price
Quote Futures Quote Message Numeric Pair Negative Ten Thousand Pair, Bid Price Quote Numeric Bid
Price Quote Futures Quote Message Numeric Pair Negative Hundred Thousand Pair, Bid Price Quote
Numeric Bid Price Quote Futures Quote Message Numeric Pair Negative Million Pair, Bid Price Quote
Futures Quote Message Numeric Pair). It is read as Bid Price Quote Numeric Bid Price Quote Futures
Quote Message Numeric Pair Negative Whole Pair's fields, so which arm applies is left to what is
built on the definition.

Note: Ask Price Quote Futures Quote Message is 7 bytes whichever arm the model names: its arms lay
their bytes out alike and differ only in what they are called and what they mean, which Ask Price
Quote Opening says (Ask Price Quote Futures Quote Message Opening Pair, Ask Price Quote Numeric Ask
Price Quote Futures Quote Message Numeric Pair Negative Whole Pair, Ask Price Quote Numeric Ask
Price Quote Futures Quote Message Numeric Pair Negative Ten Pair, Ask Price Quote Numeric Ask Price
Quote Futures Quote Message Numeric Pair Negative Hundred Pair, Ask Price Quote Numeric Ask Price
Quote Futures Quote Message Numeric Pair Negative Thousand Pair, Ask Price Quote Numeric Ask Price
Quote Futures Quote Message Numeric Pair Negative Ten Thousand Pair, Ask Price Quote Numeric Ask
Price Quote Futures Quote Message Numeric Pair Negative Hundred Thousand Pair, Ask Price Quote
Numeric Ask Price Quote Futures Quote Message Numeric Pair Negative Million Pair, Ask Price Quote
Futures Quote Message Numeric Pair). It is read as Ask Price Quote Numeric Ask Price Quote Futures
Quote Message Numeric Pair Negative Whole Pair's fields, so which arm applies is left to what is
built on the definition.

Note: Bid Price Quote Strategy Quote Message is 7 bytes whichever arm the model names: its arms lay
their bytes out alike and differ only in what they are called and what they mean, which Bid Price
Quote Opening says (Bid Price Quote Strategy Quote Message Opening Pair, Bid Price Quote Numeric Bid
Price Quote Strategy Quote Message Numeric Pair Negative Whole Pair, Bid Price Quote Numeric Bid
Price Quote Strategy Quote Message Numeric Pair Negative Ten Pair, Bid Price Quote Numeric Bid Price
Quote Strategy Quote Message Numeric Pair Negative Hundred Pair, Bid Price Quote Numeric Bid Price
Quote Strategy Quote Message Numeric Pair Negative Thousand Pair, Bid Price Quote Numeric Bid Price
Quote Strategy Quote Message Numeric Pair Negative Ten Thousand Pair, Bid Price Quote Numeric Bid
Price Quote Strategy Quote Message Numeric Pair Negative Hundred Thousand Pair, Bid Price Quote
Numeric Bid Price Quote Strategy Quote Message Numeric Pair Negative Million Pair, Bid Price Quote
Strategy Quote Message Numeric Pair). It is read as Bid Price Quote Numeric Bid Price Quote Strategy
Quote Message Numeric Pair Negative Whole Pair's fields, so which arm applies is left to what is
built on the definition.

Note: Ask Price Quote Strategy Quote Message is 7 bytes whichever arm the model names: its arms lay
their bytes out alike and differ only in what they are called and what they mean, which Ask Price
Quote Opening says (Ask Price Quote Strategy Quote Message Opening Pair, Ask Price Quote Numeric Ask
Price Quote Strategy Quote Message Numeric Pair Negative Whole Pair, Ask Price Quote Numeric Ask
Price Quote Strategy Quote Message Numeric Pair Negative Ten Pair, Ask Price Quote Numeric Ask Price
Quote Strategy Quote Message Numeric Pair Negative Hundred Pair, Ask Price Quote Numeric Ask Price
Quote Strategy Quote Message Numeric Pair Negative Thousand Pair, Ask Price Quote Numeric Ask Price
Quote Strategy Quote Message Numeric Pair Negative Ten Thousand Pair, Ask Price Quote Numeric Ask
Price Quote Strategy Quote Message Numeric Pair Negative Hundred Thousand Pair, Ask Price Quote
Numeric Ask Price Quote Strategy Quote Message Numeric Pair Negative Million Pair, Ask Price Quote
Strategy Quote Message Numeric Pair). It is read as Ask Price Quote Numeric Ask Price Quote Strategy
Quote Message Numeric Pair Negative Whole Pair's fields, so which arm applies is left to what is
built on the definition.

Note: Number Of Level counts Option Market Depth Trading Instrument in ascii digits: it is written
from the list as its digits, and a list of more than 9 could not be written

Note: Number Of Level counts Future Options Market Depth Trading Instrument in ascii digits: it is
written from the list as its digits, and a list of more than 9 could not be written

Note: Bid Price Quote Futures Market Depth Trading Instrument is 7 bytes whichever arm the model
names: its arms lay their bytes out alike and differ only in what they are called and what they
mean, which Bid Price Quote Opening says (Bid Price Quote Futures Market Depth Trading Instrument
Opening Pair, Bid Price Quote Numeric Bid Price Quote Futures Market Depth Trading Instrument
Numeric Pair Negative Whole Pair, Bid Price Quote Numeric Bid Price Quote Futures Market Depth
Trading Instrument Numeric Pair Negative Ten Pair, Bid Price Quote Numeric Bid Price Quote Futures
Market Depth Trading Instrument Numeric Pair Negative Hundred Pair, Bid Price Quote Numeric Bid
Price Quote Futures Market Depth Trading Instrument Numeric Pair Negative Thousand Pair, Bid Price
Quote Numeric Bid Price Quote Futures Market Depth Trading Instrument Numeric Pair Negative Ten
Thousand Pair, Bid Price Quote Numeric Bid Price Quote Futures Market Depth Trading Instrument
Numeric Pair Negative Hundred Thousand Pair, Bid Price Quote Numeric Bid Price Quote Futures Market
Depth Trading Instrument Numeric Pair Negative Million Pair, Bid Price Quote Futures Market Depth
Trading Instrument Numeric Pair). It is read as Bid Price Quote Numeric Bid Price Quote Futures
Market Depth Trading Instrument Numeric Pair Negative Whole Pair's fields, so which arm applies is
left to what is built on the definition.

Note: Ask Price Futures Depth Futures Market Depth Trading Instrument is 7 bytes whichever arm the
model names: its arms lay their bytes out alike and differ only in what they are called and what
they mean, which Ask Price Futures Depth Opening says (Ask Price Futures Depth Futures Market Depth
Trading Instrument Opening Pair, Ask Price Futures Depth Numeric Negative Whole Pair, Ask Price
Futures Depth Numeric Negative Ten Pair, Ask Price Futures Depth Numeric Negative Hundred Pair, Ask
Price Futures Depth Numeric Negative Thousand Pair, Ask Price Futures Depth Numeric Negative Ten
Thousand Pair, Ask Price Futures Depth Numeric Negative Hundred Thousand Pair, Ask Price Futures
Depth Numeric Negative Million Pair, Ask Price Futures Depth Futures Market Depth Trading Instrument
Numeric Pair). It is read as Ask Price Futures Depth Numeric Negative Whole Pair's fields, so which
arm applies is left to what is built on the definition.

Note: Number Of Level counts Futures Market Depth Trading Instrument in ascii digits: it is written
from the list as its digits, and a list of more than 9 could not be written

Note: Number Of Level counts Strategy Market Depth Trading Instrument in ascii digits: it is written
from the list as its digits, and a list of more than 9 could not be written

Note: Number Of Level counts Swap Future Market Depth Trading Instrument in ascii digits: it is
written from the list as its digits, and a list of more than 9 could not be written

Note: Price Fraction Pair is 7 bytes whichever arm the model names: its arms lay their bytes out
alike and differ only in what they are called and what they mean, which Price Fraction Indicator
says (Price Negative Whole Pair, Price Negative Ten Pair, Price Negative Hundred Pair, Price
Negative Thousand Pair, Price Negative Ten Thousand Pair, Price Negative Hundred Thousand Pair,
Price Negative Million Pair, Price Numeric Pair). It is read as Price Negative Whole Pair's fields,
so which arm applies is left to what is built on the definition.

Note: Maximum Threshold Price Options Fraction Pair is 7 bytes whichever arm the model names: its
arms lay their bytes out alike and differ only in what they are called and what they mean, which
Maximum Threshold Price Fraction Indicator says (Maximum Threshold Price Options Negative Whole
Pair, Maximum Threshold Price Options Negative Ten Pair, Maximum Threshold Price Options Negative
Hundred Pair, Maximum Threshold Price Options Negative Thousand Pair, Maximum Threshold Price
Options Negative Ten Thousand Pair, Maximum Threshold Price Options Negative Hundred Thousand Pair,
Maximum Threshold Price Options Negative Million Pair, Maximum Threshold Price Options Numeric
Pair). It is read as Maximum Threshold Price Options Negative Whole Pair's fields, so which arm
applies is left to what is built on the definition.

Note: Minimum Threshold Price Options Fraction Pair is 7 bytes whichever arm the model names: its
arms lay their bytes out alike and differ only in what they are called and what they mean, which
Minimum Threshold Price Fraction Indicator says (Minimum Threshold Price Options Negative Whole
Pair, Minimum Threshold Price Options Negative Ten Pair, Minimum Threshold Price Options Negative
Hundred Pair, Minimum Threshold Price Options Negative Thousand Pair, Minimum Threshold Price
Options Negative Ten Thousand Pair, Minimum Threshold Price Options Negative Hundred Thousand Pair,
Minimum Threshold Price Options Negative Million Pair, Minimum Threshold Price Options Numeric
Pair). It is read as Minimum Threshold Price Options Negative Whole Pair's fields, so which arm
applies is left to what is built on the definition.

Note: Tick Increment is 7 bytes whichever arm the model names: its arms lay their bytes out alike
and differ only in what they are called and what they mean, which Tick Increment Fraction Indicator
says (Tick Increment Numeric Pair, Tick Increment Numeric Negative Whole Pair, Tick Increment
Numeric Negative Ten Pair, Tick Increment Numeric Negative Hundred Pair, Tick Increment Numeric
Negative Thousand Pair, Tick Increment Numeric Negative Ten Thousand Pair, Tick Increment Numeric
Negative Hundred Thousand Pair, Tick Increment Numeric Negative Million Pair, Tick Increment Raw
Pair). It is read as Tick Increment Numeric Pair's fields, so which arm applies is left to what is
built on the definition.

Note: Tick Value Fraction Pair is 7 bytes whichever arm the model names: its arms lay their bytes
out alike and differ only in what they are called and what they mean, which Tick Value Fraction
Indicator says (Tick Value Negative Whole Pair, Tick Value Negative Ten Pair, Tick Value Negative
Hundred Pair, Tick Value Negative Thousand Pair, Tick Value Negative Ten Thousand Pair, Tick Value
Negative Hundred Thousand Pair, Tick Value Negative Million Pair, Tick Value Numeric Pair). It is
read as Tick Value Negative Whole Pair's fields, so which arm applies is left to what is built on
the definition.

Note: Maximum Threshold Price Futures Fraction Pair is 7 bytes whichever arm the model names: its
arms lay their bytes out alike and differ only in what they are called and what they mean, which
Maximum Threshold Price Fraction Indicator says (Maximum Threshold Price Futures Negative Whole
Pair, Maximum Threshold Price Futures Negative Ten Pair, Maximum Threshold Price Futures Negative
Hundred Pair, Maximum Threshold Price Futures Negative Thousand Pair, Maximum Threshold Price
Futures Negative Ten Thousand Pair, Maximum Threshold Price Futures Negative Hundred Thousand Pair,
Maximum Threshold Price Futures Negative Million Pair, Maximum Threshold Price Futures Numeric
Pair). It is read as Maximum Threshold Price Futures Negative Whole Pair's fields, so which arm
applies is left to what is built on the definition.

Note: Minimum Threshold Price Futures Fraction Pair is 7 bytes whichever arm the model names: its
arms lay their bytes out alike and differ only in what they are called and what they mean, which
Minimum Threshold Price Fraction Indicator says (Minimum Threshold Price Futures Negative Whole
Pair, Minimum Threshold Price Futures Negative Ten Pair, Minimum Threshold Price Futures Negative
Hundred Pair, Minimum Threshold Price Futures Negative Thousand Pair, Minimum Threshold Price
Futures Negative Ten Thousand Pair, Minimum Threshold Price Futures Negative Hundred Thousand Pair,
Minimum Threshold Price Futures Negative Million Pair, Minimum Threshold Price Futures Numeric
Pair). It is read as Minimum Threshold Price Futures Negative Whole Pair's fields, so which arm
applies is left to what is built on the definition.

Note: Notional Principal Amount Fraction Pair is 9 bytes whichever arm the model names: its arms lay
their bytes out alike and differ only in what they are called and what they mean, which Notional
Principal Amount Faction Indicator says (Notional Principal Amount Negative Whole Pair, Notional
Principal Amount Negative Ten Pair, Notional Principal Amount Negative Hundred Pair, Notional
Principal Amount Negative Thousand Pair, Notional Principal Amount Negative Ten Thousand Pair,
Notional Principal Amount Negative Hundred Thousand Pair, Notional Principal Amount Negative Million
Pair, Notional Principal Amount Numeric Pair). It is read as Notional Principal Amount Negative
Whole Pair's fields, so which arm applies is left to what is built on the definition.

Note: Bid Price Summary Fraction Pair is 7 bytes whichever arm the model names: its arms lay their
bytes out alike and differ only in what they are called and what they mean, which Bid Price Fraction
Indicator says (Bid Price Summary Negative Whole Pair, Bid Price Summary Negative Ten Pair, Bid
Price Summary Negative Hundred Pair, Bid Price Summary Negative Thousand Pair, Bid Price Summary
Negative Ten Thousand Pair, Bid Price Summary Negative Hundred Thousand Pair, Bid Price Summary
Negative Million Pair, Bid Price Summary Numeric Pair). It is read as Bid Price Summary Negative
Whole Pair's fields, so which arm applies is left to what is built on the definition.

Note: Ask Price Summary Fraction Pair is 7 bytes whichever arm the model names: its arms lay their
bytes out alike and differ only in what they are called and what they mean, which Ask Price Fraction
Indicator says (Ask Price Summary Negative Whole Pair, Ask Price Summary Negative Ten Pair, Ask
Price Summary Negative Hundred Pair, Ask Price Summary Negative Thousand Pair, Ask Price Summary
Negative Ten Thousand Pair, Ask Price Summary Negative Hundred Thousand Pair, Ask Price Summary
Negative Million Pair, Ask Price Summary Numeric Pair). It is read as Ask Price Summary Negative
Whole Pair's fields, so which arm applies is left to what is built on the definition.

Note: Last Price Fraction Pair is 7 bytes whichever arm the model names: its arms lay their bytes
out alike and differ only in what they are called and what they mean, which Last Price Fraction
Indicator says (Last Price Negative Whole Pair, Last Price Negative Ten Pair, Last Price Negative
Hundred Pair, Last Price Negative Thousand Pair, Last Price Negative Ten Thousand Pair, Last Price
Negative Hundred Thousand Pair, Last Price Negative Million Pair, Last Price Numeric Pair). It is
read as Last Price Negative Whole Pair's fields, so which arm applies is left to what is built on
the definition.

Note: Open Price Fraction Pair is 7 bytes whichever arm the model names: its arms lay their bytes
out alike and differ only in what they are called and what they mean, which Open Price Fraction
Indicator says (Open Price Negative Whole Pair, Open Price Negative Ten Pair, Open Price Negative
Hundred Pair, Open Price Negative Thousand Pair, Open Price Negative Ten Thousand Pair, Open Price
Negative Hundred Thousand Pair, Open Price Negative Million Pair, Open Price Numeric Pair). It is
read as Open Price Negative Whole Pair's fields, so which arm applies is left to what is built on
the definition.

Note: High Price Fraction Pair is 7 bytes whichever arm the model names: its arms lay their bytes
out alike and differ only in what they are called and what they mean, which High Price Fraction
Indicator says (High Price Negative Whole Pair, High Price Negative Ten Pair, High Price Negative
Hundred Pair, High Price Negative Thousand Pair, High Price Negative Ten Thousand Pair, High Price
Negative Hundred Thousand Pair, High Price Negative Million Pair, High Price Numeric Pair). It is
read as High Price Negative Whole Pair's fields, so which arm applies is left to what is built on
the definition.

Note: Low Price Fraction Pair is 7 bytes whichever arm the model names: its arms lay their bytes out
alike and differ only in what they are called and what they mean, which Low Price Fraction Indicator
says (Low Price Negative Whole Pair, Low Price Negative Ten Pair, Low Price Negative Hundred Pair,
Low Price Negative Thousand Pair, Low Price Negative Ten Thousand Pair, Low Price Negative Hundred
Thousand Pair, Low Price Negative Million Pair, Low Price Numeric Pair). It is read as Low Price
Negative Whole Pair's fields, so which arm applies is left to what is built on the definition.

Note: Settlement Price Fraction Pair is 7 bytes whichever arm the model names: its arms lay their
bytes out alike and differ only in what they are called and what they mean, which Settlement Price
Fraction Indicator says (Settlement Price Negative Whole Pair, Settlement Price Negative Ten Pair,
Settlement Price Negative Hundred Pair, Settlement Price Negative Thousand Pair, Settlement Price
Negative Ten Thousand Pair, Settlement Price Negative Hundred Thousand Pair, Settlement Price
Negative Million Pair, Settlement Price Numeric Pair). It is read as Settlement Price Negative Whole
Pair's fields, so which arm applies is left to what is built on the definition.

Note: Previous Settlement Price Fraction Pair is 7 bytes whichever arm the model names: its arms lay
their bytes out alike and differ only in what they are called and what they mean, which Previous
Settlement Price Fraction Indicator says (Previous Settlement Price Negative Whole Pair, Previous
Settlement Price Negative Ten Pair, Previous Settlement Price Negative Hundred Pair, Previous
Settlement Price Negative Thousand Pair, Previous Settlement Price Negative Ten Thousand Pair,
Previous Settlement Price Negative Hundred Thousand Pair, Previous Settlement Price Negative Million
Pair, Previous Settlement Price Numeric Pair). It is read as Previous Settlement Price Negative
Whole Pair's fields, so which arm applies is left to what is built on the definition.

Note: Last Price Future Options Summary Message Fraction Pair is 7 bytes whichever arm the model
names: its arms lay their bytes out alike and differ only in what they are called and what they
mean, which Last Price Fraction Indicator says (Last Price Future Options Summary Message Negative
Whole Pair, Last Price Future Options Summary Message Negative Ten Pair, Last Price Future Options
Summary Message Negative Hundred Pair, Last Price Future Options Summary Message Negative Thousand
Pair, Last Price Future Options Summary Message Negative Ten Thousand Pair, Last Price Future
Options Summary Message Negative Hundred Thousand Pair, Last Price Future Options Summary Message
Negative Million Pair, Last Price Future Options Summary Message Numeric Pair). It is read as Last
Price Future Options Summary Message Negative Whole Pair's fields, so which arm applies is left to
what is built on the definition.

Note: Net Change Future Options Summary Message Fraction Pair is 7 bytes whichever arm the model
names: its arms lay their bytes out alike and differ only in what they are called and what they
mean, which Net Change Fraction Indicator says (Net Change Future Options Summary Message Negative
Whole Pair, Net Change Future Options Summary Message Negative Ten Pair, Net Change Future Options
Summary Message Negative Hundred Pair, Net Change Future Options Summary Message Negative Thousand
Pair, Net Change Future Options Summary Message Negative Ten Thousand Pair, Net Change Future
Options Summary Message Negative Hundred Thousand Pair, Net Change Future Options Summary Message
Negative Million Pair, Net Change Future Options Summary Message Numeric Pair). It is read as Net
Change Future Options Summary Message Negative Whole Pair's fields, so which arm applies is left to
what is built on the definition.

Note: Opening Price Fraction Pair is 7 bytes whichever arm the model names: its arms lay their bytes
out alike and differ only in what they are called and what they mean, which Opening Price Fraction
Indicator says (Opening Price Negative Whole Pair, Opening Price Negative Ten Pair, Opening Price
Negative Hundred Pair, Opening Price Negative Thousand Pair, Opening Price Negative Ten Thousand
Pair, Opening Price Negative Hundred Thousand Pair, Opening Price Negative Million Pair, Opening
Price Numeric Pair). It is read as Opening Price Negative Whole Pair's fields, so which arm applies
is left to what is built on the definition.

Note: Settlement Price Future Options Summary Message Fraction Pair is 7 bytes whichever arm the
model names: its arms lay their bytes out alike and differ only in what they are called and what
they mean, which Settlement Price Fraction Indicator says (Settlement Price Future Options Summary
Message Negative Whole Pair, Settlement Price Future Options Summary Message Negative Ten Pair,
Settlement Price Future Options Summary Message Negative Hundred Pair, Settlement Price Future
Options Summary Message Negative Thousand Pair, Settlement Price Future Options Summary Message
Negative Ten Thousand Pair, Settlement Price Future Options Summary Message Negative Hundred
Thousand Pair, Settlement Price Future Options Summary Message Negative Million Pair, Settlement
Price Future Options Summary Message Numeric Pair). It is read as Settlement Price Future Options
Summary Message Negative Whole Pair's fields, so which arm applies is left to what is built on the
definition.

Note: Net Change Futures Summary Message Fraction Pair is 7 bytes whichever arm the model names: its
arms lay their bytes out alike and differ only in what they are called and what they mean, which Net
Change Fraction Indicator says (Net Change Futures Summary Message Negative Whole Pair, Net Change
Futures Summary Message Negative Ten Pair, Net Change Futures Summary Message Negative Hundred Pair,
Net Change Futures Summary Message Negative Thousand Pair, Net Change Futures Summary Message
Negative Ten Thousand Pair, Net Change Futures Summary Message Negative Hundred Thousand Pair, Net
Change Futures Summary Message Negative Million Pair, Net Change Futures Summary Message Numeric
Pair). It is read as Net Change Futures Summary Message Negative Whole Pair's fields, so which arm
applies is left to what is built on the definition.

Note: Previous Settlement Fraction Pair is 7 bytes whichever arm the model names: its arms lay their
bytes out alike and differ only in what they are called and what they mean, which Previous
Settlement Fraction Indicator says (Previous Settlement Negative Whole Pair, Previous Settlement
Negative Ten Pair, Previous Settlement Negative Hundred Pair, Previous Settlement Negative Thousand
Pair, Previous Settlement Negative Ten Thousand Pair, Previous Settlement Negative Hundred Thousand
Pair, Previous Settlement Negative Million Pair, Previous Settlement Numeric Pair). It is read as
Previous Settlement Negative Whole Pair's fields, so which arm applies is left to what is built on
the definition.

Note: External Price At Source Fraction Pair is 7 bytes whichever arm the model names: its arms lay
their bytes out alike and differ only in what they are called and what they mean, which External
Price Fraction Indicator says (External Price At Source Negative Whole Pair, External Price At
Source Negative Ten Pair, External Price At Source Negative Hundred Pair, External Price At Source
Negative Thousand Pair, External Price At Source Negative Ten Thousand Pair, External Price At
Source Negative Hundred Thousand Pair, External Price At Source Negative Million Pair, External
Price At Source Numeric Pair). It is read as External Price At Source Negative Whole Pair's fields,
so which arm applies is left to what is built on the definition.

Note: Net Change Strategy Summary Message Fraction Pair is 7 bytes whichever arm the model names:
its arms lay their bytes out alike and differ only in what they are called and what they mean, which
Net Change Fraction Indicator says (Net Change Strategy Summary Message Negative Whole Pair, Net
Change Strategy Summary Message Negative Ten Pair, Net Change Strategy Summary Message Negative
Hundred Pair, Net Change Strategy Summary Message Negative Thousand Pair, Net Change Strategy
Summary Message Negative Ten Thousand Pair, Net Change Strategy Summary Message Negative Hundred
Thousand Pair, Net Change Strategy Summary Message Negative Million Pair, Net Change Strategy
Summary Message Numeric Pair). It is read as Net Change Strategy Summary Message Negative Whole
Pair's fields, so which arm applies is left to what is built on the definition.

Note: Number Of Legs counts Strategy Summary Strategy Leg in ascii digits: it is written from the
list as its digits, and a list of more than 99 could not be written

Note: Net Present Value A Fraction Pair is 12 bytes whichever arm the model names: its arms lay
their bytes out alike and differ only in what they are called and what they mean, which Net Present
Value Fraction Indicator says (Net Present Value A Negative Whole Pair, Net Present Value A Negative
Ten Pair, Net Present Value A Negative Hundred Pair, Net Present Value A Negative Thousand Pair, Net
Present Value A Negative Ten Thousand Pair, Net Present Value A Negative Hundred Thousand Pair, Net
Present Value A Negative Million Pair, Net Present Value A Numeric Pair). It is read as Net Present
Value A Negative Whole Pair's fields, so which arm applies is left to what is built on the
definition.

Note: Historical Coupon B Fraction Pair is 12 bytes whichever arm the model names: its arms lay
their bytes out alike and differ only in what they are called and what they mean, which Historical
Coupon Fraction Indicator says (Historical Coupon B Negative Whole Pair, Historical Coupon B
Negative Ten Pair, Historical Coupon B Negative Hundred Pair, Historical Coupon B Negative Thousand
Pair, Historical Coupon B Negative Ten Thousand Pair, Historical Coupon B Negative Hundred Thousand
Pair, Historical Coupon B Negative Million Pair, Historical Coupon B Numeric Pair). It is read as
Historical Coupon B Negative Whole Pair's fields, so which arm applies is left to what is built on
the definition.

Note: Price Alignment Interest C Fraction Pair is 12 bytes whichever arm the model names: its arms
lay their bytes out alike and differ only in what they are called and what they mean, which Price
Alignment Interest Fraction Indicator says (Price Alignment Interest C Negative Whole Pair, Price
Alignment Interest C Negative Ten Pair, Price Alignment Interest C Negative Hundred Pair, Price
Alignment Interest C Negative Thousand Pair, Price Alignment Interest C Negative Ten Thousand Pair,
Price Alignment Interest C Negative Hundred Thousand Pair, Price Alignment Interest C Negative
Million Pair, Price Alignment Interest C Numeric Pair). It is read as Price Alignment Interest C
Negative Whole Pair's fields, so which arm applies is left to what is built on the definition.

Note: Net Change Swap Future Summary Message Fraction Pair is 7 bytes whichever arm the model names:
its arms lay their bytes out alike and differ only in what they are called and what they mean, which
Net Change Fraction Indicator says (Net Change Swap Future Summary Message Negative Whole Pair, Net
Change Swap Future Summary Message Negative Ten Pair, Net Change Swap Future Summary Message
Negative Hundred Pair, Net Change Swap Future Summary Message Negative Thousand Pair, Net Change
Swap Future Summary Message Negative Ten Thousand Pair, Net Change Swap Future Summary Message
Negative Hundred Thousand Pair, Net Change Swap Future Summary Message Negative Million Pair, Net
Change Swap Future Summary Message Numeric Pair). It is read as Net Change Swap Future Summary
Message Negative Whole Pair's fields, so which arm applies is left to what is built on the
definition.

Note: Previous Reset Rate Fraction Pair is 7 bytes whichever arm the model names: its arms lay their
bytes out alike and differ only in what they are called and what they mean, which Previous Reset
Rate Fraction Indicator says (Previous Reset Rate Negative Whole Pair, Previous Reset Rate Negative
Ten Pair, Previous Reset Rate Negative Hundred Pair, Previous Reset Rate Negative Thousand Pair,
Previous Reset Rate Negative Ten Thousand Pair, Previous Reset Rate Negative Hundred Thousand Pair,
Previous Reset Rate Negative Million Pair, Previous Reset Rate Numeric Pair). It is read as Previous
Reset Rate Negative Whole Pair's fields, so which arm applies is left to what is built on the
definition.

Note: Min Price Fraction Pair is 7 bytes whichever arm the model names: its arms lay their bytes out
alike and differ only in what they are called and what they mean, which Min Price Fraction Indicator
says (Min Price Negative Whole Pair, Min Price Negative Ten Pair, Min Price Negative Hundred Pair,
Min Price Negative Thousand Pair, Min Price Negative Ten Thousand Pair, Min Price Negative Hundred
Thousand Pair, Min Price Negative Million Pair, Min Price Numeric Pair). It is read as Min Price
Negative Whole Pair's fields, so which arm applies is left to what is built on the definition.

Note: Tick Price Fraction Pair is 7 bytes whichever arm the model names: its arms lay their bytes
out alike and differ only in what they are called and what they mean, which Tick Price Fraction
Indicator says (Tick Price Negative Whole Pair, Tick Price Negative Ten Pair, Tick Price Negative
Hundred Pair, Tick Price Negative Thousand Pair, Tick Price Negative Ten Thousand Pair, Tick Price
Negative Hundred Thousand Pair, Tick Price Negative Million Pair, Tick Price Numeric Pair). It is
read as Tick Price Negative Whole Pair's fields, so which arm applies is left to what is built on
the definition.

Note: Number Of Entries counts Tick Entry Group in ascii digits: it is written from the list as its
digits, and a list of more than 99 could not be written

License: MIT No Attribution
-/

namespace Omi.TmxMxSolamulticastHsvfV111

/-- Exchange Id: one byte code -/
def ExchangeId.codes : List UInt8 :=
  [0x51]

inductive ExchangeId where
  | montreal -- Montreal
  | unlisted (byte : { byte : UInt8 // byte ∉ ExchangeId.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExchangeId

def toByte : ExchangeId → UInt8
  | .montreal => 0x51
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : ExchangeId :=
  .montreal

def ofByte (byte : UInt8) : ExchangeId :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExchangeId) : ofByte value.toByte = value := by
  cases value with
  | montreal => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ExchangeId) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ExchangeId × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ExchangeId) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ExchangeId) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ExchangeId) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ExchangeId

/-- Expiry Month: one byte code -/
def ExpiryMonth.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x4F, 0x50, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58]

inductive ExpiryMonth where
  | januaryCall -- January Call
  | februaryCall -- February Call
  | marchCall -- March Call
  | aprilCall -- April Call
  | mayCall -- May Call
  | juneCall -- June Call
  | julyCall -- July Call
  | augustCall -- August Call
  | septemberCall -- September Call
  | octoberCall -- October Call
  | novemberCall -- November Call
  | decemberCall -- December Call
  | januaryPut -- January Put
  | februaryPut -- February Put
  | marchPut -- March Put
  | aprilPut -- April Put
  | mayPut -- May Put
  | junePut -- June Put
  | julyPut -- July Put
  | augustPut -- August Put
  | septemberPut -- September Put
  | octoberPut -- October Put
  | novemberPut -- November Put
  | decemberPut -- December Put
  | unlisted (byte : { byte : UInt8 // byte ∉ ExpiryMonth.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExpiryMonth

def toByte : ExpiryMonth → UInt8
  | .januaryCall => 0x41
  | .februaryCall => 0x42
  | .marchCall => 0x43
  | .aprilCall => 0x44
  | .mayCall => 0x45
  | .juneCall => 0x46
  | .julyCall => 0x47
  | .augustCall => 0x48
  | .septemberCall => 0x49
  | .octoberCall => 0x4A
  | .novemberCall => 0x4B
  | .decemberCall => 0x4C
  | .januaryPut => 0x4D
  | .februaryPut => 0x4E
  | .marchPut => 0x4F
  | .aprilPut => 0x50
  | .mayPut => 0x51
  | .junePut => 0x52
  | .julyPut => 0x53
  | .augustPut => 0x54
  | .septemberPut => 0x55
  | .octoberPut => 0x56
  | .novemberPut => 0x57
  | .decemberPut => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExpiryMonth :=
  if byte = 0x41 then .januaryCall
  else if byte = 0x42 then .februaryCall
  else if byte = 0x43 then .marchCall
  else if byte = 0x44 then .aprilCall
  else if byte = 0x45 then .mayCall
  else if byte = 0x46 then .juneCall
  else if byte = 0x47 then .julyCall
  else if byte = 0x48 then .augustCall
  else if byte = 0x49 then .septemberCall
  else if byte = 0x4A then .octoberCall
  else if byte = 0x4B then .novemberCall
  else if byte = 0x4C then .decemberCall
  else if byte = 0x4D then .januaryPut
  else if byte = 0x4E then .februaryPut
  else if byte = 0x4F then .marchPut
  else if byte = 0x50 then .aprilPut
  else if byte = 0x51 then .mayPut
  else if byte = 0x52 then .junePut
  else if byte = 0x53 then .julyPut
  else if byte = 0x54 then .augustPut
  else if byte = 0x55 then .septemberPut
  else if byte = 0x56 then .octoberPut
  else if byte = 0x57 then .novemberPut
  else .decemberPut

def ofByte (byte : UInt8) : ExpiryMonth :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExpiryMonth) : ofByte value.toByte = value := by
  cases value with
  | januaryCall => decide
  | februaryCall => decide
  | marchCall => decide
  | aprilCall => decide
  | mayCall => decide
  | juneCall => decide
  | julyCall => decide
  | augustCall => decide
  | septemberCall => decide
  | octoberCall => decide
  | novemberCall => decide
  | decemberCall => decide
  | januaryPut => decide
  | februaryPut => decide
  | marchPut => decide
  | aprilPut => decide
  | mayPut => decide
  | junePut => decide
  | julyPut => decide
  | augustPut => decide
  | septemberPut => decide
  | octoberPut => decide
  | novemberPut => decide
  | decemberPut => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ExpiryMonth) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ExpiryMonth × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ExpiryMonth) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ExpiryMonth) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ExpiryMonth) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ExpiryMonth

/-- Net Change Sign: one byte code -/
def NetChangeSign.codes : List UInt8 :=
  [0x2B, 0x2D]

inductive NetChangeSign where
  | positive -- Positive
  | negative -- Negative
  | unlisted (byte : { byte : UInt8 // byte ∉ NetChangeSign.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace NetChangeSign

def toByte : NetChangeSign → UInt8
  | .positive => 0x2B
  | .negative => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : NetChangeSign :=
  if byte = 0x2B then .positive
  else .negative

def ofByte (byte : UInt8) : NetChangeSign :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : NetChangeSign) : ofByte value.toByte = value := by
  cases value with
  | positive => decide
  | negative => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : NetChangeSign) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (NetChangeSign × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : NetChangeSign) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : NetChangeSign) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : NetChangeSign) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end NetChangeSign

/-- Price Indicator Marker: one byte code -/
def PriceIndicatorMarker.codes : List UInt8 :=
  [0x41, 0x42, 0x20, 0x44, 0x45, 0x47, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x50, 0x51, 0x52, 0x53, 0x74, 0x54, 0x55, 0x56, 0x59, 0x5A]

inductive PriceIndicatorMarker where
  | asOfTrade -- As Of Trade
  | blockTrade -- Block Trade
  | actualTransactionTookPlace -- Actual Transaction Took Place
  | crossed -- Crossed
  | efpReporting -- Efp Reporting
  | contingentTrade -- Contingent Trade
  | risklessBasisCross -- Riskless Basis Cross
  | impliedTrade -- Implied Trade
  | deltaTrade -- Delta Trade
  | committedBlock -- Committed Block
  | lateTrade -- Late Trade
  | forFutureUse -- For Future Use
  | forFutureUse_4e -- For Future Use
  | strategyReporting -- Strategy Reporting
  | forFutureUse_51 -- For Future Use
  | efrReporting -- Efr Reporting
  | referencePrice -- Reference Price
  | tradeCorrection -- Trade Correction
  | committed -- Committed
  | basisOnClose -- Basis On Close
  | priceVolumeAdjustment -- Price Volume Adjustment
  | forFutureUse_59 -- For Future Use
  | forFutureUse_5a -- For Future Use
  | unlisted (byte : { byte : UInt8 // byte ∉ PriceIndicatorMarker.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PriceIndicatorMarker

def toByte : PriceIndicatorMarker → UInt8
  | .asOfTrade => 0x41
  | .blockTrade => 0x42
  | .actualTransactionTookPlace => 0x20
  | .crossed => 0x44
  | .efpReporting => 0x45
  | .contingentTrade => 0x47
  | .risklessBasisCross => 0x48
  | .impliedTrade => 0x49
  | .deltaTrade => 0x4A
  | .committedBlock => 0x4B
  | .lateTrade => 0x4C
  | .forFutureUse => 0x4D
  | .forFutureUse_4e => 0x4E
  | .strategyReporting => 0x50
  | .forFutureUse_51 => 0x51
  | .efrReporting => 0x52
  | .referencePrice => 0x53
  | .tradeCorrection => 0x74
  | .committed => 0x54
  | .basisOnClose => 0x55
  | .priceVolumeAdjustment => 0x56
  | .forFutureUse_59 => 0x59
  | .forFutureUse_5a => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PriceIndicatorMarker :=
  if byte = 0x41 then .asOfTrade
  else if byte = 0x42 then .blockTrade
  else if byte = 0x20 then .actualTransactionTookPlace
  else if byte = 0x44 then .crossed
  else if byte = 0x45 then .efpReporting
  else if byte = 0x47 then .contingentTrade
  else if byte = 0x48 then .risklessBasisCross
  else if byte = 0x49 then .impliedTrade
  else if byte = 0x4A then .deltaTrade
  else if byte = 0x4B then .committedBlock
  else if byte = 0x4C then .lateTrade
  else if byte = 0x4D then .forFutureUse
  else if byte = 0x4E then .forFutureUse_4e
  else if byte = 0x50 then .strategyReporting
  else if byte = 0x51 then .forFutureUse_51
  else if byte = 0x52 then .efrReporting
  else if byte = 0x53 then .referencePrice
  else if byte = 0x74 then .tradeCorrection
  else if byte = 0x54 then .committed
  else if byte = 0x55 then .basisOnClose
  else if byte = 0x56 then .priceVolumeAdjustment
  else if byte = 0x59 then .forFutureUse_59
  else .forFutureUse_5a

def ofByte (byte : UInt8) : PriceIndicatorMarker :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PriceIndicatorMarker) : ofByte value.toByte = value := by
  cases value with
  | asOfTrade => decide
  | blockTrade => decide
  | actualTransactionTookPlace => decide
  | crossed => decide
  | efpReporting => decide
  | contingentTrade => decide
  | risklessBasisCross => decide
  | impliedTrade => decide
  | deltaTrade => decide
  | committedBlock => decide
  | lateTrade => decide
  | forFutureUse => decide
  | forFutureUse_4e => decide
  | strategyReporting => decide
  | forFutureUse_51 => decide
  | efrReporting => decide
  | referencePrice => decide
  | tradeCorrection => decide
  | committed => decide
  | basisOnClose => decide
  | priceVolumeAdjustment => decide
  | forFutureUse_59 => decide
  | forFutureUse_5a => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PriceIndicatorMarker) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PriceIndicatorMarker × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PriceIndicatorMarker) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : PriceIndicatorMarker) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : PriceIndicatorMarker) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PriceIndicatorMarker

/-- Contract Month Code: one byte code -/
def ContractMonthCode.codes : List UInt8 :=
  [0x46, 0x47, 0x48, 0x4A, 0x4B, 0x4D, 0x4E, 0x51, 0x55, 0x56, 0x58, 0x5A]

inductive ContractMonthCode where
  | january -- January
  | february -- February
  | march -- March
  | april -- April
  | may -- May
  | june -- June
  | july -- July
  | august -- August
  | september -- September
  | october -- October
  | november -- November
  | december -- December
  | unlisted (byte : { byte : UInt8 // byte ∉ ContractMonthCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ContractMonthCode

def toByte : ContractMonthCode → UInt8
  | .january => 0x46
  | .february => 0x47
  | .march => 0x48
  | .april => 0x4A
  | .may => 0x4B
  | .june => 0x4D
  | .july => 0x4E
  | .august => 0x51
  | .september => 0x55
  | .october => 0x56
  | .november => 0x58
  | .december => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ContractMonthCode :=
  if byte = 0x46 then .january
  else if byte = 0x47 then .february
  else if byte = 0x48 then .march
  else if byte = 0x4A then .april
  else if byte = 0x4B then .may
  else if byte = 0x4D then .june
  else if byte = 0x4E then .july
  else if byte = 0x51 then .august
  else if byte = 0x55 then .september
  else if byte = 0x56 then .october
  else if byte = 0x58 then .november
  else .december

def ofByte (byte : UInt8) : ContractMonthCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ContractMonthCode) : ofByte value.toByte = value := by
  cases value with
  | january => decide
  | february => decide
  | march => decide
  | april => decide
  | may => decide
  | june => decide
  | july => decide
  | august => decide
  | september => decide
  | october => decide
  | november => decide
  | december => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ContractMonthCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ContractMonthCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ContractMonthCode) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ContractMonthCode) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ContractMonthCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ContractMonthCode

/-- Call Put Code: one byte code -/
def CallPutCode.codes : List UInt8 :=
  [0x43, 0x50]

inductive CallPutCode where
  | call -- Call
  | put -- Put
  | unlisted (byte : { byte : UInt8 // byte ∉ CallPutCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CallPutCode

def toByte : CallPutCode → UInt8
  | .call => 0x43
  | .put => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CallPutCode :=
  if byte = 0x43 then .call
  else .put

def ofByte (byte : UInt8) : CallPutCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CallPutCode) : ofByte value.toByte = value := by
  cases value with
  | call => decide
  | put => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CallPutCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CallPutCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CallPutCode) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CallPutCode) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CallPutCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CallPutCode

/-- Delivery Month: one byte code -/
def DeliveryMonth.codes : List UInt8 :=
  [0x46, 0x47, 0x48, 0x4A, 0x4B, 0x4D, 0x4E, 0x51, 0x55, 0x56, 0x58, 0x5A]

inductive DeliveryMonth where
  | january -- January
  | february -- February
  | march -- March
  | april -- April
  | may -- May
  | june -- June
  | july -- July
  | august -- August
  | september -- September
  | october -- October
  | november -- November
  | december -- December
  | unlisted (byte : { byte : UInt8 // byte ∉ DeliveryMonth.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DeliveryMonth

def toByte : DeliveryMonth → UInt8
  | .january => 0x46
  | .february => 0x47
  | .march => 0x48
  | .april => 0x4A
  | .may => 0x4B
  | .june => 0x4D
  | .july => 0x4E
  | .august => 0x51
  | .september => 0x55
  | .october => 0x56
  | .november => 0x58
  | .december => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DeliveryMonth :=
  if byte = 0x46 then .january
  else if byte = 0x47 then .february
  else if byte = 0x48 then .march
  else if byte = 0x4A then .april
  else if byte = 0x4B then .may
  else if byte = 0x4D then .june
  else if byte = 0x4E then .july
  else if byte = 0x51 then .august
  else if byte = 0x55 then .september
  else if byte = 0x56 then .october
  else if byte = 0x58 then .november
  else .december

def ofByte (byte : UInt8) : DeliveryMonth :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DeliveryMonth) : ofByte value.toByte = value := by
  cases value with
  | january => decide
  | february => decide
  | march => decide
  | april => decide
  | may => decide
  | june => decide
  | july => decide
  | august => decide
  | september => decide
  | october => decide
  | november => decide
  | december => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DeliveryMonth) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DeliveryMonth × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DeliveryMonth) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : DeliveryMonth) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : DeliveryMonth) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DeliveryMonth

/-- Price Indicator Marker: one byte code -/
def FuturesTradeMessagePriceIndicatorMarker.codes : List UInt8 :=
  [0x41, 0x42, 0x20, 0x44, 0x45, 0x47, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x50, 0x51, 0x52, 0x53, 0x74, 0x54, 0x55, 0x56, 0x59, 0x5A]

inductive FuturesTradeMessagePriceIndicatorMarker where
  | asoftrade -- Asoftrade
  | blockTrade -- Block Trade
  | actualTransactionTookPlace -- Actual Transaction Took Place
  | crossed -- Crossed
  | efpReporting -- Efp Reporting
  | contingentTrade -- Contingent Trade
  | risklessBasisCross -- Riskless Basis Cross
  | impliedTrade -- Implied Trade
  | deltaTrade -- Delta Trade
  | committedBlock -- Committed Block
  | lateTrade -- Late Trade
  | forFutureUse -- For Future Use
  | forFutureUse_4e -- For Future Use
  | strategyReporting -- Strategy Reporting
  | forFutureUse_51 -- For Future Use
  | efrReporting -- Efr Reporting
  | referencePrice -- Reference Price
  | tradeCorrection -- Trade Correction
  | committed -- Committed
  | basisOnClose -- Basis On Close
  | priceVolumeAdjustment -- Price Volume Adjustment
  | forFutureUse_59 -- For Future Use
  | forFutureUse_5a -- For Future Use
  | unlisted (byte : { byte : UInt8 // byte ∉ FuturesTradeMessagePriceIndicatorMarker.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace FuturesTradeMessagePriceIndicatorMarker

def toByte : FuturesTradeMessagePriceIndicatorMarker → UInt8
  | .asoftrade => 0x41
  | .blockTrade => 0x42
  | .actualTransactionTookPlace => 0x20
  | .crossed => 0x44
  | .efpReporting => 0x45
  | .contingentTrade => 0x47
  | .risklessBasisCross => 0x48
  | .impliedTrade => 0x49
  | .deltaTrade => 0x4A
  | .committedBlock => 0x4B
  | .lateTrade => 0x4C
  | .forFutureUse => 0x4D
  | .forFutureUse_4e => 0x4E
  | .strategyReporting => 0x50
  | .forFutureUse_51 => 0x51
  | .efrReporting => 0x52
  | .referencePrice => 0x53
  | .tradeCorrection => 0x74
  | .committed => 0x54
  | .basisOnClose => 0x55
  | .priceVolumeAdjustment => 0x56
  | .forFutureUse_59 => 0x59
  | .forFutureUse_5a => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : FuturesTradeMessagePriceIndicatorMarker :=
  if byte = 0x41 then .asoftrade
  else if byte = 0x42 then .blockTrade
  else if byte = 0x20 then .actualTransactionTookPlace
  else if byte = 0x44 then .crossed
  else if byte = 0x45 then .efpReporting
  else if byte = 0x47 then .contingentTrade
  else if byte = 0x48 then .risklessBasisCross
  else if byte = 0x49 then .impliedTrade
  else if byte = 0x4A then .deltaTrade
  else if byte = 0x4B then .committedBlock
  else if byte = 0x4C then .lateTrade
  else if byte = 0x4D then .forFutureUse
  else if byte = 0x4E then .forFutureUse_4e
  else if byte = 0x50 then .strategyReporting
  else if byte = 0x51 then .forFutureUse_51
  else if byte = 0x52 then .efrReporting
  else if byte = 0x53 then .referencePrice
  else if byte = 0x74 then .tradeCorrection
  else if byte = 0x54 then .committed
  else if byte = 0x55 then .basisOnClose
  else if byte = 0x56 then .priceVolumeAdjustment
  else if byte = 0x59 then .forFutureUse_59
  else .forFutureUse_5a

def ofByte (byte : UInt8) : FuturesTradeMessagePriceIndicatorMarker :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : FuturesTradeMessagePriceIndicatorMarker) : ofByte value.toByte = value := by
  cases value with
  | asoftrade => decide
  | blockTrade => decide
  | actualTransactionTookPlace => decide
  | crossed => decide
  | efpReporting => decide
  | contingentTrade => decide
  | risklessBasisCross => decide
  | impliedTrade => decide
  | deltaTrade => decide
  | committedBlock => decide
  | lateTrade => decide
  | forFutureUse => decide
  | forFutureUse_4e => decide
  | strategyReporting => decide
  | forFutureUse_51 => decide
  | efrReporting => decide
  | referencePrice => decide
  | tradeCorrection => decide
  | committed => decide
  | basisOnClose => decide
  | priceVolumeAdjustment => decide
  | forFutureUse_59 => decide
  | forFutureUse_5a => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : FuturesTradeMessagePriceIndicatorMarker) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (FuturesTradeMessagePriceIndicatorMarker × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : FuturesTradeMessagePriceIndicatorMarker) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : FuturesTradeMessagePriceIndicatorMarker) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : FuturesTradeMessagePriceIndicatorMarker) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end FuturesTradeMessagePriceIndicatorMarker

/-- Trade Price Sign: one byte code -/
def TradePriceSign.codes : List UInt8 :=
  [0x2B, 0x2D]

inductive TradePriceSign where
  | positive -- Positive
  | negative -- Negative
  | unlisted (byte : { byte : UInt8 // byte ∉ TradePriceSign.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradePriceSign

def toByte : TradePriceSign → UInt8
  | .positive => 0x2B
  | .negative => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradePriceSign :=
  if byte = 0x2B then .positive
  else .negative

def ofByte (byte : UInt8) : TradePriceSign :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradePriceSign) : ofByte value.toByte = value := by
  cases value with
  | positive => decide
  | negative => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradePriceSign) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradePriceSign × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradePriceSign) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TradePriceSign) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TradePriceSign) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradePriceSign

/-- Expiry Month Swap Future: one byte code -/
def ExpiryMonthSwapFuture.codes : List UInt8 :=
  [0x46, 0x47, 0x48, 0x4A, 0x4B, 0x4D, 0x4E, 0x51, 0x55, 0x56, 0x58, 0x5A]

inductive ExpiryMonthSwapFuture where
  | january -- January
  | february -- February
  | march -- March
  | april -- April
  | may -- May
  | june -- June
  | july -- July
  | august -- August
  | september -- September
  | october -- October
  | november -- November
  | december -- December
  | unlisted (byte : { byte : UInt8 // byte ∉ ExpiryMonthSwapFuture.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExpiryMonthSwapFuture

def toByte : ExpiryMonthSwapFuture → UInt8
  | .january => 0x46
  | .february => 0x47
  | .march => 0x48
  | .april => 0x4A
  | .may => 0x4B
  | .june => 0x4D
  | .july => 0x4E
  | .august => 0x51
  | .september => 0x55
  | .october => 0x56
  | .november => 0x58
  | .december => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExpiryMonthSwapFuture :=
  if byte = 0x46 then .january
  else if byte = 0x47 then .february
  else if byte = 0x48 then .march
  else if byte = 0x4A then .april
  else if byte = 0x4B then .may
  else if byte = 0x4D then .june
  else if byte = 0x4E then .july
  else if byte = 0x51 then .august
  else if byte = 0x55 then .september
  else if byte = 0x56 then .october
  else if byte = 0x58 then .november
  else .december

def ofByte (byte : UInt8) : ExpiryMonthSwapFuture :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExpiryMonthSwapFuture) : ofByte value.toByte = value := by
  cases value with
  | january => decide
  | february => decide
  | march => decide
  | april => decide
  | may => decide
  | june => decide
  | july => decide
  | august => decide
  | september => decide
  | october => decide
  | november => decide
  | december => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ExpiryMonthSwapFuture) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ExpiryMonthSwapFuture × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ExpiryMonthSwapFuture) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ExpiryMonthSwapFuture) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ExpiryMonthSwapFuture) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ExpiryMonthSwapFuture

/-- Requested Market Side: one byte code -/
def RequestedMarketSide.codes : List UInt8 :=
  [0x42, 0x53, 0x32]

inductive RequestedMarketSide where
  | buy -- Buy
  | sell -- Sell
  | both -- Both
  | unlisted (byte : { byte : UInt8 // byte ∉ RequestedMarketSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RequestedMarketSide

def toByte : RequestedMarketSide → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .both => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RequestedMarketSide :=
  if byte = 0x42 then .buy
  else if byte = 0x53 then .sell
  else .both

def ofByte (byte : UInt8) : RequestedMarketSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RequestedMarketSide) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | both => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RequestedMarketSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RequestedMarketSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RequestedMarketSide) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : RequestedMarketSide) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : RequestedMarketSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RequestedMarketSide

/-- Series Status: one byte code -/
def SeriesStatus.codes : List UInt8 :=
  [0x59, 0x4F, 0x54, 0x46, 0x45, 0x48, 0x52, 0x53, 0x5A, 0x41, 0x43, 0x20]

inductive SeriesStatus where
  | preOpeningPhase -- Pre Opening Phase
  | openingPhase -- Opening Phase
  | openedForTrading -- Opened For Trading
  | forbiddenPhase -- Forbidden Phase
  | interventionBeforeOpening -- Intervention Before Opening
  | tradingHalted -- Trading Halted
  | reservedPhase -- Reserved Phase
  | suspendedPhase -- Suspended Phase
  | frozen -- Frozen
  | surveillanceInterventionPhase -- Surveillance Intervention Phase
  | endOfDayInquiriesPhase -- End Of Day Inquiries Phase
  | ifNotUsed -- If Not Used
  | unlisted (byte : { byte : UInt8 // byte ∉ SeriesStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SeriesStatus

def toByte : SeriesStatus → UInt8
  | .preOpeningPhase => 0x59
  | .openingPhase => 0x4F
  | .openedForTrading => 0x54
  | .forbiddenPhase => 0x46
  | .interventionBeforeOpening => 0x45
  | .tradingHalted => 0x48
  | .reservedPhase => 0x52
  | .suspendedPhase => 0x53
  | .frozen => 0x5A
  | .surveillanceInterventionPhase => 0x41
  | .endOfDayInquiriesPhase => 0x43
  | .ifNotUsed => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SeriesStatus :=
  if byte = 0x59 then .preOpeningPhase
  else if byte = 0x4F then .openingPhase
  else if byte = 0x54 then .openedForTrading
  else if byte = 0x46 then .forbiddenPhase
  else if byte = 0x45 then .interventionBeforeOpening
  else if byte = 0x48 then .tradingHalted
  else if byte = 0x52 then .reservedPhase
  else if byte = 0x53 then .suspendedPhase
  else if byte = 0x5A then .frozen
  else if byte = 0x41 then .surveillanceInterventionPhase
  else if byte = 0x43 then .endOfDayInquiriesPhase
  else .ifNotUsed

def ofByte (byte : UInt8) : SeriesStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SeriesStatus) : ofByte value.toByte = value := by
  cases value with
  | preOpeningPhase => decide
  | openingPhase => decide
  | openedForTrading => decide
  | forbiddenPhase => decide
  | interventionBeforeOpening => decide
  | tradingHalted => decide
  | reservedPhase => decide
  | suspendedPhase => decide
  | frozen => decide
  | surveillanceInterventionPhase => decide
  | endOfDayInquiriesPhase => decide
  | ifNotUsed => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SeriesStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SeriesStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SeriesStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SeriesStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SeriesStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SeriesStatus

/-- Instrument Status Marker: one byte code -/
def InstrumentStatusMarker.codes : List UInt8 :=
  [0x59, 0x4F, 0x54, 0x46, 0x45, 0x48, 0x52, 0x53, 0x5A, 0x41, 0x43, 0x20]

inductive InstrumentStatusMarker where
  | preOpeningPhase -- Pre Opening Phase
  | openingPhase -- Opening Phase
  | openedForTrading -- Opened For Trading
  | forbiddenPhase -- Forbidden Phase
  | interventionBeforeOpening -- Intervention Before Opening
  | tradingHalted -- Trading Halted
  | reservedPhase -- Reserved Phase
  | suspendedPhase -- Suspended Phase
  | frozen -- Frozen
  | surveillanceInterventionPhase -- Surveillance Intervention Phase
  | endOfDayInquiriesPhase -- End Of Day Inquiries Phase
  | ifNotUsed -- If Not Used
  | unlisted (byte : { byte : UInt8 // byte ∉ InstrumentStatusMarker.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InstrumentStatusMarker

def toByte : InstrumentStatusMarker → UInt8
  | .preOpeningPhase => 0x59
  | .openingPhase => 0x4F
  | .openedForTrading => 0x54
  | .forbiddenPhase => 0x46
  | .interventionBeforeOpening => 0x45
  | .tradingHalted => 0x48
  | .reservedPhase => 0x52
  | .suspendedPhase => 0x53
  | .frozen => 0x5A
  | .surveillanceInterventionPhase => 0x41
  | .endOfDayInquiriesPhase => 0x43
  | .ifNotUsed => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : InstrumentStatusMarker :=
  if byte = 0x59 then .preOpeningPhase
  else if byte = 0x4F then .openingPhase
  else if byte = 0x54 then .openedForTrading
  else if byte = 0x46 then .forbiddenPhase
  else if byte = 0x45 then .interventionBeforeOpening
  else if byte = 0x48 then .tradingHalted
  else if byte = 0x52 then .reservedPhase
  else if byte = 0x53 then .suspendedPhase
  else if byte = 0x5A then .frozen
  else if byte = 0x41 then .surveillanceInterventionPhase
  else if byte = 0x43 then .endOfDayInquiriesPhase
  else .ifNotUsed

def ofByte (byte : UInt8) : InstrumentStatusMarker :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InstrumentStatusMarker) : ofByte value.toByte = value := by
  cases value with
  | preOpeningPhase => decide
  | openingPhase => decide
  | openedForTrading => decide
  | forbiddenPhase => decide
  | interventionBeforeOpening => decide
  | tradingHalted => decide
  | reservedPhase => decide
  | suspendedPhase => decide
  | frozen => decide
  | surveillanceInterventionPhase => decide
  | endOfDayInquiriesPhase => decide
  | ifNotUsed => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : InstrumentStatusMarker) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (InstrumentStatusMarker × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : InstrumentStatusMarker) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : InstrumentStatusMarker) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : InstrumentStatusMarker) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end InstrumentStatusMarker

/-- Bid Price Sign: one byte code -/
def BidPriceSign.codes : List UInt8 :=
  [0x2B, 0x2D]

inductive BidPriceSign where
  | positive -- Positive
  | negative -- Negative
  | unlisted (byte : { byte : UInt8 // byte ∉ BidPriceSign.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BidPriceSign

def toByte : BidPriceSign → UInt8
  | .positive => 0x2B
  | .negative => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BidPriceSign :=
  if byte = 0x2B then .positive
  else .negative

def ofByte (byte : UInt8) : BidPriceSign :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BidPriceSign) : ofByte value.toByte = value := by
  cases value with
  | positive => decide
  | negative => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BidPriceSign) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BidPriceSign × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BidPriceSign) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : BidPriceSign) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : BidPriceSign) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BidPriceSign

/-- Ask Price Sign: one byte code -/
def AskPriceSign.codes : List UInt8 :=
  [0x2B, 0x2D]

inductive AskPriceSign where
  | positive -- Positive
  | negative -- Negative
  | unlisted (byte : { byte : UInt8 // byte ∉ AskPriceSign.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AskPriceSign

def toByte : AskPriceSign → UInt8
  | .positive => 0x2B
  | .negative => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AskPriceSign :=
  if byte = 0x2B then .positive
  else .negative

def ofByte (byte : UInt8) : AskPriceSign :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AskPriceSign) : ofByte value.toByte = value := by
  cases value with
  | positive => decide
  | negative => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AskPriceSign) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AskPriceSign × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AskPriceSign) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : AskPriceSign) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : AskPriceSign) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AskPriceSign

/-- Instrument Status Marker: one byte code -/
def StrategyQuoteMessageInstrumentStatusMarker.codes : List UInt8 :=
  [0x59, 0x4F, 0x54, 0x46, 0x45, 0x48, 0x52, 0x53, 0x5A, 0x41, 0x43, 0x20]

inductive StrategyQuoteMessageInstrumentStatusMarker where
  | preopeningPhase -- Preopening Phase
  | openingPhase -- Opening Phase
  | openedForTrading -- Opened For Trading
  | forbiddenPhase -- Forbidden Phase
  | interventionBeforeOpening -- Intervention Before Opening
  | tradingHalted -- Trading Halted
  | reservedPhase -- Reserved Phase
  | suspendedPhase -- Suspended Phase
  | frozen -- Frozen
  | surveillanceInterventionPhase -- Surveillance Intervention Phase
  | endofDayInquiriesPhase -- Endof Day Inquiries Phase
  | ifNotUsed -- If Not Used
  | unlisted (byte : { byte : UInt8 // byte ∉ StrategyQuoteMessageInstrumentStatusMarker.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace StrategyQuoteMessageInstrumentStatusMarker

def toByte : StrategyQuoteMessageInstrumentStatusMarker → UInt8
  | .preopeningPhase => 0x59
  | .openingPhase => 0x4F
  | .openedForTrading => 0x54
  | .forbiddenPhase => 0x46
  | .interventionBeforeOpening => 0x45
  | .tradingHalted => 0x48
  | .reservedPhase => 0x52
  | .suspendedPhase => 0x53
  | .frozen => 0x5A
  | .surveillanceInterventionPhase => 0x41
  | .endofDayInquiriesPhase => 0x43
  | .ifNotUsed => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : StrategyQuoteMessageInstrumentStatusMarker :=
  if byte = 0x59 then .preopeningPhase
  else if byte = 0x4F then .openingPhase
  else if byte = 0x54 then .openedForTrading
  else if byte = 0x46 then .forbiddenPhase
  else if byte = 0x45 then .interventionBeforeOpening
  else if byte = 0x48 then .tradingHalted
  else if byte = 0x52 then .reservedPhase
  else if byte = 0x53 then .suspendedPhase
  else if byte = 0x5A then .frozen
  else if byte = 0x41 then .surveillanceInterventionPhase
  else if byte = 0x43 then .endofDayInquiriesPhase
  else .ifNotUsed

def ofByte (byte : UInt8) : StrategyQuoteMessageInstrumentStatusMarker :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : StrategyQuoteMessageInstrumentStatusMarker) : ofByte value.toByte = value := by
  cases value with
  | preopeningPhase => decide
  | openingPhase => decide
  | openedForTrading => decide
  | forbiddenPhase => decide
  | interventionBeforeOpening => decide
  | tradingHalted => decide
  | reservedPhase => decide
  | suspendedPhase => decide
  | frozen => decide
  | surveillanceInterventionPhase => decide
  | endofDayInquiriesPhase => decide
  | ifNotUsed => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : StrategyQuoteMessageInstrumentStatusMarker) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (StrategyQuoteMessageInstrumentStatusMarker × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : StrategyQuoteMessageInstrumentStatusMarker) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : StrategyQuoteMessageInstrumentStatusMarker) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : StrategyQuoteMessageInstrumentStatusMarker) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end StrategyQuoteMessageInstrumentStatusMarker

/-- Level Of Market Depth: one byte code -/
def LevelOfMarketDepth.codes : List UInt8 :=
  [0x31, 0x32, 0x33, 0x34, 0x35, 0x41]

inductive LevelOfMarketDepth where
  | level1 -- Level 1
  | level2 -- Level 2
  | level3 -- Level 3
  | level4 -- Level 4
  | level5 -- Level 5
  | implied -- Implied
  | unlisted (byte : { byte : UInt8 // byte ∉ LevelOfMarketDepth.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LevelOfMarketDepth

def toByte : LevelOfMarketDepth → UInt8
  | .level1 => 0x31
  | .level2 => 0x32
  | .level3 => 0x33
  | .level4 => 0x34
  | .level5 => 0x35
  | .implied => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LevelOfMarketDepth :=
  if byte = 0x31 then .level1
  else if byte = 0x32 then .level2
  else if byte = 0x33 then .level3
  else if byte = 0x34 then .level4
  else if byte = 0x35 then .level5
  else .implied

def ofByte (byte : UInt8) : LevelOfMarketDepth :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LevelOfMarketDepth) : ofByte value.toByte = value := by
  cases value with
  | level1 => decide
  | level2 => decide
  | level3 => decide
  | level4 => decide
  | level5 => decide
  | implied => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LevelOfMarketDepth) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LevelOfMarketDepth × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LevelOfMarketDepth) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : LevelOfMarketDepth) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : LevelOfMarketDepth) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LevelOfMarketDepth

/-- Level: one byte code -/
def Level.codes : List UInt8 :=
  [0x31, 0x32, 0x33, 0x34, 0x35, 0x41]

inductive Level where
  | level1 -- Level 1
  | level2 -- Level 2
  | level3 -- Level 3
  | level4 -- Level 4
  | level5 -- Level 5
  | implied -- Implied
  | unlisted (byte : { byte : UInt8 // byte ∉ Level.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Level

def toByte : Level → UInt8
  | .level1 => 0x31
  | .level2 => 0x32
  | .level3 => 0x33
  | .level4 => 0x34
  | .level5 => 0x35
  | .implied => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Level :=
  if byte = 0x31 then .level1
  else if byte = 0x32 then .level2
  else if byte = 0x33 then .level3
  else if byte = 0x34 then .level4
  else if byte = 0x35 then .level5
  else .implied

def ofByte (byte : UInt8) : Level :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Level) : ofByte value.toByte = value := by
  cases value with
  | level1 => decide
  | level2 => decide
  | level3 => decide
  | level4 => decide
  | level5 => decide
  | implied => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Level) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Level × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Level) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Level) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Level) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Level

/-- Market Price Indicator: one byte code -/
def MarketPriceIndicator.codes : List UInt8 :=
  [0x41, 0x42, 0x20, 0x44, 0x45, 0x47, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x50, 0x51, 0x52, 0x53, 0x74, 0x54, 0x55, 0x56, 0x59, 0x5A]

inductive MarketPriceIndicator where
  | asOfTrade -- As Of Trade
  | blockTrade -- Block Trade
  | actualTransactionTookPlace -- Actual Transaction Took Place
  | crossed -- Crossed
  | efpReporting -- Efp Reporting
  | contingentTrade -- Contingent Trade
  | risklessBasisCross -- Riskless Basis Cross
  | impliedTrade -- Implied Trade
  | deltaTrade -- Delta Trade
  | committedBlock -- Committed Block
  | lateTrade -- Late Trade
  | forFutureUse -- For Future Use
  | forFutureUse_4e -- For Future Use
  | strategyReporting -- Strategy Reporting
  | forFutureUse_51 -- For Future Use
  | efrReporting -- Efr Reporting
  | referencePrice -- Reference Price
  | tradeCorrection -- Trade Correction
  | committed -- Committed
  | basisOnClose -- Basis On Close
  | priceVolumeAdjustment -- Price Volume Adjustment
  | forFutureUse_59 -- For Future Use
  | forFutureUse_5a -- For Future Use
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketPriceIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketPriceIndicator

def toByte : MarketPriceIndicator → UInt8
  | .asOfTrade => 0x41
  | .blockTrade => 0x42
  | .actualTransactionTookPlace => 0x20
  | .crossed => 0x44
  | .efpReporting => 0x45
  | .contingentTrade => 0x47
  | .risklessBasisCross => 0x48
  | .impliedTrade => 0x49
  | .deltaTrade => 0x4A
  | .committedBlock => 0x4B
  | .lateTrade => 0x4C
  | .forFutureUse => 0x4D
  | .forFutureUse_4e => 0x4E
  | .strategyReporting => 0x50
  | .forFutureUse_51 => 0x51
  | .efrReporting => 0x52
  | .referencePrice => 0x53
  | .tradeCorrection => 0x74
  | .committed => 0x54
  | .basisOnClose => 0x55
  | .priceVolumeAdjustment => 0x56
  | .forFutureUse_59 => 0x59
  | .forFutureUse_5a => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketPriceIndicator :=
  if byte = 0x41 then .asOfTrade
  else if byte = 0x42 then .blockTrade
  else if byte = 0x20 then .actualTransactionTookPlace
  else if byte = 0x44 then .crossed
  else if byte = 0x45 then .efpReporting
  else if byte = 0x47 then .contingentTrade
  else if byte = 0x48 then .risklessBasisCross
  else if byte = 0x49 then .impliedTrade
  else if byte = 0x4A then .deltaTrade
  else if byte = 0x4B then .committedBlock
  else if byte = 0x4C then .lateTrade
  else if byte = 0x4D then .forFutureUse
  else if byte = 0x4E then .forFutureUse_4e
  else if byte = 0x50 then .strategyReporting
  else if byte = 0x51 then .forFutureUse_51
  else if byte = 0x52 then .efrReporting
  else if byte = 0x53 then .referencePrice
  else if byte = 0x74 then .tradeCorrection
  else if byte = 0x54 then .committed
  else if byte = 0x55 then .basisOnClose
  else if byte = 0x56 then .priceVolumeAdjustment
  else if byte = 0x59 then .forFutureUse_59
  else .forFutureUse_5a

def ofByte (byte : UInt8) : MarketPriceIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketPriceIndicator) : ofByte value.toByte = value := by
  cases value with
  | asOfTrade => decide
  | blockTrade => decide
  | actualTransactionTookPlace => decide
  | crossed => decide
  | efpReporting => decide
  | contingentTrade => decide
  | risklessBasisCross => decide
  | impliedTrade => decide
  | deltaTrade => decide
  | committedBlock => decide
  | lateTrade => decide
  | forFutureUse => decide
  | forFutureUse_4e => decide
  | strategyReporting => decide
  | forFutureUse_51 => decide
  | efrReporting => decide
  | referencePrice => decide
  | tradeCorrection => decide
  | committed => decide
  | basisOnClose => decide
  | priceVolumeAdjustment => decide
  | forFutureUse_59 => decide
  | forFutureUse_5a => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarketPriceIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketPriceIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketPriceIndicator) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : MarketPriceIndicator) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : MarketPriceIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarketPriceIndicator

/-- Option Type: one byte code -/
def OptionType.codes : List UInt8 :=
  [0x41, 0x45]

inductive OptionType where
  | american -- American
  | european -- European
  | unlisted (byte : { byte : UInt8 // byte ∉ OptionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OptionType

def toByte : OptionType → UInt8
  | .american => 0x41
  | .european => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OptionType :=
  if byte = 0x41 then .american
  else .european

def ofByte (byte : UInt8) : OptionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OptionType) : ofByte value.toByte = value := by
  cases value with
  | american => decide
  | european => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OptionType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OptionType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OptionType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OptionType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OptionType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OptionType

/-- Delivery Type: one byte code -/
def DeliveryType.codes : List UInt8 :=
  [0x43, 0x50]

inductive DeliveryType where
  | cash -- Cash
  | physical -- Physical
  | unlisted (byte : { byte : UInt8 // byte ∉ DeliveryType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DeliveryType

def toByte : DeliveryType → UInt8
  | .cash => 0x43
  | .physical => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DeliveryType :=
  if byte = 0x43 then .cash
  else .physical

def ofByte (byte : UInt8) : DeliveryType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DeliveryType) : ofByte value.toByte = value := by
  cases value with
  | cash => decide
  | physical => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DeliveryType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DeliveryType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DeliveryType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : DeliveryType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : DeliveryType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DeliveryType

/-- Associated Product Delivery Month: one byte code -/
def AssociatedProductDeliveryMonth.codes : List UInt8 :=
  [0x46, 0x47, 0x48, 0x4A, 0x4B, 0x4D, 0x4E, 0x51, 0x55, 0x56, 0x58, 0x5A]

inductive AssociatedProductDeliveryMonth where
  | january -- January
  | february -- February
  | march -- March
  | april -- April
  | may -- May
  | june -- June
  | july -- July
  | august -- August
  | september -- September
  | october -- October
  | november -- November
  | december -- December
  | unlisted (byte : { byte : UInt8 // byte ∉ AssociatedProductDeliveryMonth.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AssociatedProductDeliveryMonth

def toByte : AssociatedProductDeliveryMonth → UInt8
  | .january => 0x46
  | .february => 0x47
  | .march => 0x48
  | .april => 0x4A
  | .may => 0x4B
  | .june => 0x4D
  | .july => 0x4E
  | .august => 0x51
  | .september => 0x55
  | .october => 0x56
  | .november => 0x58
  | .december => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AssociatedProductDeliveryMonth :=
  if byte = 0x46 then .january
  else if byte = 0x47 then .february
  else if byte = 0x48 then .march
  else if byte = 0x4A then .april
  else if byte = 0x4B then .may
  else if byte = 0x4D then .june
  else if byte = 0x4E then .july
  else if byte = 0x51 then .august
  else if byte = 0x55 then .september
  else if byte = 0x56 then .october
  else if byte = 0x58 then .november
  else .december

def ofByte (byte : UInt8) : AssociatedProductDeliveryMonth :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AssociatedProductDeliveryMonth) : ofByte value.toByte = value := by
  cases value with
  | january => decide
  | february => decide
  | march => decide
  | april => decide
  | may => decide
  | june => decide
  | july => decide
  | august => decide
  | september => decide
  | october => decide
  | november => decide
  | december => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AssociatedProductDeliveryMonth) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AssociatedProductDeliveryMonth × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AssociatedProductDeliveryMonth) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : AssociatedProductDeliveryMonth) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : AssociatedProductDeliveryMonth) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AssociatedProductDeliveryMonth

/-- Strategy Allow Implied: one byte code -/
def StrategyAllowImplied.codes : List UInt8 :=
  [0x59, 0x4E]

inductive StrategyAllowImplied where
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ StrategyAllowImplied.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace StrategyAllowImplied

def toByte : StrategyAllowImplied → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : StrategyAllowImplied :=
  if byte = 0x59 then .yes
  else .no

def ofByte (byte : UInt8) : StrategyAllowImplied :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : StrategyAllowImplied) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : StrategyAllowImplied) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (StrategyAllowImplied × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : StrategyAllowImplied) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : StrategyAllowImplied) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : StrategyAllowImplied) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end StrategyAllowImplied

/-- Day Count Convention: one byte code -/
def DayCountConvention.codes : List UInt8 :=
  [0x41, 0x42, 0x43]

inductive DayCountConvention where
  | act365 -- Act 365
  | act360 -- Act 360
  | thirty360 -- Thirty 360
  | unlisted (byte : { byte : UInt8 // byte ∉ DayCountConvention.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DayCountConvention

def toByte : DayCountConvention → UInt8
  | .act365 => 0x41
  | .act360 => 0x42
  | .thirty360 => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DayCountConvention :=
  if byte = 0x41 then .act365
  else if byte = 0x42 then .act360
  else .thirty360

def ofByte (byte : UInt8) : DayCountConvention :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DayCountConvention) : ofByte value.toByte = value := by
  cases value with
  | act365 => decide
  | act360 => decide
  | thirty360 => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DayCountConvention) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DayCountConvention × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DayCountConvention) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : DayCountConvention) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : DayCountConvention) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DayCountConvention

/-- Tick: one byte code -/
def Tick.codes : List UInt8 :=
  [0x2B, 0x2D]

inductive Tick where
  | uptick -- Uptick
  | downtick -- Downtick
  | unlisted (byte : { byte : UInt8 // byte ∉ Tick.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Tick

def toByte : Tick → UInt8
  | .uptick => 0x2B
  | .downtick => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Tick :=
  if byte = 0x2B then .uptick
  else .downtick

def ofByte (byte : UInt8) : Tick :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Tick) : ofByte value.toByte = value := by
  cases value with
  | uptick => decide
  | downtick => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Tick) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Tick × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Tick) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Tick) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Tick) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Tick

/-- Reason: one byte code -/
def Reason.codes : List UInt8 :=
  [0x53, 0x45, 0x55, 0x43]

inductive Reason where
  | startOfDay -- Start Of Day
  | endOfDay -- End Of Day
  | instrumentNewOrUpdate -- Instrument New Or Update
  | tradeCancellation -- Trade Cancellation
  | unlisted (byte : { byte : UInt8 // byte ∉ Reason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Reason

def toByte : Reason → UInt8
  | .startOfDay => 0x53
  | .endOfDay => 0x45
  | .instrumentNewOrUpdate => 0x55
  | .tradeCancellation => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Reason :=
  if byte = 0x53 then .startOfDay
  else if byte = 0x45 then .endOfDay
  else if byte = 0x55 then .instrumentNewOrUpdate
  else .tradeCancellation

def ofByte (byte : UInt8) : Reason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Reason) : ofByte value.toByte = value := by
  cases value with
  | startOfDay => decide
  | endOfDay => decide
  | instrumentNewOrUpdate => decide
  | tradeCancellation => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Reason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Reason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Reason) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Reason) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Reason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Reason

/-- Last Price Sign: one byte code -/
def LastPriceSign.codes : List UInt8 :=
  [0x2B, 0x2D]

inductive LastPriceSign where
  | positive -- Positive
  | negative -- Negative
  | unlisted (byte : { byte : UInt8 // byte ∉ LastPriceSign.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LastPriceSign

def toByte : LastPriceSign → UInt8
  | .positive => 0x2B
  | .negative => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LastPriceSign :=
  if byte = 0x2B then .positive
  else .negative

def ofByte (byte : UInt8) : LastPriceSign :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LastPriceSign) : ofByte value.toByte = value := by
  cases value with
  | positive => decide
  | negative => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LastPriceSign) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LastPriceSign × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LastPriceSign) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : LastPriceSign) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : LastPriceSign) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LastPriceSign

/-- Open Price Sign: one byte code -/
def OpenPriceSign.codes : List UInt8 :=
  [0x2B, 0x2D]

inductive OpenPriceSign where
  | positive -- Positive
  | negative -- Negative
  | unlisted (byte : { byte : UInt8 // byte ∉ OpenPriceSign.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OpenPriceSign

def toByte : OpenPriceSign → UInt8
  | .positive => 0x2B
  | .negative => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OpenPriceSign :=
  if byte = 0x2B then .positive
  else .negative

def ofByte (byte : UInt8) : OpenPriceSign :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OpenPriceSign) : ofByte value.toByte = value := by
  cases value with
  | positive => decide
  | negative => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OpenPriceSign) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OpenPriceSign × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OpenPriceSign) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OpenPriceSign) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OpenPriceSign) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OpenPriceSign

/-- High Price Sign: one byte code -/
def HighPriceSign.codes : List UInt8 :=
  [0x2B, 0x2D]

inductive HighPriceSign where
  | positive -- Positive
  | negative -- Negative
  | unlisted (byte : { byte : UInt8 // byte ∉ HighPriceSign.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace HighPriceSign

def toByte : HighPriceSign → UInt8
  | .positive => 0x2B
  | .negative => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : HighPriceSign :=
  if byte = 0x2B then .positive
  else .negative

def ofByte (byte : UInt8) : HighPriceSign :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : HighPriceSign) : ofByte value.toByte = value := by
  cases value with
  | positive => decide
  | negative => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : HighPriceSign) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (HighPriceSign × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : HighPriceSign) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : HighPriceSign) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : HighPriceSign) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end HighPriceSign

/-- Low Price Sign: one byte code -/
def LowPriceSign.codes : List UInt8 :=
  [0x2B, 0x2D]

inductive LowPriceSign where
  | positive -- Positive
  | negative -- Negative
  | unlisted (byte : { byte : UInt8 // byte ∉ LowPriceSign.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LowPriceSign

def toByte : LowPriceSign → UInt8
  | .positive => 0x2B
  | .negative => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LowPriceSign :=
  if byte = 0x2B then .positive
  else .negative

def ofByte (byte : UInt8) : LowPriceSign :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LowPriceSign) : ofByte value.toByte = value := by
  cases value with
  | positive => decide
  | negative => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LowPriceSign) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LowPriceSign × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LowPriceSign) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : LowPriceSign) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : LowPriceSign) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LowPriceSign

/-- Leg Ratio Sign: one byte code -/
def LegRatioSign.codes : List UInt8 :=
  [0x2B, 0x2D]

inductive LegRatioSign where
  | buyOfTheUnderlying -- Buy Of The Underlying
  | sellOfTheUnderlying -- Sell Of The Underlying
  | unlisted (byte : { byte : UInt8 // byte ∉ LegRatioSign.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LegRatioSign

def toByte : LegRatioSign → UInt8
  | .buyOfTheUnderlying => 0x2B
  | .sellOfTheUnderlying => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LegRatioSign :=
  if byte = 0x2B then .buyOfTheUnderlying
  else .sellOfTheUnderlying

def ofByte (byte : UInt8) : LegRatioSign :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LegRatioSign) : ofByte value.toByte = value := by
  cases value with
  | buyOfTheUnderlying => decide
  | sellOfTheUnderlying => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LegRatioSign) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LegRatioSign × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LegRatioSign) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : LegRatioSign) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : LegRatioSign) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LegRatioSign

/-- Group Status: one byte code -/
def GroupStatus.codes : List UInt8 :=
  [0x59, 0x4F, 0x54, 0x46, 0x45, 0x48, 0x41, 0x43, 0x20]

inductive GroupStatus where
  | preOpeningPhase -- Pre Opening Phase
  | openingPhase -- Opening Phase
  | openedForTrading -- Opened For Trading
  | forbiddenPhase -- Forbidden Phase
  | interventionBeforeOpening -- Intervention Before Opening
  | tradingHalted -- Trading Halted
  | surveillanceInterventionPhase -- Surveillance Intervention Phase
  | endOfDayInquiriesPhase -- End Of Day Inquiries Phase
  | ifNotUsed -- If Not Used
  | unlisted (byte : { byte : UInt8 // byte ∉ GroupStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace GroupStatus

def toByte : GroupStatus → UInt8
  | .preOpeningPhase => 0x59
  | .openingPhase => 0x4F
  | .openedForTrading => 0x54
  | .forbiddenPhase => 0x46
  | .interventionBeforeOpening => 0x45
  | .tradingHalted => 0x48
  | .surveillanceInterventionPhase => 0x41
  | .endOfDayInquiriesPhase => 0x43
  | .ifNotUsed => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : GroupStatus :=
  if byte = 0x59 then .preOpeningPhase
  else if byte = 0x4F then .openingPhase
  else if byte = 0x54 then .openedForTrading
  else if byte = 0x46 then .forbiddenPhase
  else if byte = 0x45 then .interventionBeforeOpening
  else if byte = 0x48 then .tradingHalted
  else if byte = 0x41 then .surveillanceInterventionPhase
  else if byte = 0x43 then .endOfDayInquiriesPhase
  else .ifNotUsed

def ofByte (byte : UInt8) : GroupStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : GroupStatus) : ofByte value.toByte = value := by
  cases value with
  | preOpeningPhase => decide
  | openingPhase => decide
  | openedForTrading => decide
  | forbiddenPhase => decide
  | interventionBeforeOpening => decide
  | tradingHalted => decide
  | surveillanceInterventionPhase => decide
  | endOfDayInquiriesPhase => decide
  | ifNotUsed => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : GroupStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (GroupStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : GroupStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : GroupStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : GroupStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end GroupStatus

/-- Continue Marker: one byte code -/
def ContinueMarker.codes : List UInt8 :=
  [0x30, 0x31]

inductive ContinueMarker where
  | bulletinContinuesInNextRecord -- Bulletin Continues In Next Record
  | bulletinEnded -- Bulletin Ended
  | unlisted (byte : { byte : UInt8 // byte ∉ ContinueMarker.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ContinueMarker

def toByte : ContinueMarker → UInt8
  | .bulletinContinuesInNextRecord => 0x30
  | .bulletinEnded => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ContinueMarker :=
  if byte = 0x30 then .bulletinContinuesInNextRecord
  else .bulletinEnded

def ofByte (byte : UInt8) : ContinueMarker :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ContinueMarker) : ofByte value.toByte = value := by
  cases value with
  | bulletinContinuesInNextRecord => decide
  | bulletinEnded => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ContinueMarker) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ContinueMarker × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ContinueMarker) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ContinueMarker) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ContinueMarker) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ContinueMarker

/-- Strike Price Instrument Fraction Pair: 8 bytes -/
structure StrikePriceInstrumentFractionPair where
  rawStrikePriceInstrument : Alpha 7
  strikePriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace StrikePriceInstrumentFractionPair

def encode (message : StrikePriceInstrumentFractionPair) : List UInt8 :=
  Alpha.encode message.rawStrikePriceInstrument
    ++ (encodeUInt 1 message.strikePriceFractionIndicator)

def decode (bytes : List UInt8) : Option (StrikePriceInstrumentFractionPair × List UInt8) := do
  let (rawStrikePriceInstrument, bytes) ← Alpha.decode 7 bytes
  let (strikePriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawStrikePriceInstrument, strikePriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : StrikePriceInstrumentFractionPair) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : StrikePriceInstrumentFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrikePriceInstrumentFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end StrikePriceInstrumentFractionPair

/-- Trade Price Fraction Pair: 7 bytes -/
structure TradePriceFractionPair where
  rawTradePrice : Alpha 6
  tradePriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace TradePriceFractionPair

def encode (message : TradePriceFractionPair) : List UInt8 :=
  Alpha.encode message.rawTradePrice
    ++ (encodeUInt 1 message.tradePriceFractionIndicator)

def decode (bytes : List UInt8) : Option (TradePriceFractionPair × List UInt8) := do
  let (rawTradePrice, bytes) ← Alpha.decode 6 bytes
  let (tradePriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawTradePrice, tradePriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : TradePriceFractionPair) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : TradePriceFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradePriceFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TradePriceFractionPair

/-- Net Change Fraction Pair: 7 bytes -/
structure NetChangeFractionPair where
  rawNetChange : Alpha 6
  netChangeFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace NetChangeFractionPair

def encode (message : NetChangeFractionPair) : List UInt8 :=
  Alpha.encode message.rawNetChange
    ++ (encodeUInt 1 message.netChangeFractionIndicator)

def decode (bytes : List UInt8) : Option (NetChangeFractionPair × List UInt8) := do
  let (rawNetChange, bytes) ← Alpha.decode 6 bytes
  let (netChangeFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawNetChange, netChangeFractionIndicator }, bytes)

@[simp] theorem encode_length (message : NetChangeFractionPair) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : NetChangeFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NetChangeFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end NetChangeFractionPair

/-- Option Trade Message: 76 bytes -/
structure OptionTradeMessage where
  exchangeId : ExchangeId
  rootSymbol : Alpha 6
  expiryMonth : ExpiryMonth
  filler1 : Alpha 1
  strikePriceInstrumentFractionPair : StrikePriceInstrumentFractionPair
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  volume : Alpha 8
  tradePriceFractionPair : TradePriceFractionPair
  netChangeSign : NetChangeSign
  netChangeFractionPair : NetChangeFractionPair
  filler6 : Alpha 6
  timestamp : Alpha 9
  openInterest : Alpha 7
  secondFiller1 : Alpha 1
  priceIndicatorMarker : PriceIndicatorMarker
  tradeNumber : Alpha 8
  deriving DecidableEq, Repr

namespace OptionTradeMessage

def encode (message : OptionTradeMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (ExpiryMonth.encode message.expiryMonth
    ++ (Alpha.encode message.filler1
    ++ (StrikePriceInstrumentFractionPair.encode message.strikePriceInstrumentFractionPair
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay
    ++ (Alpha.encode message.volume
    ++ (TradePriceFractionPair.encode message.tradePriceFractionPair
    ++ (NetChangeSign.encode message.netChangeSign
    ++ (NetChangeFractionPair.encode message.netChangeFractionPair
    ++ (Alpha.encode message.filler6
    ++ (Alpha.encode message.timestamp
    ++ (Alpha.encode message.openInterest
    ++ (Alpha.encode message.secondFiller1
    ++ (PriceIndicatorMarker.encode message.priceIndicatorMarker
    ++ (Alpha.encode message.tradeNumber))))))))))))))))

def decode (bytes : List UInt8) : Option (OptionTradeMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (expiryMonth, bytes) ← ExpiryMonth.decode bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (strikePriceInstrumentFractionPair, bytes) ← StrikePriceInstrumentFractionPair.decode bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePriceFractionPair, bytes) ← TradePriceFractionPair.decode bytes
  let (netChangeSign, bytes) ← NetChangeSign.decode bytes
  let (netChangeFractionPair, bytes) ← NetChangeFractionPair.decode bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (timestamp, bytes) ← Alpha.decode 9 bytes
  let (openInterest, bytes) ← Alpha.decode 7 bytes
  let (secondFiller1, bytes) ← Alpha.decode 1 bytes
  let (priceIndicatorMarker, bytes) ← PriceIndicatorMarker.decode bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ exchangeId, rootSymbol, expiryMonth, filler1, strikePriceInstrumentFractionPair, expiryYear, expiryDay, volume, tradePriceFractionPair, netChangeSign, netChangeFractionPair, filler6, timestamp, openInterest, secondFiller1, priceIndicatorMarker, tradeNumber }, bytes)

@[simp] theorem encode_length (message : OptionTradeMessage) : (encode message).length = 76 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length, ExpiryMonth.encode_length, StrikePriceInstrumentFractionPair.encode_length, TradePriceFractionPair.encode_length, NetChangeSign.encode_length, NetChangeFractionPair.encode_length, PriceIndicatorMarker.encode_length]

theorem encode_length_pos (message : OptionTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExpiryMonth.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StrikePriceInstrumentFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradePriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PriceIndicatorMarker.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OptionTradeMessage

/-- Net Change Future Options Trade Message Fraction Pair: 7 bytes -/
structure NetChangeFutureOptionsTradeMessageFractionPair where
  rawNetChangeFutureOptionsTradeMessage : Alpha 6
  netChangeFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace NetChangeFutureOptionsTradeMessageFractionPair

def encode (message : NetChangeFutureOptionsTradeMessageFractionPair) : List UInt8 :=
  Alpha.encode message.rawNetChangeFutureOptionsTradeMessage
    ++ (encodeUInt 1 message.netChangeFractionIndicator)

def decode (bytes : List UInt8) : Option (NetChangeFutureOptionsTradeMessageFractionPair × List UInt8) := do
  let (rawNetChangeFutureOptionsTradeMessage, bytes) ← Alpha.decode 6 bytes
  let (netChangeFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawNetChangeFutureOptionsTradeMessage, netChangeFractionIndicator }, bytes)

@[simp] theorem encode_length (message : NetChangeFutureOptionsTradeMessageFractionPair) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : NetChangeFutureOptionsTradeMessageFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NetChangeFutureOptionsTradeMessageFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end NetChangeFutureOptionsTradeMessageFractionPair

/-- Future Options Trade Message: 77 bytes -/
structure FutureOptionsTradeMessage where
  exchangeId : ExchangeId
  rootSymbol : Alpha 6
  contractMonthCode : ContractMonthCode
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  callPutCode : CallPutCode
  strikePriceInstrumentFractionPair : StrikePriceInstrumentFractionPair
  volume : Alpha 8
  tradePriceFractionPair : TradePriceFractionPair
  priceIndicatorMarker : PriceIndicatorMarker
  netChangeSign : NetChangeSign
  netChangeFutureOptionsTradeMessageFractionPair : NetChangeFutureOptionsTradeMessageFractionPair
  filler6 : Alpha 6
  timestamp : Alpha 9
  openInterest : Alpha 7
  filler2 : Alpha 2
  tradeNumber : Alpha 8
  deriving DecidableEq, Repr

namespace FutureOptionsTradeMessage

def encode (message : FutureOptionsTradeMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (ContractMonthCode.encode message.contractMonthCode
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay
    ++ (CallPutCode.encode message.callPutCode
    ++ (StrikePriceInstrumentFractionPair.encode message.strikePriceInstrumentFractionPair
    ++ (Alpha.encode message.volume
    ++ (TradePriceFractionPair.encode message.tradePriceFractionPair
    ++ (PriceIndicatorMarker.encode message.priceIndicatorMarker
    ++ (NetChangeSign.encode message.netChangeSign
    ++ (NetChangeFutureOptionsTradeMessageFractionPair.encode message.netChangeFutureOptionsTradeMessageFractionPair
    ++ (Alpha.encode message.filler6
    ++ (Alpha.encode message.timestamp
    ++ (Alpha.encode message.openInterest
    ++ (Alpha.encode message.filler2
    ++ (Alpha.encode message.tradeNumber))))))))))))))))

def decode (bytes : List UInt8) : Option (FutureOptionsTradeMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (contractMonthCode, bytes) ← ContractMonthCode.decode bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (callPutCode, bytes) ← CallPutCode.decode bytes
  let (strikePriceInstrumentFractionPair, bytes) ← StrikePriceInstrumentFractionPair.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePriceFractionPair, bytes) ← TradePriceFractionPair.decode bytes
  let (priceIndicatorMarker, bytes) ← PriceIndicatorMarker.decode bytes
  let (netChangeSign, bytes) ← NetChangeSign.decode bytes
  let (netChangeFutureOptionsTradeMessageFractionPair, bytes) ← NetChangeFutureOptionsTradeMessageFractionPair.decode bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (timestamp, bytes) ← Alpha.decode 9 bytes
  let (openInterest, bytes) ← Alpha.decode 7 bytes
  let (filler2, bytes) ← Alpha.decode 2 bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ exchangeId, rootSymbol, contractMonthCode, expiryYear, expiryDay, callPutCode, strikePriceInstrumentFractionPair, volume, tradePriceFractionPair, priceIndicatorMarker, netChangeSign, netChangeFutureOptionsTradeMessageFractionPair, filler6, timestamp, openInterest, filler2, tradeNumber }, bytes)

@[simp] theorem encode_length (message : FutureOptionsTradeMessage) : (encode message).length = 77 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length, ContractMonthCode.encode_length, CallPutCode.encode_length, StrikePriceInstrumentFractionPair.encode_length, TradePriceFractionPair.encode_length, PriceIndicatorMarker.encode_length, NetChangeSign.encode_length, NetChangeFutureOptionsTradeMessageFractionPair.encode_length]

theorem encode_length_pos (message : FutureOptionsTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FutureOptionsTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ContractMonthCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CallPutCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StrikePriceInstrumentFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradePriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PriceIndicatorMarker.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeFutureOptionsTradeMessageFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FutureOptionsTradeMessage

/-- Net Change Futures Trade Message Fraction Pair: 7 bytes -/
structure NetChangeFuturesTradeMessageFractionPair where
  rawNetChangeFuturesTradeMessage : Alpha 6
  netChangeFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace NetChangeFuturesTradeMessageFractionPair

def encode (message : NetChangeFuturesTradeMessageFractionPair) : List UInt8 :=
  Alpha.encode message.rawNetChangeFuturesTradeMessage
    ++ (encodeUInt 1 message.netChangeFractionIndicator)

def decode (bytes : List UInt8) : Option (NetChangeFuturesTradeMessageFractionPair × List UInt8) := do
  let (rawNetChangeFuturesTradeMessage, bytes) ← Alpha.decode 6 bytes
  let (netChangeFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawNetChangeFuturesTradeMessage, netChangeFractionIndicator }, bytes)

@[simp] theorem encode_length (message : NetChangeFuturesTradeMessageFractionPair) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : NetChangeFuturesTradeMessageFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NetChangeFuturesTradeMessageFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end NetChangeFuturesTradeMessageFractionPair

/-- Futures Trade Message: 59 bytes -/
structure FuturesTradeMessage where
  exchangeId : ExchangeId
  rootSymbol : Alpha 6
  deliveryMonth : DeliveryMonth
  deliveryYearFutures : Alpha 2
  deliveryDay : Alpha 2
  volume : Alpha 8
  tradePriceFractionPair : TradePriceFractionPair
  netChangeSign : NetChangeSign
  netChangeFuturesTradeMessageFractionPair : NetChangeFuturesTradeMessageFractionPair
  filler6 : Alpha 6
  timestamp : Alpha 9
  priceIndicatorMarker : FuturesTradeMessagePriceIndicatorMarker
  tradeNumber : Alpha 8
  deriving DecidableEq, Repr

namespace FuturesTradeMessage

def encode (message : FuturesTradeMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (DeliveryMonth.encode message.deliveryMonth
    ++ (Alpha.encode message.deliveryYearFutures
    ++ (Alpha.encode message.deliveryDay
    ++ (Alpha.encode message.volume
    ++ (TradePriceFractionPair.encode message.tradePriceFractionPair
    ++ (NetChangeSign.encode message.netChangeSign
    ++ (NetChangeFuturesTradeMessageFractionPair.encode message.netChangeFuturesTradeMessageFractionPair
    ++ (Alpha.encode message.filler6
    ++ (Alpha.encode message.timestamp
    ++ (FuturesTradeMessagePriceIndicatorMarker.encode message.priceIndicatorMarker
    ++ (Alpha.encode message.tradeNumber))))))))))))

def decode (bytes : List UInt8) : Option (FuturesTradeMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (deliveryMonth, bytes) ← DeliveryMonth.decode bytes
  let (deliveryYearFutures, bytes) ← Alpha.decode 2 bytes
  let (deliveryDay, bytes) ← Alpha.decode 2 bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePriceFractionPair, bytes) ← TradePriceFractionPair.decode bytes
  let (netChangeSign, bytes) ← NetChangeSign.decode bytes
  let (netChangeFuturesTradeMessageFractionPair, bytes) ← NetChangeFuturesTradeMessageFractionPair.decode bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (timestamp, bytes) ← Alpha.decode 9 bytes
  let (priceIndicatorMarker, bytes) ← FuturesTradeMessagePriceIndicatorMarker.decode bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ exchangeId, rootSymbol, deliveryMonth, deliveryYearFutures, deliveryDay, volume, tradePriceFractionPair, netChangeSign, netChangeFuturesTradeMessageFractionPair, filler6, timestamp, priceIndicatorMarker, tradeNumber }, bytes)

@[simp] theorem encode_length (message : FuturesTradeMessage) : (encode message).length = 59 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length, DeliveryMonth.encode_length, TradePriceFractionPair.encode_length, NetChangeSign.encode_length, NetChangeFuturesTradeMessageFractionPair.encode_length, FuturesTradeMessagePriceIndicatorMarker.encode_length]

theorem encode_length_pos (message : FuturesTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FuturesTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DeliveryMonth.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradePriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeFuturesTradeMessageFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FuturesTradeMessagePriceIndicatorMarker.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FuturesTradeMessage

/-- Strategy Trade Message: 79 bytes -/
structure StrategyTradeMessage where
  exchangeId : ExchangeId
  symbol : Alpha 30
  volume : Alpha 8
  tradePriceSign : TradePriceSign
  tradePriceFractionPair : TradePriceFractionPair
  netChangeSign : NetChangeSign
  netChangeFractionPair : NetChangeFractionPair
  filler6 : Alpha 6
  timestamp : Alpha 9
  priceIndicatorMarker : FuturesTradeMessagePriceIndicatorMarker
  tradeNumber : Alpha 8
  deriving DecidableEq, Repr

namespace StrategyTradeMessage

def encode (message : StrategyTradeMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.volume
    ++ (TradePriceSign.encode message.tradePriceSign
    ++ (TradePriceFractionPair.encode message.tradePriceFractionPair
    ++ (NetChangeSign.encode message.netChangeSign
    ++ (NetChangeFractionPair.encode message.netChangeFractionPair
    ++ (Alpha.encode message.filler6
    ++ (Alpha.encode message.timestamp
    ++ (FuturesTradeMessagePriceIndicatorMarker.encode message.priceIndicatorMarker
    ++ (Alpha.encode message.tradeNumber))))))))))

def decode (bytes : List UInt8) : Option (StrategyTradeMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (symbol, bytes) ← Alpha.decode 30 bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePriceSign, bytes) ← TradePriceSign.decode bytes
  let (tradePriceFractionPair, bytes) ← TradePriceFractionPair.decode bytes
  let (netChangeSign, bytes) ← NetChangeSign.decode bytes
  let (netChangeFractionPair, bytes) ← NetChangeFractionPair.decode bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (timestamp, bytes) ← Alpha.decode 9 bytes
  let (priceIndicatorMarker, bytes) ← FuturesTradeMessagePriceIndicatorMarker.decode bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ exchangeId, symbol, volume, tradePriceSign, tradePriceFractionPair, netChangeSign, netChangeFractionPair, filler6, timestamp, priceIndicatorMarker, tradeNumber }, bytes)

@[simp] theorem encode_length (message : StrategyTradeMessage) : (encode message).length = 79 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length, TradePriceSign.encode_length, TradePriceFractionPair.encode_length, NetChangeSign.encode_length, NetChangeFractionPair.encode_length, FuturesTradeMessagePriceIndicatorMarker.encode_length]

theorem encode_length_pos (message : StrategyTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradePriceSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradePriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FuturesTradeMessagePriceIndicatorMarker.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StrategyTradeMessage

/-- Fixed Rate Fraction Pair: 6 bytes -/
structure FixedRateFractionPair where
  rawFixedRate : Alpha 5
  fixedRateFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace FixedRateFractionPair

def encode (message : FixedRateFractionPair) : List UInt8 :=
  Alpha.encode message.rawFixedRate
    ++ (encodeUInt 1 message.fixedRateFractionIndicator)

def decode (bytes : List UInt8) : Option (FixedRateFractionPair × List UInt8) := do
  let (rawFixedRate, bytes) ← Alpha.decode 5 bytes
  let (fixedRateFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawFixedRate, fixedRateFractionIndicator }, bytes)

@[simp] theorem encode_length (message : FixedRateFractionPair) : (encode message).length = 6 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : FixedRateFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FixedRateFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end FixedRateFractionPair

/-- Swap Future Trade Message: 61 bytes -/
structure SwapFutureTradeMessage where
  exchangeId : ExchangeId
  rootSymbolSwapFuture : Alpha 6
  expiryMonthSwapFuture : ExpiryMonthSwapFuture
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  tenor : Alpha 2
  fixedRateFractionPair : FixedRateFractionPair
  tradeVolume : Alpha 8
  tradePriceFractionPair : TradePriceFractionPair
  netChangeSign : NetChangeSign
  netChangeFuturesTradeMessageFractionPair : NetChangeFuturesTradeMessageFractionPair
  timestamp : Alpha 9
  priceIndicatorMarker : FuturesTradeMessagePriceIndicatorMarker
  tradeNumber : Alpha 8
  deriving DecidableEq, Repr

namespace SwapFutureTradeMessage

def encode (message : SwapFutureTradeMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbolSwapFuture
    ++ (ExpiryMonthSwapFuture.encode message.expiryMonthSwapFuture
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay
    ++ (Alpha.encode message.tenor
    ++ (FixedRateFractionPair.encode message.fixedRateFractionPair
    ++ (Alpha.encode message.tradeVolume
    ++ (TradePriceFractionPair.encode message.tradePriceFractionPair
    ++ (NetChangeSign.encode message.netChangeSign
    ++ (NetChangeFuturesTradeMessageFractionPair.encode message.netChangeFuturesTradeMessageFractionPair
    ++ (Alpha.encode message.timestamp
    ++ (FuturesTradeMessagePriceIndicatorMarker.encode message.priceIndicatorMarker
    ++ (Alpha.encode message.tradeNumber)))))))))))))

def decode (bytes : List UInt8) : Option (SwapFutureTradeMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (rootSymbolSwapFuture, bytes) ← Alpha.decode 6 bytes
  let (expiryMonthSwapFuture, bytes) ← ExpiryMonthSwapFuture.decode bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (tenor, bytes) ← Alpha.decode 2 bytes
  let (fixedRateFractionPair, bytes) ← FixedRateFractionPair.decode bytes
  let (tradeVolume, bytes) ← Alpha.decode 8 bytes
  let (tradePriceFractionPair, bytes) ← TradePriceFractionPair.decode bytes
  let (netChangeSign, bytes) ← NetChangeSign.decode bytes
  let (netChangeFuturesTradeMessageFractionPair, bytes) ← NetChangeFuturesTradeMessageFractionPair.decode bytes
  let (timestamp, bytes) ← Alpha.decode 9 bytes
  let (priceIndicatorMarker, bytes) ← FuturesTradeMessagePriceIndicatorMarker.decode bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ exchangeId, rootSymbolSwapFuture, expiryMonthSwapFuture, expiryYear, expiryDay, tenor, fixedRateFractionPair, tradeVolume, tradePriceFractionPair, netChangeSign, netChangeFuturesTradeMessageFractionPair, timestamp, priceIndicatorMarker, tradeNumber }, bytes)

@[simp] theorem encode_length (message : SwapFutureTradeMessage) : (encode message).length = 61 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length, ExpiryMonthSwapFuture.encode_length, FixedRateFractionPair.encode_length, TradePriceFractionPair.encode_length, NetChangeSign.encode_length, NetChangeFuturesTradeMessageFractionPair.encode_length, FuturesTradeMessagePriceIndicatorMarker.encode_length]

theorem encode_length_pos (message : SwapFutureTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SwapFutureTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExpiryMonthSwapFuture.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FixedRateFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradePriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeFuturesTradeMessageFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FuturesTradeMessagePriceIndicatorMarker.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SwapFutureTradeMessage

/-- Option Rfq Message: 30 bytes -/
structure OptionRfqMessage where
  exchangeId : ExchangeId
  rootSymbol : Alpha 6
  expiryMonth : ExpiryMonth
  filler1 : Alpha 1
  strikePriceInstrumentFractionPair : StrikePriceInstrumentFractionPair
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  requestedSize : Alpha 8
  requestedMarketSide : RequestedMarketSide
  deriving DecidableEq, Repr

namespace OptionRfqMessage

def encode (message : OptionRfqMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (ExpiryMonth.encode message.expiryMonth
    ++ (Alpha.encode message.filler1
    ++ (StrikePriceInstrumentFractionPair.encode message.strikePriceInstrumentFractionPair
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay
    ++ (Alpha.encode message.requestedSize
    ++ (RequestedMarketSide.encode message.requestedMarketSide))))))))

def decode (bytes : List UInt8) : Option (OptionRfqMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (expiryMonth, bytes) ← ExpiryMonth.decode bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (strikePriceInstrumentFractionPair, bytes) ← StrikePriceInstrumentFractionPair.decode bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (requestedSize, bytes) ← Alpha.decode 8 bytes
  let (requestedMarketSide, bytes) ← RequestedMarketSide.decode bytes
  pure ({ exchangeId, rootSymbol, expiryMonth, filler1, strikePriceInstrumentFractionPair, expiryYear, expiryDay, requestedSize, requestedMarketSide }, bytes)

@[simp] theorem encode_length (message : OptionRfqMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length, ExpiryMonth.encode_length, StrikePriceInstrumentFractionPair.encode_length, RequestedMarketSide.encode_length]

theorem encode_length_pos (message : OptionRfqMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionRfqMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExpiryMonth.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StrikePriceInstrumentFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [RequestedMarketSide.decode_encode, some_bind]
  rfl

end OptionRfqMessage

/-- Future Options Rfq Message: 30 bytes -/
structure FutureOptionsRfqMessage where
  exchangeId : ExchangeId
  rootSymbol : Alpha 6
  contractMonthCode : ContractMonthCode
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  callPutCode : CallPutCode
  strikePriceInstrumentFractionPair : StrikePriceInstrumentFractionPair
  requestedSize : Alpha 8
  requestedMarketSide : RequestedMarketSide
  deriving DecidableEq, Repr

namespace FutureOptionsRfqMessage

def encode (message : FutureOptionsRfqMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (ContractMonthCode.encode message.contractMonthCode
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay
    ++ (CallPutCode.encode message.callPutCode
    ++ (StrikePriceInstrumentFractionPair.encode message.strikePriceInstrumentFractionPair
    ++ (Alpha.encode message.requestedSize
    ++ (RequestedMarketSide.encode message.requestedMarketSide))))))))

def decode (bytes : List UInt8) : Option (FutureOptionsRfqMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (contractMonthCode, bytes) ← ContractMonthCode.decode bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (callPutCode, bytes) ← CallPutCode.decode bytes
  let (strikePriceInstrumentFractionPair, bytes) ← StrikePriceInstrumentFractionPair.decode bytes
  let (requestedSize, bytes) ← Alpha.decode 8 bytes
  let (requestedMarketSide, bytes) ← RequestedMarketSide.decode bytes
  pure ({ exchangeId, rootSymbol, contractMonthCode, expiryYear, expiryDay, callPutCode, strikePriceInstrumentFractionPair, requestedSize, requestedMarketSide }, bytes)

@[simp] theorem encode_length (message : FutureOptionsRfqMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length, ContractMonthCode.encode_length, CallPutCode.encode_length, StrikePriceInstrumentFractionPair.encode_length, RequestedMarketSide.encode_length]

theorem encode_length_pos (message : FutureOptionsRfqMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FutureOptionsRfqMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ContractMonthCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CallPutCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StrikePriceInstrumentFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [RequestedMarketSide.decode_encode, some_bind]
  rfl

end FutureOptionsRfqMessage

/-- Futures Rfq Message: 21 bytes -/
structure FuturesRfqMessage where
  exchangeId : ExchangeId
  rootSymbol : Alpha 6
  deliveryMonth : DeliveryMonth
  deliveryYearFutures : Alpha 2
  deliveryDay : Alpha 2
  requestedSize : Alpha 8
  requestedMarketSide : RequestedMarketSide
  deriving DecidableEq, Repr

namespace FuturesRfqMessage

def encode (message : FuturesRfqMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (DeliveryMonth.encode message.deliveryMonth
    ++ (Alpha.encode message.deliveryYearFutures
    ++ (Alpha.encode message.deliveryDay
    ++ (Alpha.encode message.requestedSize
    ++ (RequestedMarketSide.encode message.requestedMarketSide))))))

def decode (bytes : List UInt8) : Option (FuturesRfqMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (deliveryMonth, bytes) ← DeliveryMonth.decode bytes
  let (deliveryYearFutures, bytes) ← Alpha.decode 2 bytes
  let (deliveryDay, bytes) ← Alpha.decode 2 bytes
  let (requestedSize, bytes) ← Alpha.decode 8 bytes
  let (requestedMarketSide, bytes) ← RequestedMarketSide.decode bytes
  pure ({ exchangeId, rootSymbol, deliveryMonth, deliveryYearFutures, deliveryDay, requestedSize, requestedMarketSide }, bytes)

@[simp] theorem encode_length (message : FuturesRfqMessage) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length, DeliveryMonth.encode_length, RequestedMarketSide.encode_length]

theorem encode_length_pos (message : FuturesRfqMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FuturesRfqMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DeliveryMonth.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [RequestedMarketSide.decode_encode, some_bind]
  rfl

end FuturesRfqMessage

/-- Strategy Rfq Message: 40 bytes -/
structure StrategyRfqMessage where
  exchangeId : ExchangeId
  symbol : Alpha 30
  requestedSize : Alpha 8
  requestedMarketSide : RequestedMarketSide
  deriving DecidableEq, Repr

namespace StrategyRfqMessage

def encode (message : StrategyRfqMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.requestedSize
    ++ (RequestedMarketSide.encode message.requestedMarketSide)))

def decode (bytes : List UInt8) : Option (StrategyRfqMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (symbol, bytes) ← Alpha.decode 30 bytes
  let (requestedSize, bytes) ← Alpha.decode 8 bytes
  let (requestedMarketSide, bytes) ← RequestedMarketSide.decode bytes
  pure ({ exchangeId, symbol, requestedSize, requestedMarketSide }, bytes)

@[simp] theorem encode_length (message : StrategyRfqMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length, RequestedMarketSide.encode_length]

theorem encode_length_pos (message : StrategyRfqMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyRfqMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [RequestedMarketSide.decode_encode, some_bind]
  rfl

end StrategyRfqMessage

/-- Swap Future Rfq Message: 29 bytes -/
structure SwapFutureRfqMessage where
  exchangeId : ExchangeId
  rootSymbolSwapFuture : Alpha 6
  expiryMonthSwapFuture : ExpiryMonthSwapFuture
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  tenor : Alpha 2
  fixedRateFractionPair : FixedRateFractionPair
  requestedSize : Alpha 8
  requestedMarketSide : RequestedMarketSide
  deriving DecidableEq, Repr

namespace SwapFutureRfqMessage

def encode (message : SwapFutureRfqMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbolSwapFuture
    ++ (ExpiryMonthSwapFuture.encode message.expiryMonthSwapFuture
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay
    ++ (Alpha.encode message.tenor
    ++ (FixedRateFractionPair.encode message.fixedRateFractionPair
    ++ (Alpha.encode message.requestedSize
    ++ (RequestedMarketSide.encode message.requestedMarketSide))))))))

def decode (bytes : List UInt8) : Option (SwapFutureRfqMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (rootSymbolSwapFuture, bytes) ← Alpha.decode 6 bytes
  let (expiryMonthSwapFuture, bytes) ← ExpiryMonthSwapFuture.decode bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (tenor, bytes) ← Alpha.decode 2 bytes
  let (fixedRateFractionPair, bytes) ← FixedRateFractionPair.decode bytes
  let (requestedSize, bytes) ← Alpha.decode 8 bytes
  let (requestedMarketSide, bytes) ← RequestedMarketSide.decode bytes
  pure ({ exchangeId, rootSymbolSwapFuture, expiryMonthSwapFuture, expiryYear, expiryDay, tenor, fixedRateFractionPair, requestedSize, requestedMarketSide }, bytes)

@[simp] theorem encode_length (message : SwapFutureRfqMessage) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length, ExpiryMonthSwapFuture.encode_length, FixedRateFractionPair.encode_length, RequestedMarketSide.encode_length]

theorem encode_length_pos (message : SwapFutureRfqMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SwapFutureRfqMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExpiryMonthSwapFuture.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FixedRateFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [RequestedMarketSide.decode_encode, some_bind]
  rfl

end SwapFutureRfqMessage

/-- Strike Price Schedule Notice Fraction Pair: 8 bytes -/
structure StrikePriceScheduleNoticeFractionPair where
  rawStrikePriceScheduleNotice : Alpha 7
  strikePriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace StrikePriceScheduleNoticeFractionPair

def encode (message : StrikePriceScheduleNoticeFractionPair) : List UInt8 :=
  Alpha.encode message.rawStrikePriceScheduleNotice
    ++ (encodeUInt 1 message.strikePriceFractionIndicator)

def decode (bytes : List UInt8) : Option (StrikePriceScheduleNoticeFractionPair × List UInt8) := do
  let (rawStrikePriceScheduleNotice, bytes) ← Alpha.decode 7 bytes
  let (strikePriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawStrikePriceScheduleNotice, strikePriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : StrikePriceScheduleNoticeFractionPair) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : StrikePriceScheduleNoticeFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrikePriceScheduleNoticeFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end StrikePriceScheduleNoticeFractionPair

/-- Instrument Schedule Notice Option Message: 28 bytes -/
structure InstrumentScheduleNoticeOptionMessage where
  exchangeId : ExchangeId
  rootSymbol : Alpha 6
  expiryMonth : ExpiryMonth
  filler1 : Alpha 1
  strikePriceScheduleNoticeFractionPair : StrikePriceScheduleNoticeFractionPair
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  seriesStatus : SeriesStatus
  scheduledStatusChangeTime : Alpha 6
  deriving DecidableEq, Repr

namespace InstrumentScheduleNoticeOptionMessage

def encode (message : InstrumentScheduleNoticeOptionMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (ExpiryMonth.encode message.expiryMonth
    ++ (Alpha.encode message.filler1
    ++ (StrikePriceScheduleNoticeFractionPair.encode message.strikePriceScheduleNoticeFractionPair
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay
    ++ (SeriesStatus.encode message.seriesStatus
    ++ (Alpha.encode message.scheduledStatusChangeTime))))))))

def decode (bytes : List UInt8) : Option (InstrumentScheduleNoticeOptionMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (expiryMonth, bytes) ← ExpiryMonth.decode bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (strikePriceScheduleNoticeFractionPair, bytes) ← StrikePriceScheduleNoticeFractionPair.decode bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (seriesStatus, bytes) ← SeriesStatus.decode bytes
  let (scheduledStatusChangeTime, bytes) ← Alpha.decode 6 bytes
  pure ({ exchangeId, rootSymbol, expiryMonth, filler1, strikePriceScheduleNoticeFractionPair, expiryYear, expiryDay, seriesStatus, scheduledStatusChangeTime }, bytes)

@[simp] theorem encode_length (message : InstrumentScheduleNoticeOptionMessage) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length, ExpiryMonth.encode_length, StrikePriceScheduleNoticeFractionPair.encode_length, SeriesStatus.encode_length]

theorem encode_length_pos (message : InstrumentScheduleNoticeOptionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentScheduleNoticeOptionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExpiryMonth.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StrikePriceScheduleNoticeFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SeriesStatus.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end InstrumentScheduleNoticeOptionMessage

/-- Instrument Schedule Notice Futures Option Message: 28 bytes -/
structure InstrumentScheduleNoticeFuturesOptionMessage where
  exchangeId : ExchangeId
  rootSymbol : Alpha 6
  contractMonthCode : ContractMonthCode
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  callPutCode : CallPutCode
  strikePriceInstrumentFractionPair : StrikePriceInstrumentFractionPair
  seriesStatus : SeriesStatus
  scheduledStatusChangeTime : Alpha 6
  deriving DecidableEq, Repr

namespace InstrumentScheduleNoticeFuturesOptionMessage

def encode (message : InstrumentScheduleNoticeFuturesOptionMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (ContractMonthCode.encode message.contractMonthCode
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay
    ++ (CallPutCode.encode message.callPutCode
    ++ (StrikePriceInstrumentFractionPair.encode message.strikePriceInstrumentFractionPair
    ++ (SeriesStatus.encode message.seriesStatus
    ++ (Alpha.encode message.scheduledStatusChangeTime))))))))

def decode (bytes : List UInt8) : Option (InstrumentScheduleNoticeFuturesOptionMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (contractMonthCode, bytes) ← ContractMonthCode.decode bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (callPutCode, bytes) ← CallPutCode.decode bytes
  let (strikePriceInstrumentFractionPair, bytes) ← StrikePriceInstrumentFractionPair.decode bytes
  let (seriesStatus, bytes) ← SeriesStatus.decode bytes
  let (scheduledStatusChangeTime, bytes) ← Alpha.decode 6 bytes
  pure ({ exchangeId, rootSymbol, contractMonthCode, expiryYear, expiryDay, callPutCode, strikePriceInstrumentFractionPair, seriesStatus, scheduledStatusChangeTime }, bytes)

@[simp] theorem encode_length (message : InstrumentScheduleNoticeFuturesOptionMessage) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length, ContractMonthCode.encode_length, CallPutCode.encode_length, StrikePriceInstrumentFractionPair.encode_length, SeriesStatus.encode_length]

theorem encode_length_pos (message : InstrumentScheduleNoticeFuturesOptionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentScheduleNoticeFuturesOptionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ContractMonthCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CallPutCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StrikePriceInstrumentFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SeriesStatus.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end InstrumentScheduleNoticeFuturesOptionMessage

/-- Instrument Schedule Notice Future Message: 19 bytes -/
structure InstrumentScheduleNoticeFutureMessage where
  exchangeId : ExchangeId
  rootSymbol : Alpha 6
  deliveryMonth : DeliveryMonth
  deliveryYearFutures : Alpha 2
  deliveryDay : Alpha 2
  seriesStatus : SeriesStatus
  scheduledStatusChangeTime : Alpha 6
  deriving DecidableEq, Repr

namespace InstrumentScheduleNoticeFutureMessage

def encode (message : InstrumentScheduleNoticeFutureMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (DeliveryMonth.encode message.deliveryMonth
    ++ (Alpha.encode message.deliveryYearFutures
    ++ (Alpha.encode message.deliveryDay
    ++ (SeriesStatus.encode message.seriesStatus
    ++ (Alpha.encode message.scheduledStatusChangeTime))))))

def decode (bytes : List UInt8) : Option (InstrumentScheduleNoticeFutureMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (deliveryMonth, bytes) ← DeliveryMonth.decode bytes
  let (deliveryYearFutures, bytes) ← Alpha.decode 2 bytes
  let (deliveryDay, bytes) ← Alpha.decode 2 bytes
  let (seriesStatus, bytes) ← SeriesStatus.decode bytes
  let (scheduledStatusChangeTime, bytes) ← Alpha.decode 6 bytes
  pure ({ exchangeId, rootSymbol, deliveryMonth, deliveryYearFutures, deliveryDay, seriesStatus, scheduledStatusChangeTime }, bytes)

@[simp] theorem encode_length (message : InstrumentScheduleNoticeFutureMessage) : (encode message).length = 19 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length, DeliveryMonth.encode_length, SeriesStatus.encode_length]

theorem encode_length_pos (message : InstrumentScheduleNoticeFutureMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentScheduleNoticeFutureMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DeliveryMonth.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SeriesStatus.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end InstrumentScheduleNoticeFutureMessage

/-- Instrument Schedule Notice Strategy Message: 38 bytes -/
structure InstrumentScheduleNoticeStrategyMessage where
  exchangeId : ExchangeId
  strategySymbol : Alpha 30
  seriesStatus : SeriesStatus
  scheduledStatusChangeTime : Alpha 6
  deriving DecidableEq, Repr

namespace InstrumentScheduleNoticeStrategyMessage

def encode (message : InstrumentScheduleNoticeStrategyMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.strategySymbol
    ++ (SeriesStatus.encode message.seriesStatus
    ++ (Alpha.encode message.scheduledStatusChangeTime)))

def decode (bytes : List UInt8) : Option (InstrumentScheduleNoticeStrategyMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (strategySymbol, bytes) ← Alpha.decode 30 bytes
  let (seriesStatus, bytes) ← SeriesStatus.decode bytes
  let (scheduledStatusChangeTime, bytes) ← Alpha.decode 6 bytes
  pure ({ exchangeId, strategySymbol, seriesStatus, scheduledStatusChangeTime }, bytes)

@[simp] theorem encode_length (message : InstrumentScheduleNoticeStrategyMessage) : (encode message).length = 38 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length, SeriesStatus.encode_length]

theorem encode_length_pos (message : InstrumentScheduleNoticeStrategyMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentScheduleNoticeStrategyMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SeriesStatus.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end InstrumentScheduleNoticeStrategyMessage

/-- Instrument Schedule Notice Swap Future Message: 27 bytes -/
structure InstrumentScheduleNoticeSwapFutureMessage where
  exchangeId : ExchangeId
  rootSymbol : Alpha 6
  expiryMonthSwapFuture : ExpiryMonthSwapFuture
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  tenor : Alpha 2
  fixedRateFractionPair : FixedRateFractionPair
  seriesStatus : SeriesStatus
  scheduledStatusChangeTime : Alpha 6
  deriving DecidableEq, Repr

namespace InstrumentScheduleNoticeSwapFutureMessage

def encode (message : InstrumentScheduleNoticeSwapFutureMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (ExpiryMonthSwapFuture.encode message.expiryMonthSwapFuture
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay
    ++ (Alpha.encode message.tenor
    ++ (FixedRateFractionPair.encode message.fixedRateFractionPair
    ++ (SeriesStatus.encode message.seriesStatus
    ++ (Alpha.encode message.scheduledStatusChangeTime))))))))

def decode (bytes : List UInt8) : Option (InstrumentScheduleNoticeSwapFutureMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (expiryMonthSwapFuture, bytes) ← ExpiryMonthSwapFuture.decode bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (tenor, bytes) ← Alpha.decode 2 bytes
  let (fixedRateFractionPair, bytes) ← FixedRateFractionPair.decode bytes
  let (seriesStatus, bytes) ← SeriesStatus.decode bytes
  let (scheduledStatusChangeTime, bytes) ← Alpha.decode 6 bytes
  pure ({ exchangeId, rootSymbol, expiryMonthSwapFuture, expiryYear, expiryDay, tenor, fixedRateFractionPair, seriesStatus, scheduledStatusChangeTime }, bytes)

@[simp] theorem encode_length (message : InstrumentScheduleNoticeSwapFutureMessage) : (encode message).length = 27 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length, ExpiryMonthSwapFuture.encode_length, FixedRateFractionPair.encode_length, SeriesStatus.encode_length]

theorem encode_length_pos (message : InstrumentScheduleNoticeSwapFutureMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentScheduleNoticeSwapFutureMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExpiryMonthSwapFuture.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FixedRateFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SeriesStatus.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end InstrumentScheduleNoticeSwapFutureMessage

/-- Bid Price Quote: 7 bytes -/
structure BidPriceQuote where
  rawBidPriceQuoteNumeric : Alpha 6
  bidPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace BidPriceQuote

def encode (message : BidPriceQuote) : List UInt8 :=
  Alpha.encode message.rawBidPriceQuoteNumeric
    ++ (encodeUInt 1 message.bidPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (BidPriceQuote × List UInt8) := do
  let (rawBidPriceQuoteNumeric, bytes) ← Alpha.decode 6 bytes
  let (bidPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawBidPriceQuoteNumeric, bidPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : BidPriceQuote) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : BidPriceQuote) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BidPriceQuote) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end BidPriceQuote

/-- Ask Price Quote: 7 bytes -/
structure AskPriceQuote where
  rawAskPriceQuoteNumeric : Alpha 6
  askPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace AskPriceQuote

def encode (message : AskPriceQuote) : List UInt8 :=
  Alpha.encode message.rawAskPriceQuoteNumeric
    ++ (encodeUInt 1 message.askPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (AskPriceQuote × List UInt8) := do
  let (rawAskPriceQuoteNumeric, bytes) ← Alpha.decode 6 bytes
  let (askPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawAskPriceQuoteNumeric, askPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : AskPriceQuote) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : AskPriceQuote) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AskPriceQuote) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end AskPriceQuote

/-- Option Quote Message: 47 bytes -/
structure OptionQuoteMessage where
  exchangeId : ExchangeId
  rootSymbol : Alpha 6
  expiryMonth : ExpiryMonth
  filler1 : Alpha 1
  strikePriceInstrumentFractionPair : StrikePriceInstrumentFractionPair
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  bidPriceQuote : BidPriceQuote
  bidSize : Alpha 5
  askPriceQuote : AskPriceQuote
  askSize : Alpha 5
  secondFiller1 : Alpha 1
  instrumentStatusMarker : InstrumentStatusMarker
  deriving DecidableEq, Repr

namespace OptionQuoteMessage

def encode (message : OptionQuoteMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (ExpiryMonth.encode message.expiryMonth
    ++ (Alpha.encode message.filler1
    ++ (StrikePriceInstrumentFractionPair.encode message.strikePriceInstrumentFractionPair
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay
    ++ (BidPriceQuote.encode message.bidPriceQuote
    ++ (Alpha.encode message.bidSize
    ++ (AskPriceQuote.encode message.askPriceQuote
    ++ (Alpha.encode message.askSize
    ++ (Alpha.encode message.secondFiller1
    ++ (InstrumentStatusMarker.encode message.instrumentStatusMarker))))))))))))

def decode (bytes : List UInt8) : Option (OptionQuoteMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (expiryMonth, bytes) ← ExpiryMonth.decode bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (strikePriceInstrumentFractionPair, bytes) ← StrikePriceInstrumentFractionPair.decode bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (bidPriceQuote, bytes) ← BidPriceQuote.decode bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPriceQuote, bytes) ← AskPriceQuote.decode bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (secondFiller1, bytes) ← Alpha.decode 1 bytes
  let (instrumentStatusMarker, bytes) ← InstrumentStatusMarker.decode bytes
  pure ({ exchangeId, rootSymbol, expiryMonth, filler1, strikePriceInstrumentFractionPair, expiryYear, expiryDay, bidPriceQuote, bidSize, askPriceQuote, askSize, secondFiller1, instrumentStatusMarker }, bytes)

@[simp] theorem encode_length (message : OptionQuoteMessage) : (encode message).length = 47 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length, ExpiryMonth.encode_length, StrikePriceInstrumentFractionPair.encode_length, BidPriceQuote.encode_length, AskPriceQuote.encode_length, InstrumentStatusMarker.encode_length]

theorem encode_length_pos (message : OptionQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExpiryMonth.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StrikePriceInstrumentFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BidPriceQuote.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskPriceQuote.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [InstrumentStatusMarker.decode_encode, some_bind]
  rfl

end OptionQuoteMessage

/-- Future Options Quote Message: 47 bytes -/
structure FutureOptionsQuoteMessage where
  exchangeId : ExchangeId
  rootSymbol : Alpha 6
  contractMonthCode : ContractMonthCode
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  callPutCode : CallPutCode
  strikePriceInstrumentFractionPair : StrikePriceInstrumentFractionPair
  bidPriceQuote : BidPriceQuote
  bidSize : Alpha 5
  askPriceQuote : AskPriceQuote
  askSize : Alpha 5
  instrumentStatusMarker : InstrumentStatusMarker
  filler1 : Alpha 1
  deriving DecidableEq, Repr

namespace FutureOptionsQuoteMessage

def encode (message : FutureOptionsQuoteMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (ContractMonthCode.encode message.contractMonthCode
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay
    ++ (CallPutCode.encode message.callPutCode
    ++ (StrikePriceInstrumentFractionPair.encode message.strikePriceInstrumentFractionPair
    ++ (BidPriceQuote.encode message.bidPriceQuote
    ++ (Alpha.encode message.bidSize
    ++ (AskPriceQuote.encode message.askPriceQuote
    ++ (Alpha.encode message.askSize
    ++ (InstrumentStatusMarker.encode message.instrumentStatusMarker
    ++ (Alpha.encode message.filler1))))))))))))

def decode (bytes : List UInt8) : Option (FutureOptionsQuoteMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (contractMonthCode, bytes) ← ContractMonthCode.decode bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (callPutCode, bytes) ← CallPutCode.decode bytes
  let (strikePriceInstrumentFractionPair, bytes) ← StrikePriceInstrumentFractionPair.decode bytes
  let (bidPriceQuote, bytes) ← BidPriceQuote.decode bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPriceQuote, bytes) ← AskPriceQuote.decode bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (instrumentStatusMarker, bytes) ← InstrumentStatusMarker.decode bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  pure ({ exchangeId, rootSymbol, contractMonthCode, expiryYear, expiryDay, callPutCode, strikePriceInstrumentFractionPair, bidPriceQuote, bidSize, askPriceQuote, askSize, instrumentStatusMarker, filler1 }, bytes)

@[simp] theorem encode_length (message : FutureOptionsQuoteMessage) : (encode message).length = 47 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length, ContractMonthCode.encode_length, CallPutCode.encode_length, StrikePriceInstrumentFractionPair.encode_length, BidPriceQuote.encode_length, AskPriceQuote.encode_length, InstrumentStatusMarker.encode_length]

theorem encode_length_pos (message : FutureOptionsQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FutureOptionsQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ContractMonthCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CallPutCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StrikePriceInstrumentFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BidPriceQuote.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskPriceQuote.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentStatusMarker.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FutureOptionsQuoteMessage

/-- Bid Price Quote Futures Quote Message: 7 bytes -/
structure BidPriceQuoteFuturesQuoteMessage where
  rawBidPriceQuoteNumericBidPriceQuoteFuturesQuoteMessageNumericPair : Alpha 6
  bidPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace BidPriceQuoteFuturesQuoteMessage

def encode (message : BidPriceQuoteFuturesQuoteMessage) : List UInt8 :=
  Alpha.encode message.rawBidPriceQuoteNumericBidPriceQuoteFuturesQuoteMessageNumericPair
    ++ (encodeUInt 1 message.bidPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (BidPriceQuoteFuturesQuoteMessage × List UInt8) := do
  let (rawBidPriceQuoteNumericBidPriceQuoteFuturesQuoteMessageNumericPair, bytes) ← Alpha.decode 6 bytes
  let (bidPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawBidPriceQuoteNumericBidPriceQuoteFuturesQuoteMessageNumericPair, bidPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : BidPriceQuoteFuturesQuoteMessage) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : BidPriceQuoteFuturesQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BidPriceQuoteFuturesQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end BidPriceQuoteFuturesQuoteMessage

/-- Ask Price Quote Futures Quote Message: 7 bytes -/
structure AskPriceQuoteFuturesQuoteMessage where
  rawAskPriceQuoteNumericAskPriceQuoteFuturesQuoteMessageNumericPair : Alpha 6
  askPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace AskPriceQuoteFuturesQuoteMessage

def encode (message : AskPriceQuoteFuturesQuoteMessage) : List UInt8 :=
  Alpha.encode message.rawAskPriceQuoteNumericAskPriceQuoteFuturesQuoteMessageNumericPair
    ++ (encodeUInt 1 message.askPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (AskPriceQuoteFuturesQuoteMessage × List UInt8) := do
  let (rawAskPriceQuoteNumericAskPriceQuoteFuturesQuoteMessageNumericPair, bytes) ← Alpha.decode 6 bytes
  let (askPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawAskPriceQuoteNumericAskPriceQuoteFuturesQuoteMessageNumericPair, askPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : AskPriceQuoteFuturesQuoteMessage) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : AskPriceQuoteFuturesQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AskPriceQuoteFuturesQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end AskPriceQuoteFuturesQuoteMessage

/-- Futures Quote Message: 37 bytes -/
structure FuturesQuoteMessage where
  exchangeId : ExchangeId
  rootSymbol : Alpha 6
  deliveryMonth : DeliveryMonth
  deliveryYearFutures : Alpha 2
  deliveryDay : Alpha 2
  bidPriceQuoteFuturesQuoteMessage : BidPriceQuoteFuturesQuoteMessage
  bidSize : Alpha 5
  askPriceQuoteFuturesQuoteMessage : AskPriceQuoteFuturesQuoteMessage
  askSize : Alpha 5
  instrumentStatusMarker : InstrumentStatusMarker
  deriving DecidableEq, Repr

namespace FuturesQuoteMessage

def encode (message : FuturesQuoteMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (DeliveryMonth.encode message.deliveryMonth
    ++ (Alpha.encode message.deliveryYearFutures
    ++ (Alpha.encode message.deliveryDay
    ++ (BidPriceQuoteFuturesQuoteMessage.encode message.bidPriceQuoteFuturesQuoteMessage
    ++ (Alpha.encode message.bidSize
    ++ (AskPriceQuoteFuturesQuoteMessage.encode message.askPriceQuoteFuturesQuoteMessage
    ++ (Alpha.encode message.askSize
    ++ (InstrumentStatusMarker.encode message.instrumentStatusMarker)))))))))

def decode (bytes : List UInt8) : Option (FuturesQuoteMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (deliveryMonth, bytes) ← DeliveryMonth.decode bytes
  let (deliveryYearFutures, bytes) ← Alpha.decode 2 bytes
  let (deliveryDay, bytes) ← Alpha.decode 2 bytes
  let (bidPriceQuoteFuturesQuoteMessage, bytes) ← BidPriceQuoteFuturesQuoteMessage.decode bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPriceQuoteFuturesQuoteMessage, bytes) ← AskPriceQuoteFuturesQuoteMessage.decode bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (instrumentStatusMarker, bytes) ← InstrumentStatusMarker.decode bytes
  pure ({ exchangeId, rootSymbol, deliveryMonth, deliveryYearFutures, deliveryDay, bidPriceQuoteFuturesQuoteMessage, bidSize, askPriceQuoteFuturesQuoteMessage, askSize, instrumentStatusMarker }, bytes)

@[simp] theorem encode_length (message : FuturesQuoteMessage) : (encode message).length = 37 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length, DeliveryMonth.encode_length, BidPriceQuoteFuturesQuoteMessage.encode_length, AskPriceQuoteFuturesQuoteMessage.encode_length, InstrumentStatusMarker.encode_length]

theorem encode_length_pos (message : FuturesQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FuturesQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DeliveryMonth.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BidPriceQuoteFuturesQuoteMessage.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskPriceQuoteFuturesQuoteMessage.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [InstrumentStatusMarker.decode_encode, some_bind]
  rfl

end FuturesQuoteMessage

/-- Bid Price Quote Strategy Quote Message: 7 bytes -/
structure BidPriceQuoteStrategyQuoteMessage where
  rawBidPriceQuoteNumericBidPriceQuoteStrategyQuoteMessageNumericPair : Alpha 6
  bidPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace BidPriceQuoteStrategyQuoteMessage

def encode (message : BidPriceQuoteStrategyQuoteMessage) : List UInt8 :=
  Alpha.encode message.rawBidPriceQuoteNumericBidPriceQuoteStrategyQuoteMessageNumericPair
    ++ (encodeUInt 1 message.bidPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (BidPriceQuoteStrategyQuoteMessage × List UInt8) := do
  let (rawBidPriceQuoteNumericBidPriceQuoteStrategyQuoteMessageNumericPair, bytes) ← Alpha.decode 6 bytes
  let (bidPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawBidPriceQuoteNumericBidPriceQuoteStrategyQuoteMessageNumericPair, bidPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : BidPriceQuoteStrategyQuoteMessage) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : BidPriceQuoteStrategyQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BidPriceQuoteStrategyQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end BidPriceQuoteStrategyQuoteMessage

/-- Ask Price Quote Strategy Quote Message: 7 bytes -/
structure AskPriceQuoteStrategyQuoteMessage where
  rawAskPriceQuoteNumericAskPriceQuoteStrategyQuoteMessageNumericPair : Alpha 6
  askPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace AskPriceQuoteStrategyQuoteMessage

def encode (message : AskPriceQuoteStrategyQuoteMessage) : List UInt8 :=
  Alpha.encode message.rawAskPriceQuoteNumericAskPriceQuoteStrategyQuoteMessageNumericPair
    ++ (encodeUInt 1 message.askPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (AskPriceQuoteStrategyQuoteMessage × List UInt8) := do
  let (rawAskPriceQuoteNumericAskPriceQuoteStrategyQuoteMessageNumericPair, bytes) ← Alpha.decode 6 bytes
  let (askPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawAskPriceQuoteNumericAskPriceQuoteStrategyQuoteMessageNumericPair, askPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : AskPriceQuoteStrategyQuoteMessage) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : AskPriceQuoteStrategyQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AskPriceQuoteStrategyQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end AskPriceQuoteStrategyQuoteMessage

/-- Strategy Quote Message: 58 bytes -/
structure StrategyQuoteMessage where
  exchangeId : ExchangeId
  symbol : Alpha 30
  bidPriceSign : BidPriceSign
  bidPriceQuoteStrategyQuoteMessage : BidPriceQuoteStrategyQuoteMessage
  bidSize : Alpha 5
  askPriceSign : AskPriceSign
  askPriceQuoteStrategyQuoteMessage : AskPriceQuoteStrategyQuoteMessage
  askSize : Alpha 5
  instrumentStatusMarker : StrategyQuoteMessageInstrumentStatusMarker
  deriving DecidableEq, Repr

namespace StrategyQuoteMessage

def encode (message : StrategyQuoteMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.symbol
    ++ (BidPriceSign.encode message.bidPriceSign
    ++ (BidPriceQuoteStrategyQuoteMessage.encode message.bidPriceQuoteStrategyQuoteMessage
    ++ (Alpha.encode message.bidSize
    ++ (AskPriceSign.encode message.askPriceSign
    ++ (AskPriceQuoteStrategyQuoteMessage.encode message.askPriceQuoteStrategyQuoteMessage
    ++ (Alpha.encode message.askSize
    ++ (StrategyQuoteMessageInstrumentStatusMarker.encode message.instrumentStatusMarker))))))))

def decode (bytes : List UInt8) : Option (StrategyQuoteMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (symbol, bytes) ← Alpha.decode 30 bytes
  let (bidPriceSign, bytes) ← BidPriceSign.decode bytes
  let (bidPriceQuoteStrategyQuoteMessage, bytes) ← BidPriceQuoteStrategyQuoteMessage.decode bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPriceSign, bytes) ← AskPriceSign.decode bytes
  let (askPriceQuoteStrategyQuoteMessage, bytes) ← AskPriceQuoteStrategyQuoteMessage.decode bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (instrumentStatusMarker, bytes) ← StrategyQuoteMessageInstrumentStatusMarker.decode bytes
  pure ({ exchangeId, symbol, bidPriceSign, bidPriceQuoteStrategyQuoteMessage, bidSize, askPriceSign, askPriceQuoteStrategyQuoteMessage, askSize, instrumentStatusMarker }, bytes)

@[simp] theorem encode_length (message : StrategyQuoteMessage) : (encode message).length = 58 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length, BidPriceSign.encode_length, BidPriceQuoteStrategyQuoteMessage.encode_length, AskPriceSign.encode_length, AskPriceQuoteStrategyQuoteMessage.encode_length, StrategyQuoteMessageInstrumentStatusMarker.encode_length]

theorem encode_length_pos (message : StrategyQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BidPriceSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BidPriceQuoteStrategyQuoteMessage.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskPriceSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskPriceQuoteStrategyQuoteMessage.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [StrategyQuoteMessageInstrumentStatusMarker.decode_encode, some_bind]
  rfl

end StrategyQuoteMessage

/-- Swap Future Quote Message: 45 bytes -/
structure SwapFutureQuoteMessage where
  exchangeId : ExchangeId
  rootSymbolSwapFuture : Alpha 6
  expiryMonthSwapFuture : ExpiryMonthSwapFuture
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  tenor : Alpha 2
  fixedRateFractionPair : FixedRateFractionPair
  bidPriceQuoteFuturesQuoteMessage : BidPriceQuoteFuturesQuoteMessage
  bidSize : Alpha 5
  askPriceQuoteStrategyQuoteMessage : AskPriceQuoteStrategyQuoteMessage
  askSize : Alpha 5
  instrumentStatusMarker : StrategyQuoteMessageInstrumentStatusMarker
  deriving DecidableEq, Repr

namespace SwapFutureQuoteMessage

def encode (message : SwapFutureQuoteMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbolSwapFuture
    ++ (ExpiryMonthSwapFuture.encode message.expiryMonthSwapFuture
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay
    ++ (Alpha.encode message.tenor
    ++ (FixedRateFractionPair.encode message.fixedRateFractionPair
    ++ (BidPriceQuoteFuturesQuoteMessage.encode message.bidPriceQuoteFuturesQuoteMessage
    ++ (Alpha.encode message.bidSize
    ++ (AskPriceQuoteStrategyQuoteMessage.encode message.askPriceQuoteStrategyQuoteMessage
    ++ (Alpha.encode message.askSize
    ++ (StrategyQuoteMessageInstrumentStatusMarker.encode message.instrumentStatusMarker)))))))))))

def decode (bytes : List UInt8) : Option (SwapFutureQuoteMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (rootSymbolSwapFuture, bytes) ← Alpha.decode 6 bytes
  let (expiryMonthSwapFuture, bytes) ← ExpiryMonthSwapFuture.decode bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (tenor, bytes) ← Alpha.decode 2 bytes
  let (fixedRateFractionPair, bytes) ← FixedRateFractionPair.decode bytes
  let (bidPriceQuoteFuturesQuoteMessage, bytes) ← BidPriceQuoteFuturesQuoteMessage.decode bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPriceQuoteStrategyQuoteMessage, bytes) ← AskPriceQuoteStrategyQuoteMessage.decode bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (instrumentStatusMarker, bytes) ← StrategyQuoteMessageInstrumentStatusMarker.decode bytes
  pure ({ exchangeId, rootSymbolSwapFuture, expiryMonthSwapFuture, expiryYear, expiryDay, tenor, fixedRateFractionPair, bidPriceQuoteFuturesQuoteMessage, bidSize, askPriceQuoteStrategyQuoteMessage, askSize, instrumentStatusMarker }, bytes)

@[simp] theorem encode_length (message : SwapFutureQuoteMessage) : (encode message).length = 45 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length, ExpiryMonthSwapFuture.encode_length, FixedRateFractionPair.encode_length, BidPriceQuoteFuturesQuoteMessage.encode_length, AskPriceQuoteStrategyQuoteMessage.encode_length, StrategyQuoteMessageInstrumentStatusMarker.encode_length]

theorem encode_length_pos (message : SwapFutureQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SwapFutureQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExpiryMonthSwapFuture.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FixedRateFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BidPriceQuoteFuturesQuoteMessage.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskPriceQuoteStrategyQuoteMessage.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [StrategyQuoteMessageInstrumentStatusMarker.decode_encode, some_bind]
  rfl

end SwapFutureQuoteMessage

/-- Option Market Depth Trading Instrument: 29 bytes -/
structure OptionMarketDepthTradingInstrument where
  levelOfMarketDepth : LevelOfMarketDepth
  bidPriceQuote : BidPriceQuote
  bidSize : Alpha 5
  numberOfBidOrders : Alpha 2
  askPriceQuote : AskPriceQuote
  askSize : Alpha 5
  numberOfAskOrders : Alpha 2
  deriving DecidableEq, Repr

namespace OptionMarketDepthTradingInstrument

def encode (message : OptionMarketDepthTradingInstrument) : List UInt8 :=
  LevelOfMarketDepth.encode message.levelOfMarketDepth
    ++ (BidPriceQuote.encode message.bidPriceQuote
    ++ (Alpha.encode message.bidSize
    ++ (Alpha.encode message.numberOfBidOrders
    ++ (AskPriceQuote.encode message.askPriceQuote
    ++ (Alpha.encode message.askSize
    ++ (Alpha.encode message.numberOfAskOrders))))))

def decode (bytes : List UInt8) : Option (OptionMarketDepthTradingInstrument × List UInt8) := do
  let (levelOfMarketDepth, bytes) ← LevelOfMarketDepth.decode bytes
  let (bidPriceQuote, bytes) ← BidPriceQuote.decode bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (numberOfBidOrders, bytes) ← Alpha.decode 2 bytes
  let (askPriceQuote, bytes) ← AskPriceQuote.decode bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (numberOfAskOrders, bytes) ← Alpha.decode 2 bytes
  pure ({ levelOfMarketDepth, bidPriceQuote, bidSize, numberOfBidOrders, askPriceQuote, askSize, numberOfAskOrders }, bytes)

@[simp] theorem encode_length (message : OptionMarketDepthTradingInstrument) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, LevelOfMarketDepth.encode_length, BidPriceQuote.encode_length, Alpha.encode_length, AskPriceQuote.encode_length]

theorem encode_length_pos (message : OptionMarketDepthTradingInstrument) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionMarketDepthTradingInstrument) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LevelOfMarketDepth.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BidPriceQuote.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskPriceQuote.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OptionMarketDepthTradingInstrument

/-- Option Market Depth Message -/
structure OptionMarketDepthMessage where
  exchangeId : ExchangeId
  rootSymbol : Alpha 6
  expiryMonth : ExpiryMonth
  filler1 : Alpha 1
  strikePriceInstrumentFractionPair : StrikePriceInstrumentFractionPair
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  instrumentStatusMarker : InstrumentStatusMarker
  optionMarketDepthTradingInstrument : Digited 1 OptionMarketDepthTradingInstrument
  deriving DecidableEq, Repr

namespace OptionMarketDepthMessage

def encode (message : OptionMarketDepthMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (ExpiryMonth.encode message.expiryMonth
    ++ (Alpha.encode message.filler1
    ++ (StrikePriceInstrumentFractionPair.encode message.strikePriceInstrumentFractionPair
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay
    ++ (InstrumentStatusMarker.encode message.instrumentStatusMarker
    ++ (encodeDigits 1 message.optionMarketDepthTradingInstrument.val.length
    ++ (encodeMany OptionMarketDepthTradingInstrument.encode message.optionMarketDepthTradingInstrument.val)))))))))

def decode (bytes : List UInt8) : Option (OptionMarketDepthMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (expiryMonth, bytes) ← ExpiryMonth.decode bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (strikePriceInstrumentFractionPair, bytes) ← StrikePriceInstrumentFractionPair.decode bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (instrumentStatusMarker, bytes) ← InstrumentStatusMarker.decode bytes
  let (numberOfLevel, bytes) ← decodeDigits 1 bytes
  let (optionMarketDepthTradingInstrument_, bytes) ← decodeMany OptionMarketDepthTradingInstrument.decode numberOfLevel bytes
  if fits_optionMarketDepthTradingInstrument : optionMarketDepthTradingInstrument_.length < 10 ^ 1 then
    pure ({ exchangeId, rootSymbol, expiryMonth, filler1, strikePriceInstrumentFractionPair, expiryYear, expiryDay, instrumentStatusMarker, optionMarketDepthTradingInstrument := ⟨optionMarketDepthTradingInstrument_, fits_optionMarketDepthTradingInstrument⟩ }, bytes)
  else none

theorem encode_length_pos (message : OptionMarketDepthMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [ExchangeId.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OptionMarketDepthMessage) : (encode message).length ≤ 284 := by
  have bound_optionMarketDepthTradingInstrument := message.optionMarketDepthTradingInstrument.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, ExchangeId.encode_length, Alpha.encode_length, ExpiryMonth.encode_length, StrikePriceInstrumentFractionPair.encode_length, InstrumentStatusMarker.encode_length, encodeDigits_length, encodeMany_length_const OptionMarketDepthTradingInstrument.encode 29 OptionMarketDepthTradingInstrument.encode_length]
  omega

@[simp] theorem decode_encode (message : OptionMarketDepthMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExpiryMonth.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StrikePriceInstrumentFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentStatusMarker.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.optionMarketDepthTradingInstrument.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany OptionMarketDepthTradingInstrument.encode OptionMarketDepthTradingInstrument.decode OptionMarketDepthTradingInstrument.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.optionMarketDepthTradingInstrument.length_lt]
  rfl

end OptionMarketDepthMessage

/-- Future Options Market Depth Trading Instrument: 29 bytes -/
structure FutureOptionsMarketDepthTradingInstrument where
  levelOfMarketDepth : LevelOfMarketDepth
  bidPriceQuote : BidPriceQuote
  bidSize : Alpha 5
  numberOfBidOrders : Alpha 2
  askPriceQuote : AskPriceQuote
  askSize : Alpha 5
  numberOfAskOrders : Alpha 2
  deriving DecidableEq, Repr

namespace FutureOptionsMarketDepthTradingInstrument

def encode (message : FutureOptionsMarketDepthTradingInstrument) : List UInt8 :=
  LevelOfMarketDepth.encode message.levelOfMarketDepth
    ++ (BidPriceQuote.encode message.bidPriceQuote
    ++ (Alpha.encode message.bidSize
    ++ (Alpha.encode message.numberOfBidOrders
    ++ (AskPriceQuote.encode message.askPriceQuote
    ++ (Alpha.encode message.askSize
    ++ (Alpha.encode message.numberOfAskOrders))))))

def decode (bytes : List UInt8) : Option (FutureOptionsMarketDepthTradingInstrument × List UInt8) := do
  let (levelOfMarketDepth, bytes) ← LevelOfMarketDepth.decode bytes
  let (bidPriceQuote, bytes) ← BidPriceQuote.decode bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (numberOfBidOrders, bytes) ← Alpha.decode 2 bytes
  let (askPriceQuote, bytes) ← AskPriceQuote.decode bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (numberOfAskOrders, bytes) ← Alpha.decode 2 bytes
  pure ({ levelOfMarketDepth, bidPriceQuote, bidSize, numberOfBidOrders, askPriceQuote, askSize, numberOfAskOrders }, bytes)

@[simp] theorem encode_length (message : FutureOptionsMarketDepthTradingInstrument) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, LevelOfMarketDepth.encode_length, BidPriceQuote.encode_length, Alpha.encode_length, AskPriceQuote.encode_length]

theorem encode_length_pos (message : FutureOptionsMarketDepthTradingInstrument) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FutureOptionsMarketDepthTradingInstrument) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LevelOfMarketDepth.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BidPriceQuote.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskPriceQuote.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FutureOptionsMarketDepthTradingInstrument

/-- Future Options Market Depth Message -/
structure FutureOptionsMarketDepthMessage where
  exchangeId : ExchangeId
  rootSymbol : Alpha 6
  contractMonthCode : ContractMonthCode
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  callPutCode : CallPutCode
  strikePriceInstrumentFractionPair : StrikePriceInstrumentFractionPair
  instrumentStatusMarker : InstrumentStatusMarker
  futureOptionsMarketDepthTradingInstrument : Digited 1 FutureOptionsMarketDepthTradingInstrument
  deriving DecidableEq, Repr

namespace FutureOptionsMarketDepthMessage

def encode (message : FutureOptionsMarketDepthMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (ContractMonthCode.encode message.contractMonthCode
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay
    ++ (CallPutCode.encode message.callPutCode
    ++ (StrikePriceInstrumentFractionPair.encode message.strikePriceInstrumentFractionPair
    ++ (InstrumentStatusMarker.encode message.instrumentStatusMarker
    ++ (encodeDigits 1 message.futureOptionsMarketDepthTradingInstrument.val.length
    ++ (encodeMany FutureOptionsMarketDepthTradingInstrument.encode message.futureOptionsMarketDepthTradingInstrument.val)))))))))

def decode (bytes : List UInt8) : Option (FutureOptionsMarketDepthMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (contractMonthCode, bytes) ← ContractMonthCode.decode bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (callPutCode, bytes) ← CallPutCode.decode bytes
  let (strikePriceInstrumentFractionPair, bytes) ← StrikePriceInstrumentFractionPair.decode bytes
  let (instrumentStatusMarker, bytes) ← InstrumentStatusMarker.decode bytes
  let (numberOfLevel, bytes) ← decodeDigits 1 bytes
  let (futureOptionsMarketDepthTradingInstrument_, bytes) ← decodeMany FutureOptionsMarketDepthTradingInstrument.decode numberOfLevel bytes
  if fits_futureOptionsMarketDepthTradingInstrument : futureOptionsMarketDepthTradingInstrument_.length < 10 ^ 1 then
    pure ({ exchangeId, rootSymbol, contractMonthCode, expiryYear, expiryDay, callPutCode, strikePriceInstrumentFractionPair, instrumentStatusMarker, futureOptionsMarketDepthTradingInstrument := ⟨futureOptionsMarketDepthTradingInstrument_, fits_futureOptionsMarketDepthTradingInstrument⟩ }, bytes)
  else none

theorem encode_length_pos (message : FutureOptionsMarketDepthMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [ExchangeId.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : FutureOptionsMarketDepthMessage) : (encode message).length ≤ 284 := by
  have bound_futureOptionsMarketDepthTradingInstrument := message.futureOptionsMarketDepthTradingInstrument.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, ExchangeId.encode_length, Alpha.encode_length, ContractMonthCode.encode_length, CallPutCode.encode_length, StrikePriceInstrumentFractionPair.encode_length, InstrumentStatusMarker.encode_length, encodeDigits_length, encodeMany_length_const FutureOptionsMarketDepthTradingInstrument.encode 29 FutureOptionsMarketDepthTradingInstrument.encode_length]
  omega

@[simp] theorem decode_encode (message : FutureOptionsMarketDepthMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ContractMonthCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CallPutCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StrikePriceInstrumentFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentStatusMarker.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.futureOptionsMarketDepthTradingInstrument.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany FutureOptionsMarketDepthTradingInstrument.encode FutureOptionsMarketDepthTradingInstrument.decode FutureOptionsMarketDepthTradingInstrument.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.futureOptionsMarketDepthTradingInstrument.length_lt]
  rfl

end FutureOptionsMarketDepthMessage

/-- Bid Price Quote Futures Market Depth Trading Instrument: 7 bytes -/
structure BidPriceQuoteFuturesMarketDepthTradingInstrument where
  rawBidPriceQuoteNumericBidPriceQuoteFuturesMarketDepthTradingInstrumentNumericPair : Alpha 6
  bidPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace BidPriceQuoteFuturesMarketDepthTradingInstrument

def encode (message : BidPriceQuoteFuturesMarketDepthTradingInstrument) : List UInt8 :=
  Alpha.encode message.rawBidPriceQuoteNumericBidPriceQuoteFuturesMarketDepthTradingInstrumentNumericPair
    ++ (encodeUInt 1 message.bidPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (BidPriceQuoteFuturesMarketDepthTradingInstrument × List UInt8) := do
  let (rawBidPriceQuoteNumericBidPriceQuoteFuturesMarketDepthTradingInstrumentNumericPair, bytes) ← Alpha.decode 6 bytes
  let (bidPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawBidPriceQuoteNumericBidPriceQuoteFuturesMarketDepthTradingInstrumentNumericPair, bidPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : BidPriceQuoteFuturesMarketDepthTradingInstrument) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : BidPriceQuoteFuturesMarketDepthTradingInstrument) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BidPriceQuoteFuturesMarketDepthTradingInstrument) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end BidPriceQuoteFuturesMarketDepthTradingInstrument

/-- Ask Price Futures Depth Futures Market Depth Trading Instrument: 7 bytes -/
structure AskPriceFuturesDepthFuturesMarketDepthTradingInstrument where
  rawAskPriceFuturesDepthNumeric : Alpha 6
  askPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace AskPriceFuturesDepthFuturesMarketDepthTradingInstrument

def encode (message : AskPriceFuturesDepthFuturesMarketDepthTradingInstrument) : List UInt8 :=
  Alpha.encode message.rawAskPriceFuturesDepthNumeric
    ++ (encodeUInt 1 message.askPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (AskPriceFuturesDepthFuturesMarketDepthTradingInstrument × List UInt8) := do
  let (rawAskPriceFuturesDepthNumeric, bytes) ← Alpha.decode 6 bytes
  let (askPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawAskPriceFuturesDepthNumeric, askPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : AskPriceFuturesDepthFuturesMarketDepthTradingInstrument) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : AskPriceFuturesDepthFuturesMarketDepthTradingInstrument) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AskPriceFuturesDepthFuturesMarketDepthTradingInstrument) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end AskPriceFuturesDepthFuturesMarketDepthTradingInstrument

/-- Futures Market Depth Trading Instrument: 29 bytes -/
structure FuturesMarketDepthTradingInstrument where
  levelOfMarketDepth : LevelOfMarketDepth
  bidPriceQuoteFuturesMarketDepthTradingInstrument : BidPriceQuoteFuturesMarketDepthTradingInstrument
  bidSize : Alpha 5
  numberOfBidOrders : Alpha 2
  askPriceFuturesDepthFuturesMarketDepthTradingInstrument : AskPriceFuturesDepthFuturesMarketDepthTradingInstrument
  askSize : Alpha 5
  numberOfAskOrders : Alpha 2
  deriving DecidableEq, Repr

namespace FuturesMarketDepthTradingInstrument

def encode (message : FuturesMarketDepthTradingInstrument) : List UInt8 :=
  LevelOfMarketDepth.encode message.levelOfMarketDepth
    ++ (BidPriceQuoteFuturesMarketDepthTradingInstrument.encode message.bidPriceQuoteFuturesMarketDepthTradingInstrument
    ++ (Alpha.encode message.bidSize
    ++ (Alpha.encode message.numberOfBidOrders
    ++ (AskPriceFuturesDepthFuturesMarketDepthTradingInstrument.encode message.askPriceFuturesDepthFuturesMarketDepthTradingInstrument
    ++ (Alpha.encode message.askSize
    ++ (Alpha.encode message.numberOfAskOrders))))))

def decode (bytes : List UInt8) : Option (FuturesMarketDepthTradingInstrument × List UInt8) := do
  let (levelOfMarketDepth, bytes) ← LevelOfMarketDepth.decode bytes
  let (bidPriceQuoteFuturesMarketDepthTradingInstrument, bytes) ← BidPriceQuoteFuturesMarketDepthTradingInstrument.decode bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (numberOfBidOrders, bytes) ← Alpha.decode 2 bytes
  let (askPriceFuturesDepthFuturesMarketDepthTradingInstrument, bytes) ← AskPriceFuturesDepthFuturesMarketDepthTradingInstrument.decode bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (numberOfAskOrders, bytes) ← Alpha.decode 2 bytes
  pure ({ levelOfMarketDepth, bidPriceQuoteFuturesMarketDepthTradingInstrument, bidSize, numberOfBidOrders, askPriceFuturesDepthFuturesMarketDepthTradingInstrument, askSize, numberOfAskOrders }, bytes)

@[simp] theorem encode_length (message : FuturesMarketDepthTradingInstrument) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, LevelOfMarketDepth.encode_length, BidPriceQuoteFuturesMarketDepthTradingInstrument.encode_length, Alpha.encode_length, AskPriceFuturesDepthFuturesMarketDepthTradingInstrument.encode_length]

theorem encode_length_pos (message : FuturesMarketDepthTradingInstrument) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FuturesMarketDepthTradingInstrument) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LevelOfMarketDepth.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BidPriceQuoteFuturesMarketDepthTradingInstrument.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskPriceFuturesDepthFuturesMarketDepthTradingInstrument.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FuturesMarketDepthTradingInstrument

/-- Futures Market Depth Message -/
structure FuturesMarketDepthMessage where
  exchangeId : ExchangeId
  rootSymbol : Alpha 6
  deliveryMonth : DeliveryMonth
  deliveryYearFutures : Alpha 2
  deliveryDay : Alpha 2
  instrumentStatusMarker : InstrumentStatusMarker
  futuresMarketDepthTradingInstrument : Digited 1 FuturesMarketDepthTradingInstrument
  deriving DecidableEq, Repr

namespace FuturesMarketDepthMessage

def encode (message : FuturesMarketDepthMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (DeliveryMonth.encode message.deliveryMonth
    ++ (Alpha.encode message.deliveryYearFutures
    ++ (Alpha.encode message.deliveryDay
    ++ (InstrumentStatusMarker.encode message.instrumentStatusMarker
    ++ (encodeDigits 1 message.futuresMarketDepthTradingInstrument.val.length
    ++ (encodeMany FuturesMarketDepthTradingInstrument.encode message.futuresMarketDepthTradingInstrument.val)))))))

def decode (bytes : List UInt8) : Option (FuturesMarketDepthMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (deliveryMonth, bytes) ← DeliveryMonth.decode bytes
  let (deliveryYearFutures, bytes) ← Alpha.decode 2 bytes
  let (deliveryDay, bytes) ← Alpha.decode 2 bytes
  let (instrumentStatusMarker, bytes) ← InstrumentStatusMarker.decode bytes
  let (numberOfLevel, bytes) ← decodeDigits 1 bytes
  let (futuresMarketDepthTradingInstrument_, bytes) ← decodeMany FuturesMarketDepthTradingInstrument.decode numberOfLevel bytes
  if fits_futuresMarketDepthTradingInstrument : futuresMarketDepthTradingInstrument_.length < 10 ^ 1 then
    pure ({ exchangeId, rootSymbol, deliveryMonth, deliveryYearFutures, deliveryDay, instrumentStatusMarker, futuresMarketDepthTradingInstrument := ⟨futuresMarketDepthTradingInstrument_, fits_futuresMarketDepthTradingInstrument⟩ }, bytes)
  else none

theorem encode_length_pos (message : FuturesMarketDepthMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [ExchangeId.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : FuturesMarketDepthMessage) : (encode message).length ≤ 275 := by
  have bound_futuresMarketDepthTradingInstrument := message.futuresMarketDepthTradingInstrument.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, ExchangeId.encode_length, Alpha.encode_length, DeliveryMonth.encode_length, InstrumentStatusMarker.encode_length, encodeDigits_length, encodeMany_length_const FuturesMarketDepthTradingInstrument.encode 29 FuturesMarketDepthTradingInstrument.encode_length]
  omega

@[simp] theorem decode_encode (message : FuturesMarketDepthMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DeliveryMonth.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentStatusMarker.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.futuresMarketDepthTradingInstrument.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany FuturesMarketDepthTradingInstrument.encode FuturesMarketDepthTradingInstrument.decode FuturesMarketDepthTradingInstrument.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.futuresMarketDepthTradingInstrument.length_lt]
  rfl

end FuturesMarketDepthMessage

/-- Strategy Market Depth Trading Instrument: 31 bytes -/
structure StrategyMarketDepthTradingInstrument where
  levelOfMarketDepth : LevelOfMarketDepth
  bidPriceSign : BidPriceSign
  bidPriceQuote : BidPriceQuote
  bidSize : Alpha 5
  numberOfBidOrders : Alpha 2
  askPriceSign : AskPriceSign
  askPriceQuote : AskPriceQuote
  askSize : Alpha 5
  numberOfAskOrders : Alpha 2
  deriving DecidableEq, Repr

namespace StrategyMarketDepthTradingInstrument

def encode (message : StrategyMarketDepthTradingInstrument) : List UInt8 :=
  LevelOfMarketDepth.encode message.levelOfMarketDepth
    ++ (BidPriceSign.encode message.bidPriceSign
    ++ (BidPriceQuote.encode message.bidPriceQuote
    ++ (Alpha.encode message.bidSize
    ++ (Alpha.encode message.numberOfBidOrders
    ++ (AskPriceSign.encode message.askPriceSign
    ++ (AskPriceQuote.encode message.askPriceQuote
    ++ (Alpha.encode message.askSize
    ++ (Alpha.encode message.numberOfAskOrders))))))))

def decode (bytes : List UInt8) : Option (StrategyMarketDepthTradingInstrument × List UInt8) := do
  let (levelOfMarketDepth, bytes) ← LevelOfMarketDepth.decode bytes
  let (bidPriceSign, bytes) ← BidPriceSign.decode bytes
  let (bidPriceQuote, bytes) ← BidPriceQuote.decode bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (numberOfBidOrders, bytes) ← Alpha.decode 2 bytes
  let (askPriceSign, bytes) ← AskPriceSign.decode bytes
  let (askPriceQuote, bytes) ← AskPriceQuote.decode bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (numberOfAskOrders, bytes) ← Alpha.decode 2 bytes
  pure ({ levelOfMarketDepth, bidPriceSign, bidPriceQuote, bidSize, numberOfBidOrders, askPriceSign, askPriceQuote, askSize, numberOfAskOrders }, bytes)

@[simp] theorem encode_length (message : StrategyMarketDepthTradingInstrument) : (encode message).length = 31 := by
  unfold encode
  simp only [List.length_append, LevelOfMarketDepth.encode_length, BidPriceSign.encode_length, BidPriceQuote.encode_length, Alpha.encode_length, AskPriceSign.encode_length, AskPriceQuote.encode_length]

theorem encode_length_pos (message : StrategyMarketDepthTradingInstrument) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyMarketDepthTradingInstrument) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LevelOfMarketDepth.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BidPriceSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BidPriceQuote.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskPriceSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskPriceQuote.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StrategyMarketDepthTradingInstrument

/-- Strategy Market Depth Message -/
structure StrategyMarketDepthMessage where
  exchangeId : ExchangeId
  symbol : Alpha 30
  instrumentStatusMarker : InstrumentStatusMarker
  strategyMarketDepthTradingInstrument : Digited 1 StrategyMarketDepthTradingInstrument
  deriving DecidableEq, Repr

namespace StrategyMarketDepthMessage

def encode (message : StrategyMarketDepthMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.symbol
    ++ (InstrumentStatusMarker.encode message.instrumentStatusMarker
    ++ (encodeDigits 1 message.strategyMarketDepthTradingInstrument.val.length
    ++ (encodeMany StrategyMarketDepthTradingInstrument.encode message.strategyMarketDepthTradingInstrument.val))))

def decode (bytes : List UInt8) : Option (StrategyMarketDepthMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (symbol, bytes) ← Alpha.decode 30 bytes
  let (instrumentStatusMarker, bytes) ← InstrumentStatusMarker.decode bytes
  let (numberOfLevel, bytes) ← decodeDigits 1 bytes
  let (strategyMarketDepthTradingInstrument_, bytes) ← decodeMany StrategyMarketDepthTradingInstrument.decode numberOfLevel bytes
  if fits_strategyMarketDepthTradingInstrument : strategyMarketDepthTradingInstrument_.length < 10 ^ 1 then
    pure ({ exchangeId, symbol, instrumentStatusMarker, strategyMarketDepthTradingInstrument := ⟨strategyMarketDepthTradingInstrument_, fits_strategyMarketDepthTradingInstrument⟩ }, bytes)
  else none

theorem encode_length_pos (message : StrategyMarketDepthMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [ExchangeId.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : StrategyMarketDepthMessage) : (encode message).length ≤ 312 := by
  have bound_strategyMarketDepthTradingInstrument := message.strategyMarketDepthTradingInstrument.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, ExchangeId.encode_length, Alpha.encode_length, InstrumentStatusMarker.encode_length, encodeDigits_length, encodeMany_length_const StrategyMarketDepthTradingInstrument.encode 31 StrategyMarketDepthTradingInstrument.encode_length]
  omega

@[simp] theorem decode_encode (message : StrategyMarketDepthMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentStatusMarker.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.strategyMarketDepthTradingInstrument.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany StrategyMarketDepthTradingInstrument.encode StrategyMarketDepthTradingInstrument.decode StrategyMarketDepthTradingInstrument.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.strategyMarketDepthTradingInstrument.length_lt]
  rfl

end StrategyMarketDepthMessage

/-- Swap Future Market Depth Trading Instrument: 29 bytes -/
structure SwapFutureMarketDepthTradingInstrument where
  level : Level
  bidPriceQuote : BidPriceQuote
  bidSize : Alpha 5
  numberOfBidOrders : Alpha 2
  askPriceQuote : AskPriceQuote
  askSize : Alpha 5
  numberOfAskOrders : Alpha 2
  deriving DecidableEq, Repr

namespace SwapFutureMarketDepthTradingInstrument

def encode (message : SwapFutureMarketDepthTradingInstrument) : List UInt8 :=
  Level.encode message.level
    ++ (BidPriceQuote.encode message.bidPriceQuote
    ++ (Alpha.encode message.bidSize
    ++ (Alpha.encode message.numberOfBidOrders
    ++ (AskPriceQuote.encode message.askPriceQuote
    ++ (Alpha.encode message.askSize
    ++ (Alpha.encode message.numberOfAskOrders))))))

def decode (bytes : List UInt8) : Option (SwapFutureMarketDepthTradingInstrument × List UInt8) := do
  let (level, bytes) ← Level.decode bytes
  let (bidPriceQuote, bytes) ← BidPriceQuote.decode bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (numberOfBidOrders, bytes) ← Alpha.decode 2 bytes
  let (askPriceQuote, bytes) ← AskPriceQuote.decode bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (numberOfAskOrders, bytes) ← Alpha.decode 2 bytes
  pure ({ level, bidPriceQuote, bidSize, numberOfBidOrders, askPriceQuote, askSize, numberOfAskOrders }, bytes)

@[simp] theorem encode_length (message : SwapFutureMarketDepthTradingInstrument) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, Level.encode_length, BidPriceQuote.encode_length, Alpha.encode_length, AskPriceQuote.encode_length]

theorem encode_length_pos (message : SwapFutureMarketDepthTradingInstrument) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SwapFutureMarketDepthTradingInstrument) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Level.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BidPriceQuote.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskPriceQuote.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SwapFutureMarketDepthTradingInstrument

/-- Swap Future Market Depth Message -/
structure SwapFutureMarketDepthMessage where
  exchangeId : ExchangeId
  rootSymbolSwapFuture : Alpha 6
  expiryMonthSwapFuture : ExpiryMonthSwapFuture
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  tenor : Alpha 2
  fixedRateFractionPair : FixedRateFractionPair
  instrumentStatusMarker : InstrumentStatusMarker
  swapFutureMarketDepthTradingInstrument : Digited 1 SwapFutureMarketDepthTradingInstrument
  deriving DecidableEq, Repr

namespace SwapFutureMarketDepthMessage

def encode (message : SwapFutureMarketDepthMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbolSwapFuture
    ++ (ExpiryMonthSwapFuture.encode message.expiryMonthSwapFuture
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay
    ++ (Alpha.encode message.tenor
    ++ (FixedRateFractionPair.encode message.fixedRateFractionPair
    ++ (InstrumentStatusMarker.encode message.instrumentStatusMarker
    ++ (encodeDigits 1 message.swapFutureMarketDepthTradingInstrument.val.length
    ++ (encodeMany SwapFutureMarketDepthTradingInstrument.encode message.swapFutureMarketDepthTradingInstrument.val)))))))))

def decode (bytes : List UInt8) : Option (SwapFutureMarketDepthMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (rootSymbolSwapFuture, bytes) ← Alpha.decode 6 bytes
  let (expiryMonthSwapFuture, bytes) ← ExpiryMonthSwapFuture.decode bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (tenor, bytes) ← Alpha.decode 2 bytes
  let (fixedRateFractionPair, bytes) ← FixedRateFractionPair.decode bytes
  let (instrumentStatusMarker, bytes) ← InstrumentStatusMarker.decode bytes
  let (numberOfLevel, bytes) ← decodeDigits 1 bytes
  let (swapFutureMarketDepthTradingInstrument_, bytes) ← decodeMany SwapFutureMarketDepthTradingInstrument.decode numberOfLevel bytes
  if fits_swapFutureMarketDepthTradingInstrument : swapFutureMarketDepthTradingInstrument_.length < 10 ^ 1 then
    pure ({ exchangeId, rootSymbolSwapFuture, expiryMonthSwapFuture, expiryYear, expiryDay, tenor, fixedRateFractionPair, instrumentStatusMarker, swapFutureMarketDepthTradingInstrument := ⟨swapFutureMarketDepthTradingInstrument_, fits_swapFutureMarketDepthTradingInstrument⟩ }, bytes)
  else none

theorem encode_length_pos (message : SwapFutureMarketDepthMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [ExchangeId.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SwapFutureMarketDepthMessage) : (encode message).length ≤ 283 := by
  have bound_swapFutureMarketDepthTradingInstrument := message.swapFutureMarketDepthTradingInstrument.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, ExchangeId.encode_length, Alpha.encode_length, ExpiryMonthSwapFuture.encode_length, FixedRateFractionPair.encode_length, InstrumentStatusMarker.encode_length, encodeDigits_length, encodeMany_length_const SwapFutureMarketDepthTradingInstrument.encode 29 SwapFutureMarketDepthTradingInstrument.encode_length]
  omega

@[simp] theorem decode_encode (message : SwapFutureMarketDepthMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExpiryMonthSwapFuture.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FixedRateFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentStatusMarker.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.swapFutureMarketDepthTradingInstrument.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany SwapFutureMarketDepthTradingInstrument.encode SwapFutureMarketDepthTradingInstrument.decode SwapFutureMarketDepthTradingInstrument.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.swapFutureMarketDepthTradingInstrument.length_lt]
  rfl

end SwapFutureMarketDepthMessage

/-- Option Trade Cancellation Message: 68 bytes -/
structure OptionTradeCancellationMessage where
  exchangeId : ExchangeId
  rootSymbol : Alpha 6
  expiryMonth : ExpiryMonth
  filler1 : Alpha 1
  strikePriceInstrumentFractionPair : StrikePriceInstrumentFractionPair
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  volume : Alpha 8
  tradePriceFractionPair : TradePriceFractionPair
  filler6 : Alpha 6
  timestamp : Alpha 9
  openInterest : Alpha 7
  secondFiller1 : Alpha 1
  priceIndicatorMarker : PriceIndicatorMarker
  tradeNumber : Alpha 8
  deriving DecidableEq, Repr

namespace OptionTradeCancellationMessage

def encode (message : OptionTradeCancellationMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (ExpiryMonth.encode message.expiryMonth
    ++ (Alpha.encode message.filler1
    ++ (StrikePriceInstrumentFractionPair.encode message.strikePriceInstrumentFractionPair
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay
    ++ (Alpha.encode message.volume
    ++ (TradePriceFractionPair.encode message.tradePriceFractionPair
    ++ (Alpha.encode message.filler6
    ++ (Alpha.encode message.timestamp
    ++ (Alpha.encode message.openInterest
    ++ (Alpha.encode message.secondFiller1
    ++ (PriceIndicatorMarker.encode message.priceIndicatorMarker
    ++ (Alpha.encode message.tradeNumber))))))))))))))

def decode (bytes : List UInt8) : Option (OptionTradeCancellationMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (expiryMonth, bytes) ← ExpiryMonth.decode bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (strikePriceInstrumentFractionPair, bytes) ← StrikePriceInstrumentFractionPair.decode bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePriceFractionPair, bytes) ← TradePriceFractionPair.decode bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (timestamp, bytes) ← Alpha.decode 9 bytes
  let (openInterest, bytes) ← Alpha.decode 7 bytes
  let (secondFiller1, bytes) ← Alpha.decode 1 bytes
  let (priceIndicatorMarker, bytes) ← PriceIndicatorMarker.decode bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ exchangeId, rootSymbol, expiryMonth, filler1, strikePriceInstrumentFractionPair, expiryYear, expiryDay, volume, tradePriceFractionPair, filler6, timestamp, openInterest, secondFiller1, priceIndicatorMarker, tradeNumber }, bytes)

@[simp] theorem encode_length (message : OptionTradeCancellationMessage) : (encode message).length = 68 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length, ExpiryMonth.encode_length, StrikePriceInstrumentFractionPair.encode_length, TradePriceFractionPair.encode_length, PriceIndicatorMarker.encode_length]

theorem encode_length_pos (message : OptionTradeCancellationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionTradeCancellationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExpiryMonth.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StrikePriceInstrumentFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradePriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PriceIndicatorMarker.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OptionTradeCancellationMessage

/-- Price Fraction Pair: 7 bytes -/
structure PriceFractionPair where
  rawPrice : Alpha 6
  priceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace PriceFractionPair

def encode (message : PriceFractionPair) : List UInt8 :=
  Alpha.encode message.rawPrice
    ++ (encodeUInt 1 message.priceFractionIndicator)

def decode (bytes : List UInt8) : Option (PriceFractionPair × List UInt8) := do
  let (rawPrice, bytes) ← Alpha.decode 6 bytes
  let (priceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawPrice, priceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : PriceFractionPair) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : PriceFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PriceFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end PriceFractionPair

/-- Future Options Trade Cancellation Message: 69 bytes -/
structure FutureOptionsTradeCancellationMessage where
  exchangeId : ExchangeId
  rootSymbol : Alpha 6
  contractMonthCode : ContractMonthCode
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  callPutCode : CallPutCode
  strikePriceInstrumentFractionPair : StrikePriceInstrumentFractionPair
  volume : Alpha 8
  priceFractionPair : PriceFractionPair
  priceIndicatorMarker : PriceIndicatorMarker
  filler6 : Alpha 6
  timestamp : Alpha 9
  openInterest : Alpha 7
  filler2 : Alpha 2
  tradeNumber : Alpha 8
  deriving DecidableEq, Repr

namespace FutureOptionsTradeCancellationMessage

def encode (message : FutureOptionsTradeCancellationMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (ContractMonthCode.encode message.contractMonthCode
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay
    ++ (CallPutCode.encode message.callPutCode
    ++ (StrikePriceInstrumentFractionPair.encode message.strikePriceInstrumentFractionPair
    ++ (Alpha.encode message.volume
    ++ (PriceFractionPair.encode message.priceFractionPair
    ++ (PriceIndicatorMarker.encode message.priceIndicatorMarker
    ++ (Alpha.encode message.filler6
    ++ (Alpha.encode message.timestamp
    ++ (Alpha.encode message.openInterest
    ++ (Alpha.encode message.filler2
    ++ (Alpha.encode message.tradeNumber))))))))))))))

def decode (bytes : List UInt8) : Option (FutureOptionsTradeCancellationMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (contractMonthCode, bytes) ← ContractMonthCode.decode bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (callPutCode, bytes) ← CallPutCode.decode bytes
  let (strikePriceInstrumentFractionPair, bytes) ← StrikePriceInstrumentFractionPair.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (priceFractionPair, bytes) ← PriceFractionPair.decode bytes
  let (priceIndicatorMarker, bytes) ← PriceIndicatorMarker.decode bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (timestamp, bytes) ← Alpha.decode 9 bytes
  let (openInterest, bytes) ← Alpha.decode 7 bytes
  let (filler2, bytes) ← Alpha.decode 2 bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ exchangeId, rootSymbol, contractMonthCode, expiryYear, expiryDay, callPutCode, strikePriceInstrumentFractionPair, volume, priceFractionPair, priceIndicatorMarker, filler6, timestamp, openInterest, filler2, tradeNumber }, bytes)

@[simp] theorem encode_length (message : FutureOptionsTradeCancellationMessage) : (encode message).length = 69 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length, ContractMonthCode.encode_length, CallPutCode.encode_length, StrikePriceInstrumentFractionPair.encode_length, PriceFractionPair.encode_length, PriceIndicatorMarker.encode_length]

theorem encode_length_pos (message : FutureOptionsTradeCancellationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FutureOptionsTradeCancellationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ContractMonthCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CallPutCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StrikePriceInstrumentFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PriceIndicatorMarker.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FutureOptionsTradeCancellationMessage

/-- Futures Trade Cancellation Message: 51 bytes -/
structure FuturesTradeCancellationMessage where
  exchangeId : ExchangeId
  rootSymbol : Alpha 6
  deliveryMonth : DeliveryMonth
  deliveryYearFutures : Alpha 2
  deliveryDay : Alpha 2
  volume : Alpha 8
  tradePriceFractionPair : TradePriceFractionPair
  filler6 : Alpha 6
  timestamp : Alpha 9
  priceIndicatorMarker : FuturesTradeMessagePriceIndicatorMarker
  tradeNumber : Alpha 8
  deriving DecidableEq, Repr

namespace FuturesTradeCancellationMessage

def encode (message : FuturesTradeCancellationMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (DeliveryMonth.encode message.deliveryMonth
    ++ (Alpha.encode message.deliveryYearFutures
    ++ (Alpha.encode message.deliveryDay
    ++ (Alpha.encode message.volume
    ++ (TradePriceFractionPair.encode message.tradePriceFractionPair
    ++ (Alpha.encode message.filler6
    ++ (Alpha.encode message.timestamp
    ++ (FuturesTradeMessagePriceIndicatorMarker.encode message.priceIndicatorMarker
    ++ (Alpha.encode message.tradeNumber))))))))))

def decode (bytes : List UInt8) : Option (FuturesTradeCancellationMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (deliveryMonth, bytes) ← DeliveryMonth.decode bytes
  let (deliveryYearFutures, bytes) ← Alpha.decode 2 bytes
  let (deliveryDay, bytes) ← Alpha.decode 2 bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePriceFractionPair, bytes) ← TradePriceFractionPair.decode bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (timestamp, bytes) ← Alpha.decode 9 bytes
  let (priceIndicatorMarker, bytes) ← FuturesTradeMessagePriceIndicatorMarker.decode bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ exchangeId, rootSymbol, deliveryMonth, deliveryYearFutures, deliveryDay, volume, tradePriceFractionPair, filler6, timestamp, priceIndicatorMarker, tradeNumber }, bytes)

@[simp] theorem encode_length (message : FuturesTradeCancellationMessage) : (encode message).length = 51 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length, DeliveryMonth.encode_length, TradePriceFractionPair.encode_length, FuturesTradeMessagePriceIndicatorMarker.encode_length]

theorem encode_length_pos (message : FuturesTradeCancellationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FuturesTradeCancellationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DeliveryMonth.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradePriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FuturesTradeMessagePriceIndicatorMarker.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FuturesTradeCancellationMessage

/-- Strategy Trade Cancellation Message: 71 bytes -/
structure StrategyTradeCancellationMessage where
  exchangeId : ExchangeId
  symbol : Alpha 30
  volume : Alpha 8
  tradePriceSign : TradePriceSign
  tradePriceFractionPair : TradePriceFractionPair
  filler6 : Alpha 6
  timestamp : Alpha 9
  filler1 : Alpha 1
  tradeNumber : Alpha 8
  deriving DecidableEq, Repr

namespace StrategyTradeCancellationMessage

def encode (message : StrategyTradeCancellationMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.volume
    ++ (TradePriceSign.encode message.tradePriceSign
    ++ (TradePriceFractionPair.encode message.tradePriceFractionPair
    ++ (Alpha.encode message.filler6
    ++ (Alpha.encode message.timestamp
    ++ (Alpha.encode message.filler1
    ++ (Alpha.encode message.tradeNumber))))))))

def decode (bytes : List UInt8) : Option (StrategyTradeCancellationMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (symbol, bytes) ← Alpha.decode 30 bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePriceSign, bytes) ← TradePriceSign.decode bytes
  let (tradePriceFractionPair, bytes) ← TradePriceFractionPair.decode bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (timestamp, bytes) ← Alpha.decode 9 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ exchangeId, symbol, volume, tradePriceSign, tradePriceFractionPair, filler6, timestamp, filler1, tradeNumber }, bytes)

@[simp] theorem encode_length (message : StrategyTradeCancellationMessage) : (encode message).length = 71 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length, TradePriceSign.encode_length, TradePriceFractionPair.encode_length]

theorem encode_length_pos (message : StrategyTradeCancellationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyTradeCancellationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradePriceSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradePriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StrategyTradeCancellationMessage

/-- Swap Future Trade Cancellation Message: 53 bytes -/
structure SwapFutureTradeCancellationMessage where
  exchangeId : ExchangeId
  rootSymbolSwapFuture : Alpha 6
  expiryMonthSwapFuture : ExpiryMonthSwapFuture
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  tenor : Alpha 2
  fixedRateFractionPair : FixedRateFractionPair
  volume : Alpha 8
  tradePriceFractionPair : TradePriceFractionPair
  timestamp : Alpha 9
  marketPriceIndicator : MarketPriceIndicator
  tradeNumber : Alpha 8
  deriving DecidableEq, Repr

namespace SwapFutureTradeCancellationMessage

def encode (message : SwapFutureTradeCancellationMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbolSwapFuture
    ++ (ExpiryMonthSwapFuture.encode message.expiryMonthSwapFuture
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay
    ++ (Alpha.encode message.tenor
    ++ (FixedRateFractionPair.encode message.fixedRateFractionPair
    ++ (Alpha.encode message.volume
    ++ (TradePriceFractionPair.encode message.tradePriceFractionPair
    ++ (Alpha.encode message.timestamp
    ++ (MarketPriceIndicator.encode message.marketPriceIndicator
    ++ (Alpha.encode message.tradeNumber)))))))))))

def decode (bytes : List UInt8) : Option (SwapFutureTradeCancellationMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (rootSymbolSwapFuture, bytes) ← Alpha.decode 6 bytes
  let (expiryMonthSwapFuture, bytes) ← ExpiryMonthSwapFuture.decode bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (tenor, bytes) ← Alpha.decode 2 bytes
  let (fixedRateFractionPair, bytes) ← FixedRateFractionPair.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePriceFractionPair, bytes) ← TradePriceFractionPair.decode bytes
  let (timestamp, bytes) ← Alpha.decode 9 bytes
  let (marketPriceIndicator, bytes) ← MarketPriceIndicator.decode bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ exchangeId, rootSymbolSwapFuture, expiryMonthSwapFuture, expiryYear, expiryDay, tenor, fixedRateFractionPair, volume, tradePriceFractionPair, timestamp, marketPriceIndicator, tradeNumber }, bytes)

@[simp] theorem encode_length (message : SwapFutureTradeCancellationMessage) : (encode message).length = 53 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length, ExpiryMonthSwapFuture.encode_length, FixedRateFractionPair.encode_length, TradePriceFractionPair.encode_length, MarketPriceIndicator.encode_length]

theorem encode_length_pos (message : SwapFutureTradeCancellationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SwapFutureTradeCancellationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExpiryMonthSwapFuture.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FixedRateFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradePriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketPriceIndicator.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SwapFutureTradeCancellationMessage

/-- Maximum Threshold Price Options Fraction Pair: 7 bytes -/
structure MaximumThresholdPriceOptionsFractionPair where
  rawMaximumThresholdPriceOptions : Alpha 6
  maximumThresholdPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace MaximumThresholdPriceOptionsFractionPair

def encode (message : MaximumThresholdPriceOptionsFractionPair) : List UInt8 :=
  Alpha.encode message.rawMaximumThresholdPriceOptions
    ++ (encodeUInt 1 message.maximumThresholdPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (MaximumThresholdPriceOptionsFractionPair × List UInt8) := do
  let (rawMaximumThresholdPriceOptions, bytes) ← Alpha.decode 6 bytes
  let (maximumThresholdPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawMaximumThresholdPriceOptions, maximumThresholdPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : MaximumThresholdPriceOptionsFractionPair) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : MaximumThresholdPriceOptionsFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MaximumThresholdPriceOptionsFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MaximumThresholdPriceOptionsFractionPair

/-- Minimum Threshold Price Options Fraction Pair: 7 bytes -/
structure MinimumThresholdPriceOptionsFractionPair where
  rawMinimumThresholdPriceOptions : Alpha 6
  minimumThresholdPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace MinimumThresholdPriceOptionsFractionPair

def encode (message : MinimumThresholdPriceOptionsFractionPair) : List UInt8 :=
  Alpha.encode message.rawMinimumThresholdPriceOptions
    ++ (encodeUInt 1 message.minimumThresholdPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (MinimumThresholdPriceOptionsFractionPair × List UInt8) := do
  let (rawMinimumThresholdPriceOptions, bytes) ← Alpha.decode 6 bytes
  let (minimumThresholdPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawMinimumThresholdPriceOptions, minimumThresholdPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : MinimumThresholdPriceOptionsFractionPair) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : MinimumThresholdPriceOptionsFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MinimumThresholdPriceOptionsFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MinimumThresholdPriceOptionsFractionPair

/-- Tick Increment: 7 bytes -/
structure TickIncrement where
  tickIncrementNumeric : Alpha 6
  tickIncrementFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace TickIncrement

def encode (message : TickIncrement) : List UInt8 :=
  Alpha.encode message.tickIncrementNumeric
    ++ (encodeUInt 1 message.tickIncrementFractionIndicator)

def decode (bytes : List UInt8) : Option (TickIncrement × List UInt8) := do
  let (tickIncrementNumeric, bytes) ← Alpha.decode 6 bytes
  let (tickIncrementFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ tickIncrementNumeric, tickIncrementFractionIndicator }, bytes)

@[simp] theorem encode_length (message : TickIncrement) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : TickIncrement) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TickIncrement) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TickIncrement

/-- Tick Value Fraction Pair: 7 bytes -/
structure TickValueFractionPair where
  rawTickValue : Alpha 6
  tickValueFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace TickValueFractionPair

def encode (message : TickValueFractionPair) : List UInt8 :=
  Alpha.encode message.rawTickValue
    ++ (encodeUInt 1 message.tickValueFractionIndicator)

def decode (bytes : List UInt8) : Option (TickValueFractionPair × List UInt8) := do
  let (rawTickValue, bytes) ← Alpha.decode 6 bytes
  let (tickValueFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawTickValue, tickValueFractionIndicator }, bytes)

@[simp] theorem encode_length (message : TickValueFractionPair) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : TickValueFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TickValueFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TickValueFractionPair

/-- Option Instrument Keys Message: 127 bytes -/
structure OptionInstrumentKeysMessage where
  exchangeId : ExchangeId
  rootSymbol : Alpha 6
  expiryMonth : ExpiryMonth
  filler1 : Alpha 1
  strikePriceInstrumentFractionPair : StrikePriceInstrumentFractionPair
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  strikePriceCurrency : Alpha 3
  maximumNumberOfContractsPerOrder : Alpha 6
  minimumNumberOfContractsPerOrder : Alpha 6
  maximumThresholdPriceOptionsFractionPair : MaximumThresholdPriceOptionsFractionPair
  minimumThresholdPriceOptionsFractionPair : MinimumThresholdPriceOptionsFractionPair
  tickIncrement : TickIncrement
  optionType : OptionType
  marketFlowIndicator : Alpha 2
  groupInstrument : Alpha 2
  instrument : Alpha 4
  instrumentExternalCode : Alpha 30
  optionMarker : Alpha 2
  underlyingSymbolRootOptions : Alpha 10
  contractSize : Alpha 8
  tickValueFractionPair : TickValueFractionPair
  currency : Alpha 3
  deliveryType : DeliveryType
  deriving DecidableEq, Repr

namespace OptionInstrumentKeysMessage

def encode (message : OptionInstrumentKeysMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (ExpiryMonth.encode message.expiryMonth
    ++ (Alpha.encode message.filler1
    ++ (StrikePriceInstrumentFractionPair.encode message.strikePriceInstrumentFractionPair
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay
    ++ (Alpha.encode message.strikePriceCurrency
    ++ (Alpha.encode message.maximumNumberOfContractsPerOrder
    ++ (Alpha.encode message.minimumNumberOfContractsPerOrder
    ++ (MaximumThresholdPriceOptionsFractionPair.encode message.maximumThresholdPriceOptionsFractionPair
    ++ (MinimumThresholdPriceOptionsFractionPair.encode message.minimumThresholdPriceOptionsFractionPair
    ++ (TickIncrement.encode message.tickIncrement
    ++ (OptionType.encode message.optionType
    ++ (Alpha.encode message.marketFlowIndicator
    ++ (Alpha.encode message.groupInstrument
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.instrumentExternalCode
    ++ (Alpha.encode message.optionMarker
    ++ (Alpha.encode message.underlyingSymbolRootOptions
    ++ (Alpha.encode message.contractSize
    ++ (TickValueFractionPair.encode message.tickValueFractionPair
    ++ (Alpha.encode message.currency
    ++ (DeliveryType.encode message.deliveryType)))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (OptionInstrumentKeysMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (expiryMonth, bytes) ← ExpiryMonth.decode bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (strikePriceInstrumentFractionPair, bytes) ← StrikePriceInstrumentFractionPair.decode bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (strikePriceCurrency, bytes) ← Alpha.decode 3 bytes
  let (maximumNumberOfContractsPerOrder, bytes) ← Alpha.decode 6 bytes
  let (minimumNumberOfContractsPerOrder, bytes) ← Alpha.decode 6 bytes
  let (maximumThresholdPriceOptionsFractionPair, bytes) ← MaximumThresholdPriceOptionsFractionPair.decode bytes
  let (minimumThresholdPriceOptionsFractionPair, bytes) ← MinimumThresholdPriceOptionsFractionPair.decode bytes
  let (tickIncrement, bytes) ← TickIncrement.decode bytes
  let (optionType, bytes) ← OptionType.decode bytes
  let (marketFlowIndicator, bytes) ← Alpha.decode 2 bytes
  let (groupInstrument, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (instrumentExternalCode, bytes) ← Alpha.decode 30 bytes
  let (optionMarker, bytes) ← Alpha.decode 2 bytes
  let (underlyingSymbolRootOptions, bytes) ← Alpha.decode 10 bytes
  let (contractSize, bytes) ← Alpha.decode 8 bytes
  let (tickValueFractionPair, bytes) ← TickValueFractionPair.decode bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (deliveryType, bytes) ← DeliveryType.decode bytes
  pure ({ exchangeId, rootSymbol, expiryMonth, filler1, strikePriceInstrumentFractionPair, expiryYear, expiryDay, strikePriceCurrency, maximumNumberOfContractsPerOrder, minimumNumberOfContractsPerOrder, maximumThresholdPriceOptionsFractionPair, minimumThresholdPriceOptionsFractionPair, tickIncrement, optionType, marketFlowIndicator, groupInstrument, instrument, instrumentExternalCode, optionMarker, underlyingSymbolRootOptions, contractSize, tickValueFractionPair, currency, deliveryType }, bytes)

@[simp] theorem encode_length (message : OptionInstrumentKeysMessage) : (encode message).length = 127 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length, ExpiryMonth.encode_length, StrikePriceInstrumentFractionPair.encode_length, MaximumThresholdPriceOptionsFractionPair.encode_length, MinimumThresholdPriceOptionsFractionPair.encode_length, TickIncrement.encode_length, OptionType.encode_length, TickValueFractionPair.encode_length, DeliveryType.encode_length]

theorem encode_length_pos (message : OptionInstrumentKeysMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionInstrumentKeysMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExpiryMonth.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StrikePriceInstrumentFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MaximumThresholdPriceOptionsFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MinimumThresholdPriceOptionsFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TickIncrement.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OptionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TickValueFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [DeliveryType.decode_encode, some_bind]
  rfl

end OptionInstrumentKeysMessage

/-- Future Options Instrument Keys Message: 114 bytes -/
structure FutureOptionsInstrumentKeysMessage where
  exchangeId : ExchangeId
  rootSymbol : Alpha 6
  contractMonthCode : ContractMonthCode
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  callPutCode : CallPutCode
  strikePriceInstrumentFractionPair : StrikePriceInstrumentFractionPair
  strikePriceCurrency : Alpha 3
  maximumNumberOfContractsPerOrder : Alpha 6
  minimumNumberOfContractsPerOrder : Alpha 6
  maximumThresholdPriceOptionsFractionPair : MaximumThresholdPriceOptionsFractionPair
  minimumThresholdPriceOptionsFractionPair : MinimumThresholdPriceOptionsFractionPair
  tickIncrement : TickIncrement
  marketFlowIndicator : Alpha 2
  groupInstrument : Alpha 2
  instrument : Alpha 4
  instrumentExternalCode : Alpha 30
  contractSize : Alpha 8
  tickValueFractionPair : TickValueFractionPair
  currency : Alpha 3
  deliveryType : DeliveryType
  deriving DecidableEq, Repr

namespace FutureOptionsInstrumentKeysMessage

def encode (message : FutureOptionsInstrumentKeysMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (ContractMonthCode.encode message.contractMonthCode
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay
    ++ (CallPutCode.encode message.callPutCode
    ++ (StrikePriceInstrumentFractionPair.encode message.strikePriceInstrumentFractionPair
    ++ (Alpha.encode message.strikePriceCurrency
    ++ (Alpha.encode message.maximumNumberOfContractsPerOrder
    ++ (Alpha.encode message.minimumNumberOfContractsPerOrder
    ++ (MaximumThresholdPriceOptionsFractionPair.encode message.maximumThresholdPriceOptionsFractionPair
    ++ (MinimumThresholdPriceOptionsFractionPair.encode message.minimumThresholdPriceOptionsFractionPair
    ++ (TickIncrement.encode message.tickIncrement
    ++ (Alpha.encode message.marketFlowIndicator
    ++ (Alpha.encode message.groupInstrument
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.instrumentExternalCode
    ++ (Alpha.encode message.contractSize
    ++ (TickValueFractionPair.encode message.tickValueFractionPair
    ++ (Alpha.encode message.currency
    ++ (DeliveryType.encode message.deliveryType))))))))))))))))))))

def decode (bytes : List UInt8) : Option (FutureOptionsInstrumentKeysMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (contractMonthCode, bytes) ← ContractMonthCode.decode bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (callPutCode, bytes) ← CallPutCode.decode bytes
  let (strikePriceInstrumentFractionPair, bytes) ← StrikePriceInstrumentFractionPair.decode bytes
  let (strikePriceCurrency, bytes) ← Alpha.decode 3 bytes
  let (maximumNumberOfContractsPerOrder, bytes) ← Alpha.decode 6 bytes
  let (minimumNumberOfContractsPerOrder, bytes) ← Alpha.decode 6 bytes
  let (maximumThresholdPriceOptionsFractionPair, bytes) ← MaximumThresholdPriceOptionsFractionPair.decode bytes
  let (minimumThresholdPriceOptionsFractionPair, bytes) ← MinimumThresholdPriceOptionsFractionPair.decode bytes
  let (tickIncrement, bytes) ← TickIncrement.decode bytes
  let (marketFlowIndicator, bytes) ← Alpha.decode 2 bytes
  let (groupInstrument, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (instrumentExternalCode, bytes) ← Alpha.decode 30 bytes
  let (contractSize, bytes) ← Alpha.decode 8 bytes
  let (tickValueFractionPair, bytes) ← TickValueFractionPair.decode bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (deliveryType, bytes) ← DeliveryType.decode bytes
  pure ({ exchangeId, rootSymbol, contractMonthCode, expiryYear, expiryDay, callPutCode, strikePriceInstrumentFractionPair, strikePriceCurrency, maximumNumberOfContractsPerOrder, minimumNumberOfContractsPerOrder, maximumThresholdPriceOptionsFractionPair, minimumThresholdPriceOptionsFractionPair, tickIncrement, marketFlowIndicator, groupInstrument, instrument, instrumentExternalCode, contractSize, tickValueFractionPair, currency, deliveryType }, bytes)

@[simp] theorem encode_length (message : FutureOptionsInstrumentKeysMessage) : (encode message).length = 114 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length, ContractMonthCode.encode_length, CallPutCode.encode_length, StrikePriceInstrumentFractionPair.encode_length, MaximumThresholdPriceOptionsFractionPair.encode_length, MinimumThresholdPriceOptionsFractionPair.encode_length, TickIncrement.encode_length, TickValueFractionPair.encode_length, DeliveryType.encode_length]

theorem encode_length_pos (message : FutureOptionsInstrumentKeysMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FutureOptionsInstrumentKeysMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ContractMonthCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CallPutCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StrikePriceInstrumentFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MaximumThresholdPriceOptionsFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MinimumThresholdPriceOptionsFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TickIncrement.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TickValueFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [DeliveryType.decode_encode, some_bind]
  rfl

end FutureOptionsInstrumentKeysMessage

/-- Underlying Instrument Keys Message: 37 bytes -/
structure UnderlyingInstrumentKeysMessage where
  exchangeId : ExchangeId
  groupInstrument : Alpha 2
  instrument : Alpha 4
  instrumentExternalCode : Alpha 30
  deriving DecidableEq, Repr

namespace UnderlyingInstrumentKeysMessage

def encode (message : UnderlyingInstrumentKeysMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.groupInstrument
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.instrumentExternalCode)))

def decode (bytes : List UInt8) : Option (UnderlyingInstrumentKeysMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (groupInstrument, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (instrumentExternalCode, bytes) ← Alpha.decode 30 bytes
  pure ({ exchangeId, groupInstrument, instrument, instrumentExternalCode }, bytes)

@[simp] theorem encode_length (message : UnderlyingInstrumentKeysMessage) : (encode message).length = 37 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : UnderlyingInstrumentKeysMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UnderlyingInstrumentKeysMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end UnderlyingInstrumentKeysMessage

/-- Maximum Threshold Price Futures Fraction Pair: 7 bytes -/
structure MaximumThresholdPriceFuturesFractionPair where
  rawMaximumThresholdPriceFutures : Alpha 6
  maximumThresholdPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace MaximumThresholdPriceFuturesFractionPair

def encode (message : MaximumThresholdPriceFuturesFractionPair) : List UInt8 :=
  Alpha.encode message.rawMaximumThresholdPriceFutures
    ++ (encodeUInt 1 message.maximumThresholdPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (MaximumThresholdPriceFuturesFractionPair × List UInt8) := do
  let (rawMaximumThresholdPriceFutures, bytes) ← Alpha.decode 6 bytes
  let (maximumThresholdPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawMaximumThresholdPriceFutures, maximumThresholdPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : MaximumThresholdPriceFuturesFractionPair) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : MaximumThresholdPriceFuturesFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MaximumThresholdPriceFuturesFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MaximumThresholdPriceFuturesFractionPair

/-- Minimum Threshold Price Futures Fraction Pair: 7 bytes -/
structure MinimumThresholdPriceFuturesFractionPair where
  rawMinimumThresholdPriceFutures : Alpha 6
  minimumThresholdPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace MinimumThresholdPriceFuturesFractionPair

def encode (message : MinimumThresholdPriceFuturesFractionPair) : List UInt8 :=
  Alpha.encode message.rawMinimumThresholdPriceFutures
    ++ (encodeUInt 1 message.minimumThresholdPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (MinimumThresholdPriceFuturesFractionPair × List UInt8) := do
  let (rawMinimumThresholdPriceFutures, bytes) ← Alpha.decode 6 bytes
  let (minimumThresholdPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawMinimumThresholdPriceFutures, minimumThresholdPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : MinimumThresholdPriceFuturesFractionPair) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : MinimumThresholdPriceFuturesFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MinimumThresholdPriceFuturesFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MinimumThresholdPriceFuturesFractionPair

/-- Futures Instrument Keys Message: 123 bytes -/
structure FuturesInstrumentKeysMessage where
  exchangeId : ExchangeId
  rootSymbol : Alpha 6
  deliveryMonth : DeliveryMonth
  deliveryYearFutures : Alpha 2
  expiryDay : Alpha 2
  maximumNumberOfContractsPerOrder : Alpha 6
  minimumNumberOfContractsPerOrder : Alpha 6
  maximumThresholdPriceFuturesFractionPair : MaximumThresholdPriceFuturesFractionPair
  minimumThresholdPriceFuturesFractionPair : MinimumThresholdPriceFuturesFractionPair
  tickIncrement : TickIncrement
  marketFlowIndicator : Alpha 2
  groupInstrument : Alpha 2
  instrument : Alpha 4
  instrumentExternalCode : Alpha 30
  contractSize : Alpha 8
  tickValueFractionPair : TickValueFractionPair
  currency : Alpha 3
  underlyingSymbol : Alpha 10
  deliveryType : DeliveryType
  associatedProductRootSymbol : Alpha 6
  associatedProductDeliveryMonth : AssociatedProductDeliveryMonth
  associatedProductDeliveryYear : Alpha 2
  associatedProductExpiryDay : Alpha 2
  deriving DecidableEq, Repr

namespace FuturesInstrumentKeysMessage

def encode (message : FuturesInstrumentKeysMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (DeliveryMonth.encode message.deliveryMonth
    ++ (Alpha.encode message.deliveryYearFutures
    ++ (Alpha.encode message.expiryDay
    ++ (Alpha.encode message.maximumNumberOfContractsPerOrder
    ++ (Alpha.encode message.minimumNumberOfContractsPerOrder
    ++ (MaximumThresholdPriceFuturesFractionPair.encode message.maximumThresholdPriceFuturesFractionPair
    ++ (MinimumThresholdPriceFuturesFractionPair.encode message.minimumThresholdPriceFuturesFractionPair
    ++ (TickIncrement.encode message.tickIncrement
    ++ (Alpha.encode message.marketFlowIndicator
    ++ (Alpha.encode message.groupInstrument
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.instrumentExternalCode
    ++ (Alpha.encode message.contractSize
    ++ (TickValueFractionPair.encode message.tickValueFractionPair
    ++ (Alpha.encode message.currency
    ++ (Alpha.encode message.underlyingSymbol
    ++ (DeliveryType.encode message.deliveryType
    ++ (Alpha.encode message.associatedProductRootSymbol
    ++ (AssociatedProductDeliveryMonth.encode message.associatedProductDeliveryMonth
    ++ (Alpha.encode message.associatedProductDeliveryYear
    ++ (Alpha.encode message.associatedProductExpiryDay))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (FuturesInstrumentKeysMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (deliveryMonth, bytes) ← DeliveryMonth.decode bytes
  let (deliveryYearFutures, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (maximumNumberOfContractsPerOrder, bytes) ← Alpha.decode 6 bytes
  let (minimumNumberOfContractsPerOrder, bytes) ← Alpha.decode 6 bytes
  let (maximumThresholdPriceFuturesFractionPair, bytes) ← MaximumThresholdPriceFuturesFractionPair.decode bytes
  let (minimumThresholdPriceFuturesFractionPair, bytes) ← MinimumThresholdPriceFuturesFractionPair.decode bytes
  let (tickIncrement, bytes) ← TickIncrement.decode bytes
  let (marketFlowIndicator, bytes) ← Alpha.decode 2 bytes
  let (groupInstrument, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (instrumentExternalCode, bytes) ← Alpha.decode 30 bytes
  let (contractSize, bytes) ← Alpha.decode 8 bytes
  let (tickValueFractionPair, bytes) ← TickValueFractionPair.decode bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 10 bytes
  let (deliveryType, bytes) ← DeliveryType.decode bytes
  let (associatedProductRootSymbol, bytes) ← Alpha.decode 6 bytes
  let (associatedProductDeliveryMonth, bytes) ← AssociatedProductDeliveryMonth.decode bytes
  let (associatedProductDeliveryYear, bytes) ← Alpha.decode 2 bytes
  let (associatedProductExpiryDay, bytes) ← Alpha.decode 2 bytes
  pure ({ exchangeId, rootSymbol, deliveryMonth, deliveryYearFutures, expiryDay, maximumNumberOfContractsPerOrder, minimumNumberOfContractsPerOrder, maximumThresholdPriceFuturesFractionPair, minimumThresholdPriceFuturesFractionPair, tickIncrement, marketFlowIndicator, groupInstrument, instrument, instrumentExternalCode, contractSize, tickValueFractionPair, currency, underlyingSymbol, deliveryType, associatedProductRootSymbol, associatedProductDeliveryMonth, associatedProductDeliveryYear, associatedProductExpiryDay }, bytes)

@[simp] theorem encode_length (message : FuturesInstrumentKeysMessage) : (encode message).length = 123 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length, DeliveryMonth.encode_length, MaximumThresholdPriceFuturesFractionPair.encode_length, MinimumThresholdPriceFuturesFractionPair.encode_length, TickIncrement.encode_length, TickValueFractionPair.encode_length, DeliveryType.encode_length, AssociatedProductDeliveryMonth.encode_length]

theorem encode_length_pos (message : FuturesInstrumentKeysMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FuturesInstrumentKeysMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DeliveryMonth.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MaximumThresholdPriceFuturesFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MinimumThresholdPriceFuturesFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TickIncrement.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TickValueFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DeliveryType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AssociatedProductDeliveryMonth.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FuturesInstrumentKeysMessage

/-- Strategy Instrument Keys Message: 108 bytes -/
structure StrategyInstrumentKeysMessage where
  exchangeId : ExchangeId
  strategySymbol : Alpha 30
  expiryYear : Alpha 2
  deliveryMonthStrategy : Alpha 1
  expiryDay : Alpha 2
  maximumNumberOfContractsPerOrder : Alpha 6
  minimumNumberOfContractsPerOrder : Alpha 6
  maximumThresholdPriceOptionsFractionPair : MaximumThresholdPriceOptionsFractionPair
  minimumThresholdPriceOptionsFractionPair : MinimumThresholdPriceOptionsFractionPair
  tickIncrement : TickIncrement
  marketFlowIndicator : Alpha 2
  groupInstrument : Alpha 2
  instrument : Alpha 4
  instrumentExternalCode : Alpha 30
  strategyAllowImplied : StrategyAllowImplied
  deriving DecidableEq, Repr

namespace StrategyInstrumentKeysMessage

def encode (message : StrategyInstrumentKeysMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.strategySymbol
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.deliveryMonthStrategy
    ++ (Alpha.encode message.expiryDay
    ++ (Alpha.encode message.maximumNumberOfContractsPerOrder
    ++ (Alpha.encode message.minimumNumberOfContractsPerOrder
    ++ (MaximumThresholdPriceOptionsFractionPair.encode message.maximumThresholdPriceOptionsFractionPair
    ++ (MinimumThresholdPriceOptionsFractionPair.encode message.minimumThresholdPriceOptionsFractionPair
    ++ (TickIncrement.encode message.tickIncrement
    ++ (Alpha.encode message.marketFlowIndicator
    ++ (Alpha.encode message.groupInstrument
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.instrumentExternalCode
    ++ (StrategyAllowImplied.encode message.strategyAllowImplied))))))))))))))

def decode (bytes : List UInt8) : Option (StrategyInstrumentKeysMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (strategySymbol, bytes) ← Alpha.decode 30 bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (deliveryMonthStrategy, bytes) ← Alpha.decode 1 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (maximumNumberOfContractsPerOrder, bytes) ← Alpha.decode 6 bytes
  let (minimumNumberOfContractsPerOrder, bytes) ← Alpha.decode 6 bytes
  let (maximumThresholdPriceOptionsFractionPair, bytes) ← MaximumThresholdPriceOptionsFractionPair.decode bytes
  let (minimumThresholdPriceOptionsFractionPair, bytes) ← MinimumThresholdPriceOptionsFractionPair.decode bytes
  let (tickIncrement, bytes) ← TickIncrement.decode bytes
  let (marketFlowIndicator, bytes) ← Alpha.decode 2 bytes
  let (groupInstrument, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (instrumentExternalCode, bytes) ← Alpha.decode 30 bytes
  let (strategyAllowImplied, bytes) ← StrategyAllowImplied.decode bytes
  pure ({ exchangeId, strategySymbol, expiryYear, deliveryMonthStrategy, expiryDay, maximumNumberOfContractsPerOrder, minimumNumberOfContractsPerOrder, maximumThresholdPriceOptionsFractionPair, minimumThresholdPriceOptionsFractionPair, tickIncrement, marketFlowIndicator, groupInstrument, instrument, instrumentExternalCode, strategyAllowImplied }, bytes)

@[simp] theorem encode_length (message : StrategyInstrumentKeysMessage) : (encode message).length = 108 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length, MaximumThresholdPriceOptionsFractionPair.encode_length, MinimumThresholdPriceOptionsFractionPair.encode_length, TickIncrement.encode_length, StrategyAllowImplied.encode_length]

theorem encode_length_pos (message : StrategyInstrumentKeysMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyInstrumentKeysMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MaximumThresholdPriceOptionsFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MinimumThresholdPriceOptionsFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TickIncrement.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [StrategyAllowImplied.decode_encode, some_bind]
  rfl

end StrategyInstrumentKeysMessage

/-- Notional Principal Amount Fraction Pair: 9 bytes -/
structure NotionalPrincipalAmountFractionPair where
  rawNotionalPrincipalAmount : Alpha 8
  notionalPrincipalAmountFactionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace NotionalPrincipalAmountFractionPair

def encode (message : NotionalPrincipalAmountFractionPair) : List UInt8 :=
  Alpha.encode message.rawNotionalPrincipalAmount
    ++ (encodeUInt 1 message.notionalPrincipalAmountFactionIndicator)

def decode (bytes : List UInt8) : Option (NotionalPrincipalAmountFractionPair × List UInt8) := do
  let (rawNotionalPrincipalAmount, bytes) ← Alpha.decode 8 bytes
  let (notionalPrincipalAmountFactionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawNotionalPrincipalAmount, notionalPrincipalAmountFactionIndicator }, bytes)

@[simp] theorem encode_length (message : NotionalPrincipalAmountFractionPair) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : NotionalPrincipalAmountFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NotionalPrincipalAmountFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end NotionalPrincipalAmountFractionPair

/-- Swap Future Instrument Keys Message: 172 bytes -/
structure SwapFutureInstrumentKeysMessage where
  exchangeId : ExchangeId
  rootSymbol : Alpha 6
  expiryMonthSwapFuture : ExpiryMonthSwapFuture
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  tenor : Alpha 2
  fixedRateFractionPair : FixedRateFractionPair
  maximumNumberOfContractsPerOrder : Alpha 6
  minimumNumberOfContractsPerOrder : Alpha 6
  maximumThresholdPriceOptionsFractionPair : MaximumThresholdPriceOptionsFractionPair
  minimumThresholdPriceOptionsFractionPair : MinimumThresholdPriceOptionsFractionPair
  tickIncrement : TickIncrement
  marketFlow : Alpha 2
  groupInstrument : Alpha 2
  instrumentId : Alpha 4
  externalSymbol : Alpha 30
  contractSize : Alpha 8
  tickValueFractionPair : TickValueFractionPair
  currency : Alpha 3
  effectiveDate : Alpha 6
  initialEffectiveDate : Alpha 6
  cashFlowAlignmentDate : Alpha 6
  paymentFrequency : Alpha 2
  resetFrequency : Alpha 2
  notionalPrincipalAmountFractionPair : NotionalPrincipalAmountFractionPair
  dayCountConvention : DayCountConvention
  firstPaymentDate : Alpha 6
  nextPaymentDate : Alpha 6
  firstResetDate : Alpha 6
  nextResetDate : Alpha 6
  previousResetDate : Alpha 6
  deliveryType : DeliveryType
  deriving DecidableEq, Repr

namespace SwapFutureInstrumentKeysMessage

def encode (message : SwapFutureInstrumentKeysMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (ExpiryMonthSwapFuture.encode message.expiryMonthSwapFuture
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay
    ++ (Alpha.encode message.tenor
    ++ (FixedRateFractionPair.encode message.fixedRateFractionPair
    ++ (Alpha.encode message.maximumNumberOfContractsPerOrder
    ++ (Alpha.encode message.minimumNumberOfContractsPerOrder
    ++ (MaximumThresholdPriceOptionsFractionPair.encode message.maximumThresholdPriceOptionsFractionPair
    ++ (MinimumThresholdPriceOptionsFractionPair.encode message.minimumThresholdPriceOptionsFractionPair
    ++ (TickIncrement.encode message.tickIncrement
    ++ (Alpha.encode message.marketFlow
    ++ (Alpha.encode message.groupInstrument
    ++ (Alpha.encode message.instrumentId
    ++ (Alpha.encode message.externalSymbol
    ++ (Alpha.encode message.contractSize
    ++ (TickValueFractionPair.encode message.tickValueFractionPair
    ++ (Alpha.encode message.currency
    ++ (Alpha.encode message.effectiveDate
    ++ (Alpha.encode message.initialEffectiveDate
    ++ (Alpha.encode message.cashFlowAlignmentDate
    ++ (Alpha.encode message.paymentFrequency
    ++ (Alpha.encode message.resetFrequency
    ++ (NotionalPrincipalAmountFractionPair.encode message.notionalPrincipalAmountFractionPair
    ++ (DayCountConvention.encode message.dayCountConvention
    ++ (Alpha.encode message.firstPaymentDate
    ++ (Alpha.encode message.nextPaymentDate
    ++ (Alpha.encode message.firstResetDate
    ++ (Alpha.encode message.nextResetDate
    ++ (Alpha.encode message.previousResetDate
    ++ (DeliveryType.encode message.deliveryType)))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SwapFutureInstrumentKeysMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (expiryMonthSwapFuture, bytes) ← ExpiryMonthSwapFuture.decode bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (tenor, bytes) ← Alpha.decode 2 bytes
  let (fixedRateFractionPair, bytes) ← FixedRateFractionPair.decode bytes
  let (maximumNumberOfContractsPerOrder, bytes) ← Alpha.decode 6 bytes
  let (minimumNumberOfContractsPerOrder, bytes) ← Alpha.decode 6 bytes
  let (maximumThresholdPriceOptionsFractionPair, bytes) ← MaximumThresholdPriceOptionsFractionPair.decode bytes
  let (minimumThresholdPriceOptionsFractionPair, bytes) ← MinimumThresholdPriceOptionsFractionPair.decode bytes
  let (tickIncrement, bytes) ← TickIncrement.decode bytes
  let (marketFlow, bytes) ← Alpha.decode 2 bytes
  let (groupInstrument, bytes) ← Alpha.decode 2 bytes
  let (instrumentId, bytes) ← Alpha.decode 4 bytes
  let (externalSymbol, bytes) ← Alpha.decode 30 bytes
  let (contractSize, bytes) ← Alpha.decode 8 bytes
  let (tickValueFractionPair, bytes) ← TickValueFractionPair.decode bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (effectiveDate, bytes) ← Alpha.decode 6 bytes
  let (initialEffectiveDate, bytes) ← Alpha.decode 6 bytes
  let (cashFlowAlignmentDate, bytes) ← Alpha.decode 6 bytes
  let (paymentFrequency, bytes) ← Alpha.decode 2 bytes
  let (resetFrequency, bytes) ← Alpha.decode 2 bytes
  let (notionalPrincipalAmountFractionPair, bytes) ← NotionalPrincipalAmountFractionPair.decode bytes
  let (dayCountConvention, bytes) ← DayCountConvention.decode bytes
  let (firstPaymentDate, bytes) ← Alpha.decode 6 bytes
  let (nextPaymentDate, bytes) ← Alpha.decode 6 bytes
  let (firstResetDate, bytes) ← Alpha.decode 6 bytes
  let (nextResetDate, bytes) ← Alpha.decode 6 bytes
  let (previousResetDate, bytes) ← Alpha.decode 6 bytes
  let (deliveryType, bytes) ← DeliveryType.decode bytes
  pure ({ exchangeId, rootSymbol, expiryMonthSwapFuture, expiryYear, expiryDay, tenor, fixedRateFractionPair, maximumNumberOfContractsPerOrder, minimumNumberOfContractsPerOrder, maximumThresholdPriceOptionsFractionPair, minimumThresholdPriceOptionsFractionPair, tickIncrement, marketFlow, groupInstrument, instrumentId, externalSymbol, contractSize, tickValueFractionPair, currency, effectiveDate, initialEffectiveDate, cashFlowAlignmentDate, paymentFrequency, resetFrequency, notionalPrincipalAmountFractionPair, dayCountConvention, firstPaymentDate, nextPaymentDate, firstResetDate, nextResetDate, previousResetDate, deliveryType }, bytes)

@[simp] theorem encode_length (message : SwapFutureInstrumentKeysMessage) : (encode message).length = 172 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length, ExpiryMonthSwapFuture.encode_length, FixedRateFractionPair.encode_length, MaximumThresholdPriceOptionsFractionPair.encode_length, MinimumThresholdPriceOptionsFractionPair.encode_length, TickIncrement.encode_length, TickValueFractionPair.encode_length, NotionalPrincipalAmountFractionPair.encode_length, DayCountConvention.encode_length, DeliveryType.encode_length]

theorem encode_length_pos (message : SwapFutureInstrumentKeysMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SwapFutureInstrumentKeysMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExpiryMonthSwapFuture.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FixedRateFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MaximumThresholdPriceOptionsFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MinimumThresholdPriceOptionsFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TickIncrement.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TickValueFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NotionalPrincipalAmountFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DayCountConvention.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [DeliveryType.decode_encode, some_bind]
  rfl

end SwapFutureInstrumentKeysMessage

/-- Bid Price Summary Fraction Pair: 7 bytes -/
structure BidPriceSummaryFractionPair where
  rawBidPriceSummary : Alpha 6
  bidPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace BidPriceSummaryFractionPair

def encode (message : BidPriceSummaryFractionPair) : List UInt8 :=
  Alpha.encode message.rawBidPriceSummary
    ++ (encodeUInt 1 message.bidPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (BidPriceSummaryFractionPair × List UInt8) := do
  let (rawBidPriceSummary, bytes) ← Alpha.decode 6 bytes
  let (bidPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawBidPriceSummary, bidPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : BidPriceSummaryFractionPair) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : BidPriceSummaryFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BidPriceSummaryFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end BidPriceSummaryFractionPair

/-- Ask Price Summary Fraction Pair: 7 bytes -/
structure AskPriceSummaryFractionPair where
  rawAskPriceSummary : Alpha 6
  askPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace AskPriceSummaryFractionPair

def encode (message : AskPriceSummaryFractionPair) : List UInt8 :=
  Alpha.encode message.rawAskPriceSummary
    ++ (encodeUInt 1 message.askPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (AskPriceSummaryFractionPair × List UInt8) := do
  let (rawAskPriceSummary, bytes) ← Alpha.decode 6 bytes
  let (askPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawAskPriceSummary, askPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : AskPriceSummaryFractionPair) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : AskPriceSummaryFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AskPriceSummaryFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end AskPriceSummaryFractionPair

/-- Last Price Fraction Pair: 7 bytes -/
structure LastPriceFractionPair where
  rawLastPrice : Alpha 6
  lastPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace LastPriceFractionPair

def encode (message : LastPriceFractionPair) : List UInt8 :=
  Alpha.encode message.rawLastPrice
    ++ (encodeUInt 1 message.lastPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (LastPriceFractionPair × List UInt8) := do
  let (rawLastPrice, bytes) ← Alpha.decode 6 bytes
  let (lastPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawLastPrice, lastPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : LastPriceFractionPair) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : LastPriceFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LastPriceFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end LastPriceFractionPair

/-- Open Price Fraction Pair: 7 bytes -/
structure OpenPriceFractionPair where
  rawOpenPrice : Alpha 6
  openPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace OpenPriceFractionPair

def encode (message : OpenPriceFractionPair) : List UInt8 :=
  Alpha.encode message.rawOpenPrice
    ++ (encodeUInt 1 message.openPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (OpenPriceFractionPair × List UInt8) := do
  let (rawOpenPrice, bytes) ← Alpha.decode 6 bytes
  let (openPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawOpenPrice, openPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : OpenPriceFractionPair) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : OpenPriceFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OpenPriceFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OpenPriceFractionPair

/-- High Price Fraction Pair: 7 bytes -/
structure HighPriceFractionPair where
  rawHighPrice : Alpha 6
  highPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace HighPriceFractionPair

def encode (message : HighPriceFractionPair) : List UInt8 :=
  Alpha.encode message.rawHighPrice
    ++ (encodeUInt 1 message.highPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (HighPriceFractionPair × List UInt8) := do
  let (rawHighPrice, bytes) ← Alpha.decode 6 bytes
  let (highPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawHighPrice, highPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : HighPriceFractionPair) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : HighPriceFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : HighPriceFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end HighPriceFractionPair

/-- Low Price Fraction Pair: 7 bytes -/
structure LowPriceFractionPair where
  rawLowPrice : Alpha 6
  lowPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace LowPriceFractionPair

def encode (message : LowPriceFractionPair) : List UInt8 :=
  Alpha.encode message.rawLowPrice
    ++ (encodeUInt 1 message.lowPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (LowPriceFractionPair × List UInt8) := do
  let (rawLowPrice, bytes) ← Alpha.decode 6 bytes
  let (lowPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawLowPrice, lowPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : LowPriceFractionPair) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : LowPriceFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LowPriceFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end LowPriceFractionPair

/-- Settlement Price Fraction Pair: 7 bytes -/
structure SettlementPriceFractionPair where
  rawSettlementPrice : Alpha 6
  settlementPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace SettlementPriceFractionPair

def encode (message : SettlementPriceFractionPair) : List UInt8 :=
  Alpha.encode message.rawSettlementPrice
    ++ (encodeUInt 1 message.settlementPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (SettlementPriceFractionPair × List UInt8) := do
  let (rawSettlementPrice, bytes) ← Alpha.decode 6 bytes
  let (settlementPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawSettlementPrice, settlementPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : SettlementPriceFractionPair) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SettlementPriceFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SettlementPriceFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SettlementPriceFractionPair

/-- Previous Settlement Price Fraction Pair: 7 bytes -/
structure PreviousSettlementPriceFractionPair where
  rawPreviousSettlementPrice : Alpha 6
  previousSettlementPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace PreviousSettlementPriceFractionPair

def encode (message : PreviousSettlementPriceFractionPair) : List UInt8 :=
  Alpha.encode message.rawPreviousSettlementPrice
    ++ (encodeUInt 1 message.previousSettlementPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (PreviousSettlementPriceFractionPair × List UInt8) := do
  let (rawPreviousSettlementPrice, bytes) ← Alpha.decode 6 bytes
  let (previousSettlementPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawPreviousSettlementPrice, previousSettlementPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : PreviousSettlementPriceFractionPair) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : PreviousSettlementPriceFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PreviousSettlementPriceFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end PreviousSettlementPriceFractionPair

/-- Option Summary Message: 124 bytes -/
structure OptionSummaryMessage where
  exchangeId : ExchangeId
  rootSymbol : Alpha 6
  expiryMonth : ExpiryMonth
  filler1 : Alpha 1
  strikePriceInstrumentFractionPair : StrikePriceInstrumentFractionPair
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  bidPriceSummaryFractionPair : BidPriceSummaryFractionPair
  bidSize : Alpha 5
  askPriceSummaryFractionPair : AskPriceSummaryFractionPair
  askSize : Alpha 5
  lastPriceFractionPair : LastPriceFractionPair
  openInterest : Alpha 7
  tick : Tick
  volume : Alpha 8
  netChangeSign : NetChangeSign
  netChangeFractionPair : NetChangeFractionPair
  openPriceFractionPair : OpenPriceFractionPair
  highPriceFractionPair : HighPriceFractionPair
  lowPriceFractionPair : LowPriceFractionPair
  optionMarker : Alpha 2
  underlyingSymbolRootOptions : Alpha 10
  settlementPriceFractionPair : SettlementPriceFractionPair
  previousSettlementPriceFractionPair : PreviousSettlementPriceFractionPair
  reason : Reason
  deriving DecidableEq, Repr

namespace OptionSummaryMessage

def encode (message : OptionSummaryMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (ExpiryMonth.encode message.expiryMonth
    ++ (Alpha.encode message.filler1
    ++ (StrikePriceInstrumentFractionPair.encode message.strikePriceInstrumentFractionPair
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay
    ++ (BidPriceSummaryFractionPair.encode message.bidPriceSummaryFractionPair
    ++ (Alpha.encode message.bidSize
    ++ (AskPriceSummaryFractionPair.encode message.askPriceSummaryFractionPair
    ++ (Alpha.encode message.askSize
    ++ (LastPriceFractionPair.encode message.lastPriceFractionPair
    ++ (Alpha.encode message.openInterest
    ++ (Tick.encode message.tick
    ++ (Alpha.encode message.volume
    ++ (NetChangeSign.encode message.netChangeSign
    ++ (NetChangeFractionPair.encode message.netChangeFractionPair
    ++ (OpenPriceFractionPair.encode message.openPriceFractionPair
    ++ (HighPriceFractionPair.encode message.highPriceFractionPair
    ++ (LowPriceFractionPair.encode message.lowPriceFractionPair
    ++ (Alpha.encode message.optionMarker
    ++ (Alpha.encode message.underlyingSymbolRootOptions
    ++ (SettlementPriceFractionPair.encode message.settlementPriceFractionPair
    ++ (PreviousSettlementPriceFractionPair.encode message.previousSettlementPriceFractionPair
    ++ (Reason.encode message.reason))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OptionSummaryMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (expiryMonth, bytes) ← ExpiryMonth.decode bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (strikePriceInstrumentFractionPair, bytes) ← StrikePriceInstrumentFractionPair.decode bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (bidPriceSummaryFractionPair, bytes) ← BidPriceSummaryFractionPair.decode bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPriceSummaryFractionPair, bytes) ← AskPriceSummaryFractionPair.decode bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (lastPriceFractionPair, bytes) ← LastPriceFractionPair.decode bytes
  let (openInterest, bytes) ← Alpha.decode 7 bytes
  let (tick, bytes) ← Tick.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (netChangeSign, bytes) ← NetChangeSign.decode bytes
  let (netChangeFractionPair, bytes) ← NetChangeFractionPair.decode bytes
  let (openPriceFractionPair, bytes) ← OpenPriceFractionPair.decode bytes
  let (highPriceFractionPair, bytes) ← HighPriceFractionPair.decode bytes
  let (lowPriceFractionPair, bytes) ← LowPriceFractionPair.decode bytes
  let (optionMarker, bytes) ← Alpha.decode 2 bytes
  let (underlyingSymbolRootOptions, bytes) ← Alpha.decode 10 bytes
  let (settlementPriceFractionPair, bytes) ← SettlementPriceFractionPair.decode bytes
  let (previousSettlementPriceFractionPair, bytes) ← PreviousSettlementPriceFractionPair.decode bytes
  let (reason, bytes) ← Reason.decode bytes
  pure ({ exchangeId, rootSymbol, expiryMonth, filler1, strikePriceInstrumentFractionPair, expiryYear, expiryDay, bidPriceSummaryFractionPair, bidSize, askPriceSummaryFractionPair, askSize, lastPriceFractionPair, openInterest, tick, volume, netChangeSign, netChangeFractionPair, openPriceFractionPair, highPriceFractionPair, lowPriceFractionPair, optionMarker, underlyingSymbolRootOptions, settlementPriceFractionPair, previousSettlementPriceFractionPair, reason }, bytes)

@[simp] theorem encode_length (message : OptionSummaryMessage) : (encode message).length = 124 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length, ExpiryMonth.encode_length, StrikePriceInstrumentFractionPair.encode_length, BidPriceSummaryFractionPair.encode_length, AskPriceSummaryFractionPair.encode_length, LastPriceFractionPair.encode_length, Tick.encode_length, NetChangeSign.encode_length, NetChangeFractionPair.encode_length, OpenPriceFractionPair.encode_length, HighPriceFractionPair.encode_length, LowPriceFractionPair.encode_length, SettlementPriceFractionPair.encode_length, PreviousSettlementPriceFractionPair.encode_length, Reason.encode_length]

theorem encode_length_pos (message : OptionSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OptionSummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExpiryMonth.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StrikePriceInstrumentFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BidPriceSummaryFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskPriceSummaryFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LastPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Tick.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpenPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, HighPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LowPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SettlementPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PreviousSettlementPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [Reason.decode_encode, some_bind]
  rfl

end OptionSummaryMessage

/-- Last Price Future Options Summary Message Fraction Pair: 7 bytes -/
structure LastPriceFutureOptionsSummaryMessageFractionPair where
  rawLastPriceFutureOptionsSummaryMessage : Alpha 6
  lastPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace LastPriceFutureOptionsSummaryMessageFractionPair

def encode (message : LastPriceFutureOptionsSummaryMessageFractionPair) : List UInt8 :=
  Alpha.encode message.rawLastPriceFutureOptionsSummaryMessage
    ++ (encodeUInt 1 message.lastPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (LastPriceFutureOptionsSummaryMessageFractionPair × List UInt8) := do
  let (rawLastPriceFutureOptionsSummaryMessage, bytes) ← Alpha.decode 6 bytes
  let (lastPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawLastPriceFutureOptionsSummaryMessage, lastPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : LastPriceFutureOptionsSummaryMessageFractionPair) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : LastPriceFutureOptionsSummaryMessageFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LastPriceFutureOptionsSummaryMessageFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end LastPriceFutureOptionsSummaryMessageFractionPair

/-- Net Change Future Options Summary Message Fraction Pair: 7 bytes -/
structure NetChangeFutureOptionsSummaryMessageFractionPair where
  rawNetChangeFutureOptionsSummaryMessage : Alpha 6
  netChangeFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace NetChangeFutureOptionsSummaryMessageFractionPair

def encode (message : NetChangeFutureOptionsSummaryMessageFractionPair) : List UInt8 :=
  Alpha.encode message.rawNetChangeFutureOptionsSummaryMessage
    ++ (encodeUInt 1 message.netChangeFractionIndicator)

def decode (bytes : List UInt8) : Option (NetChangeFutureOptionsSummaryMessageFractionPair × List UInt8) := do
  let (rawNetChangeFutureOptionsSummaryMessage, bytes) ← Alpha.decode 6 bytes
  let (netChangeFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawNetChangeFutureOptionsSummaryMessage, netChangeFractionIndicator }, bytes)

@[simp] theorem encode_length (message : NetChangeFutureOptionsSummaryMessageFractionPair) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : NetChangeFutureOptionsSummaryMessageFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NetChangeFutureOptionsSummaryMessageFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end NetChangeFutureOptionsSummaryMessageFractionPair

/-- Opening Price Fraction Pair: 7 bytes -/
structure OpeningPriceFractionPair where
  rawOpeningPrice : Alpha 6
  openingPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace OpeningPriceFractionPair

def encode (message : OpeningPriceFractionPair) : List UInt8 :=
  Alpha.encode message.rawOpeningPrice
    ++ (encodeUInt 1 message.openingPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (OpeningPriceFractionPair × List UInt8) := do
  let (rawOpeningPrice, bytes) ← Alpha.decode 6 bytes
  let (openingPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawOpeningPrice, openingPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : OpeningPriceFractionPair) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : OpeningPriceFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OpeningPriceFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OpeningPriceFractionPair

/-- Settlement Price Future Options Summary Message Fraction Pair: 7 bytes -/
structure SettlementPriceFutureOptionsSummaryMessageFractionPair where
  rawSettlementPriceFutureOptionsSummaryMessage : Alpha 6
  settlementPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace SettlementPriceFutureOptionsSummaryMessageFractionPair

def encode (message : SettlementPriceFutureOptionsSummaryMessageFractionPair) : List UInt8 :=
  Alpha.encode message.rawSettlementPriceFutureOptionsSummaryMessage
    ++ (encodeUInt 1 message.settlementPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (SettlementPriceFutureOptionsSummaryMessageFractionPair × List UInt8) := do
  let (rawSettlementPriceFutureOptionsSummaryMessage, bytes) ← Alpha.decode 6 bytes
  let (settlementPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawSettlementPriceFutureOptionsSummaryMessage, settlementPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : SettlementPriceFutureOptionsSummaryMessageFractionPair) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SettlementPriceFutureOptionsSummaryMessageFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SettlementPriceFutureOptionsSummaryMessageFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SettlementPriceFutureOptionsSummaryMessageFractionPair

/-- Future Options Summary Message: 119 bytes -/
structure FutureOptionsSummaryMessage where
  exchangeId : ExchangeId
  rootSymbol : Alpha 6
  contractMonthCode : ContractMonthCode
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  callPutCode : CallPutCode
  strikePriceInstrumentFractionPair : StrikePriceInstrumentFractionPair
  bidPriceSummaryFractionPair : BidPriceSummaryFractionPair
  bidSize : Alpha 5
  askPriceSummaryFractionPair : AskPriceSummaryFractionPair
  askSize : Alpha 5
  lastPriceFutureOptionsSummaryMessageFractionPair : LastPriceFutureOptionsSummaryMessageFractionPair
  openInterest : Alpha 7
  tick : Tick
  volume : Alpha 8
  netChangeSign : NetChangeSign
  netChangeFutureOptionsSummaryMessageFractionPair : NetChangeFutureOptionsSummaryMessageFractionPair
  openingPriceFractionPair : OpeningPriceFractionPair
  highPriceFractionPair : HighPriceFractionPair
  lowPriceFractionPair : LowPriceFractionPair
  filler2 : Alpha 2
  underlyingSymbolRootFutureOptions : Alpha 3
  deliveryMonth : DeliveryMonth
  deliveryYearUnderlying : Alpha 1
  settlementPriceFutureOptionsSummaryMessageFractionPair : SettlementPriceFutureOptionsSummaryMessageFractionPair
  previousSettlementPriceFractionPair : PreviousSettlementPriceFractionPair
  reason : Reason
  deriving DecidableEq, Repr

namespace FutureOptionsSummaryMessage

def encode (message : FutureOptionsSummaryMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (ContractMonthCode.encode message.contractMonthCode
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay
    ++ (CallPutCode.encode message.callPutCode
    ++ (StrikePriceInstrumentFractionPair.encode message.strikePriceInstrumentFractionPair
    ++ (BidPriceSummaryFractionPair.encode message.bidPriceSummaryFractionPair
    ++ (Alpha.encode message.bidSize
    ++ (AskPriceSummaryFractionPair.encode message.askPriceSummaryFractionPair
    ++ (Alpha.encode message.askSize
    ++ (LastPriceFutureOptionsSummaryMessageFractionPair.encode message.lastPriceFutureOptionsSummaryMessageFractionPair
    ++ (Alpha.encode message.openInterest
    ++ (Tick.encode message.tick
    ++ (Alpha.encode message.volume
    ++ (NetChangeSign.encode message.netChangeSign
    ++ (NetChangeFutureOptionsSummaryMessageFractionPair.encode message.netChangeFutureOptionsSummaryMessageFractionPair
    ++ (OpeningPriceFractionPair.encode message.openingPriceFractionPair
    ++ (HighPriceFractionPair.encode message.highPriceFractionPair
    ++ (LowPriceFractionPair.encode message.lowPriceFractionPair
    ++ (Alpha.encode message.filler2
    ++ (Alpha.encode message.underlyingSymbolRootFutureOptions
    ++ (DeliveryMonth.encode message.deliveryMonth
    ++ (Alpha.encode message.deliveryYearUnderlying
    ++ (SettlementPriceFutureOptionsSummaryMessageFractionPair.encode message.settlementPriceFutureOptionsSummaryMessageFractionPair
    ++ (PreviousSettlementPriceFractionPair.encode message.previousSettlementPriceFractionPair
    ++ (Reason.encode message.reason))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (FutureOptionsSummaryMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (contractMonthCode, bytes) ← ContractMonthCode.decode bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (callPutCode, bytes) ← CallPutCode.decode bytes
  let (strikePriceInstrumentFractionPair, bytes) ← StrikePriceInstrumentFractionPair.decode bytes
  let (bidPriceSummaryFractionPair, bytes) ← BidPriceSummaryFractionPair.decode bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPriceSummaryFractionPair, bytes) ← AskPriceSummaryFractionPair.decode bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (lastPriceFutureOptionsSummaryMessageFractionPair, bytes) ← LastPriceFutureOptionsSummaryMessageFractionPair.decode bytes
  let (openInterest, bytes) ← Alpha.decode 7 bytes
  let (tick, bytes) ← Tick.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (netChangeSign, bytes) ← NetChangeSign.decode bytes
  let (netChangeFutureOptionsSummaryMessageFractionPair, bytes) ← NetChangeFutureOptionsSummaryMessageFractionPair.decode bytes
  let (openingPriceFractionPair, bytes) ← OpeningPriceFractionPair.decode bytes
  let (highPriceFractionPair, bytes) ← HighPriceFractionPair.decode bytes
  let (lowPriceFractionPair, bytes) ← LowPriceFractionPair.decode bytes
  let (filler2, bytes) ← Alpha.decode 2 bytes
  let (underlyingSymbolRootFutureOptions, bytes) ← Alpha.decode 3 bytes
  let (deliveryMonth, bytes) ← DeliveryMonth.decode bytes
  let (deliveryYearUnderlying, bytes) ← Alpha.decode 1 bytes
  let (settlementPriceFutureOptionsSummaryMessageFractionPair, bytes) ← SettlementPriceFutureOptionsSummaryMessageFractionPair.decode bytes
  let (previousSettlementPriceFractionPair, bytes) ← PreviousSettlementPriceFractionPair.decode bytes
  let (reason, bytes) ← Reason.decode bytes
  pure ({ exchangeId, rootSymbol, contractMonthCode, expiryYear, expiryDay, callPutCode, strikePriceInstrumentFractionPair, bidPriceSummaryFractionPair, bidSize, askPriceSummaryFractionPair, askSize, lastPriceFutureOptionsSummaryMessageFractionPair, openInterest, tick, volume, netChangeSign, netChangeFutureOptionsSummaryMessageFractionPair, openingPriceFractionPair, highPriceFractionPair, lowPriceFractionPair, filler2, underlyingSymbolRootFutureOptions, deliveryMonth, deliveryYearUnderlying, settlementPriceFutureOptionsSummaryMessageFractionPair, previousSettlementPriceFractionPair, reason }, bytes)

@[simp] theorem encode_length (message : FutureOptionsSummaryMessage) : (encode message).length = 119 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length, ContractMonthCode.encode_length, CallPutCode.encode_length, StrikePriceInstrumentFractionPair.encode_length, BidPriceSummaryFractionPair.encode_length, AskPriceSummaryFractionPair.encode_length, LastPriceFutureOptionsSummaryMessageFractionPair.encode_length, Tick.encode_length, NetChangeSign.encode_length, NetChangeFutureOptionsSummaryMessageFractionPair.encode_length, OpeningPriceFractionPair.encode_length, HighPriceFractionPair.encode_length, LowPriceFractionPair.encode_length, DeliveryMonth.encode_length, SettlementPriceFutureOptionsSummaryMessageFractionPair.encode_length, PreviousSettlementPriceFractionPair.encode_length, Reason.encode_length]

theorem encode_length_pos (message : FutureOptionsSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : FutureOptionsSummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ContractMonthCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CallPutCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StrikePriceInstrumentFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BidPriceSummaryFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskPriceSummaryFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LastPriceFutureOptionsSummaryMessageFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Tick.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeFutureOptionsSummaryMessageFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpeningPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, HighPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LowPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DeliveryMonth.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SettlementPriceFutureOptionsSummaryMessageFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PreviousSettlementPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [Reason.decode_encode, some_bind]
  rfl

end FutureOptionsSummaryMessage

/-- Net Change Futures Summary Message Fraction Pair: 7 bytes -/
structure NetChangeFuturesSummaryMessageFractionPair where
  rawNetChangeFuturesSummaryMessage : Alpha 6
  netChangeFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace NetChangeFuturesSummaryMessageFractionPair

def encode (message : NetChangeFuturesSummaryMessageFractionPair) : List UInt8 :=
  Alpha.encode message.rawNetChangeFuturesSummaryMessage
    ++ (encodeUInt 1 message.netChangeFractionIndicator)

def decode (bytes : List UInt8) : Option (NetChangeFuturesSummaryMessageFractionPair × List UInt8) := do
  let (rawNetChangeFuturesSummaryMessage, bytes) ← Alpha.decode 6 bytes
  let (netChangeFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawNetChangeFuturesSummaryMessage, netChangeFractionIndicator }, bytes)

@[simp] theorem encode_length (message : NetChangeFuturesSummaryMessageFractionPair) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : NetChangeFuturesSummaryMessageFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NetChangeFuturesSummaryMessageFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end NetChangeFuturesSummaryMessageFractionPair

/-- Previous Settlement Fraction Pair: 7 bytes -/
structure PreviousSettlementFractionPair where
  rawPreviousSettlement : Alpha 6
  previousSettlementFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace PreviousSettlementFractionPair

def encode (message : PreviousSettlementFractionPair) : List UInt8 :=
  Alpha.encode message.rawPreviousSettlement
    ++ (encodeUInt 1 message.previousSettlementFractionIndicator)

def decode (bytes : List UInt8) : Option (PreviousSettlementFractionPair × List UInt8) := do
  let (rawPreviousSettlement, bytes) ← Alpha.decode 6 bytes
  let (previousSettlementFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawPreviousSettlement, previousSettlementFractionIndicator }, bytes)

@[simp] theorem encode_length (message : PreviousSettlementFractionPair) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : PreviousSettlementFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PreviousSettlementFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end PreviousSettlementFractionPair

/-- External Price At Source Fraction Pair: 7 bytes -/
structure ExternalPriceAtSourceFractionPair where
  rawExternalPriceAtSource : Alpha 6
  externalPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace ExternalPriceAtSourceFractionPair

def encode (message : ExternalPriceAtSourceFractionPair) : List UInt8 :=
  Alpha.encode message.rawExternalPriceAtSource
    ++ (encodeUInt 1 message.externalPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (ExternalPriceAtSourceFractionPair × List UInt8) := do
  let (rawExternalPriceAtSource, bytes) ← Alpha.decode 6 bytes
  let (externalPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawExternalPriceAtSource, externalPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : ExternalPriceAtSourceFractionPair) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ExternalPriceAtSourceFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExternalPriceAtSourceFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ExternalPriceAtSourceFractionPair

/-- Futures Summary Message: 109 bytes -/
structure FuturesSummaryMessage where
  exchangeId : ExchangeId
  rootSymbol : Alpha 6
  deliveryMonth : DeliveryMonth
  deliveryYearFutures : Alpha 2
  deliveryDay : Alpha 2
  bidPriceSummaryFractionPair : BidPriceSummaryFractionPair
  bidSize : Alpha 5
  askPriceSummaryFractionPair : AskPriceSummaryFractionPair
  askSize : Alpha 5
  lastPriceFractionPair : LastPriceFractionPair
  openPriceFractionPair : OpenPriceFractionPair
  highPriceFractionPair : HighPriceFractionPair
  lowPriceFractionPair : LowPriceFractionPair
  settlementPriceFutureOptionsSummaryMessageFractionPair : SettlementPriceFutureOptionsSummaryMessageFractionPair
  netChangeSign : NetChangeSign
  netChangeFuturesSummaryMessageFractionPair : NetChangeFuturesSummaryMessageFractionPair
  volume : Alpha 8
  previousSettlementFractionPair : PreviousSettlementFractionPair
  openInterest : Alpha 7
  reason : Reason
  externalPriceAtSourceFractionPair : ExternalPriceAtSourceFractionPair
  deriving DecidableEq, Repr

namespace FuturesSummaryMessage

def encode (message : FuturesSummaryMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (DeliveryMonth.encode message.deliveryMonth
    ++ (Alpha.encode message.deliveryYearFutures
    ++ (Alpha.encode message.deliveryDay
    ++ (BidPriceSummaryFractionPair.encode message.bidPriceSummaryFractionPair
    ++ (Alpha.encode message.bidSize
    ++ (AskPriceSummaryFractionPair.encode message.askPriceSummaryFractionPair
    ++ (Alpha.encode message.askSize
    ++ (LastPriceFractionPair.encode message.lastPriceFractionPair
    ++ (OpenPriceFractionPair.encode message.openPriceFractionPair
    ++ (HighPriceFractionPair.encode message.highPriceFractionPair
    ++ (LowPriceFractionPair.encode message.lowPriceFractionPair
    ++ (SettlementPriceFutureOptionsSummaryMessageFractionPair.encode message.settlementPriceFutureOptionsSummaryMessageFractionPair
    ++ (NetChangeSign.encode message.netChangeSign
    ++ (NetChangeFuturesSummaryMessageFractionPair.encode message.netChangeFuturesSummaryMessageFractionPair
    ++ (Alpha.encode message.volume
    ++ (PreviousSettlementFractionPair.encode message.previousSettlementFractionPair
    ++ (Alpha.encode message.openInterest
    ++ (Reason.encode message.reason
    ++ (ExternalPriceAtSourceFractionPair.encode message.externalPriceAtSourceFractionPair))))))))))))))))))))

def decode (bytes : List UInt8) : Option (FuturesSummaryMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (deliveryMonth, bytes) ← DeliveryMonth.decode bytes
  let (deliveryYearFutures, bytes) ← Alpha.decode 2 bytes
  let (deliveryDay, bytes) ← Alpha.decode 2 bytes
  let (bidPriceSummaryFractionPair, bytes) ← BidPriceSummaryFractionPair.decode bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPriceSummaryFractionPair, bytes) ← AskPriceSummaryFractionPair.decode bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (lastPriceFractionPair, bytes) ← LastPriceFractionPair.decode bytes
  let (openPriceFractionPair, bytes) ← OpenPriceFractionPair.decode bytes
  let (highPriceFractionPair, bytes) ← HighPriceFractionPair.decode bytes
  let (lowPriceFractionPair, bytes) ← LowPriceFractionPair.decode bytes
  let (settlementPriceFutureOptionsSummaryMessageFractionPair, bytes) ← SettlementPriceFutureOptionsSummaryMessageFractionPair.decode bytes
  let (netChangeSign, bytes) ← NetChangeSign.decode bytes
  let (netChangeFuturesSummaryMessageFractionPair, bytes) ← NetChangeFuturesSummaryMessageFractionPair.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (previousSettlementFractionPair, bytes) ← PreviousSettlementFractionPair.decode bytes
  let (openInterest, bytes) ← Alpha.decode 7 bytes
  let (reason, bytes) ← Reason.decode bytes
  let (externalPriceAtSourceFractionPair, bytes) ← ExternalPriceAtSourceFractionPair.decode bytes
  pure ({ exchangeId, rootSymbol, deliveryMonth, deliveryYearFutures, deliveryDay, bidPriceSummaryFractionPair, bidSize, askPriceSummaryFractionPair, askSize, lastPriceFractionPair, openPriceFractionPair, highPriceFractionPair, lowPriceFractionPair, settlementPriceFutureOptionsSummaryMessageFractionPair, netChangeSign, netChangeFuturesSummaryMessageFractionPair, volume, previousSettlementFractionPair, openInterest, reason, externalPriceAtSourceFractionPair }, bytes)

@[simp] theorem encode_length (message : FuturesSummaryMessage) : (encode message).length = 109 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length, DeliveryMonth.encode_length, BidPriceSummaryFractionPair.encode_length, AskPriceSummaryFractionPair.encode_length, LastPriceFractionPair.encode_length, OpenPriceFractionPair.encode_length, HighPriceFractionPair.encode_length, LowPriceFractionPair.encode_length, SettlementPriceFutureOptionsSummaryMessageFractionPair.encode_length, NetChangeSign.encode_length, NetChangeFuturesSummaryMessageFractionPair.encode_length, PreviousSettlementFractionPair.encode_length, Reason.encode_length, ExternalPriceAtSourceFractionPair.encode_length]

theorem encode_length_pos (message : FuturesSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FuturesSummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DeliveryMonth.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BidPriceSummaryFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskPriceSummaryFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LastPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpenPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, HighPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LowPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SettlementPriceFutureOptionsSummaryMessageFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeFuturesSummaryMessageFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PreviousSettlementFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Reason.decode_encode, some_bind]
  dsimp only
  rw [ExternalPriceAtSourceFractionPair.decode_encode, some_bind]
  rfl

end FuturesSummaryMessage

/-- Net Change Strategy Summary Message Fraction Pair: 7 bytes -/
structure NetChangeStrategySummaryMessageFractionPair where
  rawNetChangeStrategySummaryMessage : Alpha 6
  netChangeFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace NetChangeStrategySummaryMessageFractionPair

def encode (message : NetChangeStrategySummaryMessageFractionPair) : List UInt8 :=
  Alpha.encode message.rawNetChangeStrategySummaryMessage
    ++ (encodeUInt 1 message.netChangeFractionIndicator)

def decode (bytes : List UInt8) : Option (NetChangeStrategySummaryMessageFractionPair × List UInt8) := do
  let (rawNetChangeStrategySummaryMessage, bytes) ← Alpha.decode 6 bytes
  let (netChangeFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawNetChangeStrategySummaryMessage, netChangeFractionIndicator }, bytes)

@[simp] theorem encode_length (message : NetChangeStrategySummaryMessageFractionPair) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : NetChangeStrategySummaryMessageFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NetChangeStrategySummaryMessageFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end NetChangeStrategySummaryMessageFractionPair

/-- Strategy Summary Strategy Leg: 33 bytes -/
structure StrategySummaryStrategyLeg where
  legRatioSign : LegRatioSign
  legRatio : Alpha 2
  legSymbol : Alpha 30
  deriving DecidableEq, Repr

namespace StrategySummaryStrategyLeg

def encode (message : StrategySummaryStrategyLeg) : List UInt8 :=
  LegRatioSign.encode message.legRatioSign
    ++ (Alpha.encode message.legRatio
    ++ (Alpha.encode message.legSymbol))

def decode (bytes : List UInt8) : Option (StrategySummaryStrategyLeg × List UInt8) := do
  let (legRatioSign, bytes) ← LegRatioSign.decode bytes
  let (legRatio, bytes) ← Alpha.decode 2 bytes
  let (legSymbol, bytes) ← Alpha.decode 30 bytes
  pure ({ legRatioSign, legRatio, legSymbol }, bytes)

@[simp] theorem encode_length (message : StrategySummaryStrategyLeg) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, LegRatioSign.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : StrategySummaryStrategyLeg) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategySummaryStrategyLeg) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LegRatioSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StrategySummaryStrategyLeg

/-- Strategy Summary Message -/
structure StrategySummaryMessage where
  exchangeId : ExchangeId
  strategySymbol : Alpha 30
  bidPriceSign : BidPriceSign
  bidPriceSummaryFractionPair : BidPriceSummaryFractionPair
  bidSize : Alpha 5
  askPriceSign : AskPriceSign
  askPriceSummaryFractionPair : AskPriceSummaryFractionPair
  askSize : Alpha 5
  lastPriceSign : LastPriceSign
  lastPriceFractionPair : LastPriceFractionPair
  openPriceSign : OpenPriceSign
  openPriceFractionPair : OpenPriceFractionPair
  highPriceSign : HighPriceSign
  highPriceFractionPair : HighPriceFractionPair
  lowPriceSign : LowPriceSign
  lowPriceFractionPair : LowPriceFractionPair
  netChangeSign : NetChangeSign
  netChangeStrategySummaryMessageFractionPair : NetChangeStrategySummaryMessageFractionPair
  volume : Alpha 8
  reason : Reason
  strategySummaryStrategyLeg : Digited 2 StrategySummaryStrategyLeg
  deriving DecidableEq, Repr

namespace StrategySummaryMessage

def encode (message : StrategySummaryMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.strategySymbol
    ++ (BidPriceSign.encode message.bidPriceSign
    ++ (BidPriceSummaryFractionPair.encode message.bidPriceSummaryFractionPair
    ++ (Alpha.encode message.bidSize
    ++ (AskPriceSign.encode message.askPriceSign
    ++ (AskPriceSummaryFractionPair.encode message.askPriceSummaryFractionPair
    ++ (Alpha.encode message.askSize
    ++ (LastPriceSign.encode message.lastPriceSign
    ++ (LastPriceFractionPair.encode message.lastPriceFractionPair
    ++ (OpenPriceSign.encode message.openPriceSign
    ++ (OpenPriceFractionPair.encode message.openPriceFractionPair
    ++ (HighPriceSign.encode message.highPriceSign
    ++ (HighPriceFractionPair.encode message.highPriceFractionPair
    ++ (LowPriceSign.encode message.lowPriceSign
    ++ (LowPriceFractionPair.encode message.lowPriceFractionPair
    ++ (NetChangeSign.encode message.netChangeSign
    ++ (NetChangeStrategySummaryMessageFractionPair.encode message.netChangeStrategySummaryMessageFractionPair
    ++ (Alpha.encode message.volume
    ++ (Reason.encode message.reason
    ++ (encodeDigits 2 message.strategySummaryStrategyLeg.val.length
    ++ (encodeMany StrategySummaryStrategyLeg.encode message.strategySummaryStrategyLeg.val)))))))))))))))))))))

def decode (bytes : List UInt8) : Option (StrategySummaryMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (strategySymbol, bytes) ← Alpha.decode 30 bytes
  let (bidPriceSign, bytes) ← BidPriceSign.decode bytes
  let (bidPriceSummaryFractionPair, bytes) ← BidPriceSummaryFractionPair.decode bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPriceSign, bytes) ← AskPriceSign.decode bytes
  let (askPriceSummaryFractionPair, bytes) ← AskPriceSummaryFractionPair.decode bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (lastPriceSign, bytes) ← LastPriceSign.decode bytes
  let (lastPriceFractionPair, bytes) ← LastPriceFractionPair.decode bytes
  let (openPriceSign, bytes) ← OpenPriceSign.decode bytes
  let (openPriceFractionPair, bytes) ← OpenPriceFractionPair.decode bytes
  let (highPriceSign, bytes) ← HighPriceSign.decode bytes
  let (highPriceFractionPair, bytes) ← HighPriceFractionPair.decode bytes
  let (lowPriceSign, bytes) ← LowPriceSign.decode bytes
  let (lowPriceFractionPair, bytes) ← LowPriceFractionPair.decode bytes
  let (netChangeSign, bytes) ← NetChangeSign.decode bytes
  let (netChangeStrategySummaryMessageFractionPair, bytes) ← NetChangeStrategySummaryMessageFractionPair.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (reason, bytes) ← Reason.decode bytes
  let (numberOfLegs, bytes) ← decodeDigits 2 bytes
  let (strategySummaryStrategyLeg_, bytes) ← decodeMany StrategySummaryStrategyLeg.decode numberOfLegs bytes
  if fits_strategySummaryStrategyLeg : strategySummaryStrategyLeg_.length < 10 ^ 2 then
    pure ({ exchangeId, strategySymbol, bidPriceSign, bidPriceSummaryFractionPair, bidSize, askPriceSign, askPriceSummaryFractionPair, askSize, lastPriceSign, lastPriceFractionPair, openPriceSign, openPriceFractionPair, highPriceSign, highPriceFractionPair, lowPriceSign, lowPriceFractionPair, netChangeSign, netChangeStrategySummaryMessageFractionPair, volume, reason, strategySummaryStrategyLeg := ⟨strategySummaryStrategyLeg_, fits_strategySummaryStrategyLeg⟩ }, bytes)
  else none

theorem encode_length_pos (message : StrategySummaryMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [ExchangeId.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : StrategySummaryMessage) : (encode message).length ≤ 3375 := by
  have bound_strategySummaryStrategyLeg := message.strategySummaryStrategyLeg.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, ExchangeId.encode_length, Alpha.encode_length, BidPriceSign.encode_length, BidPriceSummaryFractionPair.encode_length, AskPriceSign.encode_length, AskPriceSummaryFractionPair.encode_length, LastPriceSign.encode_length, LastPriceFractionPair.encode_length, OpenPriceSign.encode_length, OpenPriceFractionPair.encode_length, HighPriceSign.encode_length, HighPriceFractionPair.encode_length, LowPriceSign.encode_length, LowPriceFractionPair.encode_length, NetChangeSign.encode_length, NetChangeStrategySummaryMessageFractionPair.encode_length, Reason.encode_length, encodeDigits_length, encodeMany_length_const StrategySummaryStrategyLeg.encode 33 StrategySummaryStrategyLeg.encode_length]
  omega

@[simp] theorem decode_encode (message : StrategySummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BidPriceSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BidPriceSummaryFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskPriceSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskPriceSummaryFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LastPriceSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LastPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpenPriceSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpenPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, HighPriceSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, HighPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LowPriceSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LowPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeStrategySummaryMessageFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Reason.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.strategySummaryStrategyLeg.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany StrategySummaryStrategyLeg.encode StrategySummaryStrategyLeg.decode StrategySummaryStrategyLeg.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.strategySummaryStrategyLeg.length_lt]
  rfl

end StrategySummaryMessage

/-- Net Present Value A Fraction Pair: 12 bytes -/
structure NetPresentValueAFractionPair where
  rawNetPresentValueA : Alpha 11
  netPresentValueFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace NetPresentValueAFractionPair

def encode (message : NetPresentValueAFractionPair) : List UInt8 :=
  Alpha.encode message.rawNetPresentValueA
    ++ (encodeUInt 1 message.netPresentValueFractionIndicator)

def decode (bytes : List UInt8) : Option (NetPresentValueAFractionPair × List UInt8) := do
  let (rawNetPresentValueA, bytes) ← Alpha.decode 11 bytes
  let (netPresentValueFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawNetPresentValueA, netPresentValueFractionIndicator }, bytes)

@[simp] theorem encode_length (message : NetPresentValueAFractionPair) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : NetPresentValueAFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NetPresentValueAFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end NetPresentValueAFractionPair

/-- Historical Coupon B Fraction Pair: 12 bytes -/
structure HistoricalCouponBFractionPair where
  rawHistoricalCouponB : Alpha 11
  historicalCouponFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace HistoricalCouponBFractionPair

def encode (message : HistoricalCouponBFractionPair) : List UInt8 :=
  Alpha.encode message.rawHistoricalCouponB
    ++ (encodeUInt 1 message.historicalCouponFractionIndicator)

def decode (bytes : List UInt8) : Option (HistoricalCouponBFractionPair × List UInt8) := do
  let (rawHistoricalCouponB, bytes) ← Alpha.decode 11 bytes
  let (historicalCouponFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawHistoricalCouponB, historicalCouponFractionIndicator }, bytes)

@[simp] theorem encode_length (message : HistoricalCouponBFractionPair) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : HistoricalCouponBFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : HistoricalCouponBFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end HistoricalCouponBFractionPair

/-- Price Alignment Interest C Fraction Pair: 12 bytes -/
structure PriceAlignmentInterestCFractionPair where
  rawPriceAlignmentInterestC : Alpha 11
  priceAlignmentInterestFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace PriceAlignmentInterestCFractionPair

def encode (message : PriceAlignmentInterestCFractionPair) : List UInt8 :=
  Alpha.encode message.rawPriceAlignmentInterestC
    ++ (encodeUInt 1 message.priceAlignmentInterestFractionIndicator)

def decode (bytes : List UInt8) : Option (PriceAlignmentInterestCFractionPair × List UInt8) := do
  let (rawPriceAlignmentInterestC, bytes) ← Alpha.decode 11 bytes
  let (priceAlignmentInterestFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawPriceAlignmentInterestC, priceAlignmentInterestFractionIndicator }, bytes)

@[simp] theorem encode_length (message : PriceAlignmentInterestCFractionPair) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : PriceAlignmentInterestCFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PriceAlignmentInterestCFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end PriceAlignmentInterestCFractionPair

/-- Net Change Swap Future Summary Message Fraction Pair: 7 bytes -/
structure NetChangeSwapFutureSummaryMessageFractionPair where
  rawNetChangeSwapFutureSummaryMessage : Alpha 6
  netChangeFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace NetChangeSwapFutureSummaryMessageFractionPair

def encode (message : NetChangeSwapFutureSummaryMessageFractionPair) : List UInt8 :=
  Alpha.encode message.rawNetChangeSwapFutureSummaryMessage
    ++ (encodeUInt 1 message.netChangeFractionIndicator)

def decode (bytes : List UInt8) : Option (NetChangeSwapFutureSummaryMessageFractionPair × List UInt8) := do
  let (rawNetChangeSwapFutureSummaryMessage, bytes) ← Alpha.decode 6 bytes
  let (netChangeFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawNetChangeSwapFutureSummaryMessage, netChangeFractionIndicator }, bytes)

@[simp] theorem encode_length (message : NetChangeSwapFutureSummaryMessageFractionPair) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : NetChangeSwapFutureSummaryMessageFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NetChangeSwapFutureSummaryMessageFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end NetChangeSwapFutureSummaryMessageFractionPair

/-- Previous Reset Rate Fraction Pair: 7 bytes -/
structure PreviousResetRateFractionPair where
  rawPreviousResetRate : Alpha 6
  previousResetRateFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace PreviousResetRateFractionPair

def encode (message : PreviousResetRateFractionPair) : List UInt8 :=
  Alpha.encode message.rawPreviousResetRate
    ++ (encodeUInt 1 message.previousResetRateFractionIndicator)

def decode (bytes : List UInt8) : Option (PreviousResetRateFractionPair × List UInt8) := do
  let (rawPreviousResetRate, bytes) ← Alpha.decode 6 bytes
  let (previousResetRateFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawPreviousResetRate, previousResetRateFractionIndicator }, bytes)

@[simp] theorem encode_length (message : PreviousResetRateFractionPair) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : PreviousResetRateFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PreviousResetRateFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end PreviousResetRateFractionPair

/-- Swap Future Summary Message: 153 bytes -/
structure SwapFutureSummaryMessage where
  exchangeId : ExchangeId
  rootSymbol : Alpha 6
  expiryMonthSwapFuture : ExpiryMonthSwapFuture
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  tenor : Alpha 2
  fixedRateFractionPair : FixedRateFractionPair
  bidPriceSummaryFractionPair : BidPriceSummaryFractionPair
  bidSize : Alpha 5
  askPriceSummaryFractionPair : AskPriceSummaryFractionPair
  askSize : Alpha 5
  lastPriceFractionPair : LastPriceFractionPair
  openPriceFractionPair : OpenPriceFractionPair
  highPriceFractionPair : HighPriceFractionPair
  lowPriceFractionPair : LowPriceFractionPair
  settlementPriceFutureOptionsSummaryMessageFractionPair : SettlementPriceFutureOptionsSummaryMessageFractionPair
  netPresentValueAFractionPair : NetPresentValueAFractionPair
  historicalCouponBFractionPair : HistoricalCouponBFractionPair
  priceAlignmentInterestCFractionPair : PriceAlignmentInterestCFractionPair
  netChangeSign : NetChangeSign
  netChangeSwapFutureSummaryMessageFractionPair : NetChangeSwapFutureSummaryMessageFractionPair
  volume : Alpha 8
  previousSettlementPriceFractionPair : PreviousSettlementPriceFractionPair
  previousResetRateFractionPair : PreviousResetRateFractionPair
  openInterest : Alpha 7
  reason : Reason
  deriving DecidableEq, Repr

namespace SwapFutureSummaryMessage

def encode (message : SwapFutureSummaryMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (ExpiryMonthSwapFuture.encode message.expiryMonthSwapFuture
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay
    ++ (Alpha.encode message.tenor
    ++ (FixedRateFractionPair.encode message.fixedRateFractionPair
    ++ (BidPriceSummaryFractionPair.encode message.bidPriceSummaryFractionPair
    ++ (Alpha.encode message.bidSize
    ++ (AskPriceSummaryFractionPair.encode message.askPriceSummaryFractionPair
    ++ (Alpha.encode message.askSize
    ++ (LastPriceFractionPair.encode message.lastPriceFractionPair
    ++ (OpenPriceFractionPair.encode message.openPriceFractionPair
    ++ (HighPriceFractionPair.encode message.highPriceFractionPair
    ++ (LowPriceFractionPair.encode message.lowPriceFractionPair
    ++ (SettlementPriceFutureOptionsSummaryMessageFractionPair.encode message.settlementPriceFutureOptionsSummaryMessageFractionPair
    ++ (NetPresentValueAFractionPair.encode message.netPresentValueAFractionPair
    ++ (HistoricalCouponBFractionPair.encode message.historicalCouponBFractionPair
    ++ (PriceAlignmentInterestCFractionPair.encode message.priceAlignmentInterestCFractionPair
    ++ (NetChangeSign.encode message.netChangeSign
    ++ (NetChangeSwapFutureSummaryMessageFractionPair.encode message.netChangeSwapFutureSummaryMessageFractionPair
    ++ (Alpha.encode message.volume
    ++ (PreviousSettlementPriceFractionPair.encode message.previousSettlementPriceFractionPair
    ++ (PreviousResetRateFractionPair.encode message.previousResetRateFractionPair
    ++ (Alpha.encode message.openInterest
    ++ (Reason.encode message.reason)))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SwapFutureSummaryMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (expiryMonthSwapFuture, bytes) ← ExpiryMonthSwapFuture.decode bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (tenor, bytes) ← Alpha.decode 2 bytes
  let (fixedRateFractionPair, bytes) ← FixedRateFractionPair.decode bytes
  let (bidPriceSummaryFractionPair, bytes) ← BidPriceSummaryFractionPair.decode bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPriceSummaryFractionPair, bytes) ← AskPriceSummaryFractionPair.decode bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (lastPriceFractionPair, bytes) ← LastPriceFractionPair.decode bytes
  let (openPriceFractionPair, bytes) ← OpenPriceFractionPair.decode bytes
  let (highPriceFractionPair, bytes) ← HighPriceFractionPair.decode bytes
  let (lowPriceFractionPair, bytes) ← LowPriceFractionPair.decode bytes
  let (settlementPriceFutureOptionsSummaryMessageFractionPair, bytes) ← SettlementPriceFutureOptionsSummaryMessageFractionPair.decode bytes
  let (netPresentValueAFractionPair, bytes) ← NetPresentValueAFractionPair.decode bytes
  let (historicalCouponBFractionPair, bytes) ← HistoricalCouponBFractionPair.decode bytes
  let (priceAlignmentInterestCFractionPair, bytes) ← PriceAlignmentInterestCFractionPair.decode bytes
  let (netChangeSign, bytes) ← NetChangeSign.decode bytes
  let (netChangeSwapFutureSummaryMessageFractionPair, bytes) ← NetChangeSwapFutureSummaryMessageFractionPair.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (previousSettlementPriceFractionPair, bytes) ← PreviousSettlementPriceFractionPair.decode bytes
  let (previousResetRateFractionPair, bytes) ← PreviousResetRateFractionPair.decode bytes
  let (openInterest, bytes) ← Alpha.decode 7 bytes
  let (reason, bytes) ← Reason.decode bytes
  pure ({ exchangeId, rootSymbol, expiryMonthSwapFuture, expiryYear, expiryDay, tenor, fixedRateFractionPair, bidPriceSummaryFractionPair, bidSize, askPriceSummaryFractionPair, askSize, lastPriceFractionPair, openPriceFractionPair, highPriceFractionPair, lowPriceFractionPair, settlementPriceFutureOptionsSummaryMessageFractionPair, netPresentValueAFractionPair, historicalCouponBFractionPair, priceAlignmentInterestCFractionPair, netChangeSign, netChangeSwapFutureSummaryMessageFractionPair, volume, previousSettlementPriceFractionPair, previousResetRateFractionPair, openInterest, reason }, bytes)

@[simp] theorem encode_length (message : SwapFutureSummaryMessage) : (encode message).length = 153 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length, ExpiryMonthSwapFuture.encode_length, FixedRateFractionPair.encode_length, BidPriceSummaryFractionPair.encode_length, AskPriceSummaryFractionPair.encode_length, LastPriceFractionPair.encode_length, OpenPriceFractionPair.encode_length, HighPriceFractionPair.encode_length, LowPriceFractionPair.encode_length, SettlementPriceFutureOptionsSummaryMessageFractionPair.encode_length, NetPresentValueAFractionPair.encode_length, HistoricalCouponBFractionPair.encode_length, PriceAlignmentInterestCFractionPair.encode_length, NetChangeSign.encode_length, NetChangeSwapFutureSummaryMessageFractionPair.encode_length, PreviousSettlementPriceFractionPair.encode_length, PreviousResetRateFractionPair.encode_length, Reason.encode_length]

theorem encode_length_pos (message : SwapFutureSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SwapFutureSummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExpiryMonthSwapFuture.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FixedRateFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BidPriceSummaryFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskPriceSummaryFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LastPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpenPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, HighPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LowPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SettlementPriceFutureOptionsSummaryMessageFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetPresentValueAFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, HistoricalCouponBFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PriceAlignmentInterestCFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeSwapFutureSummaryMessageFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PreviousSettlementPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PreviousResetRateFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Reason.decode_encode, some_bind]
  rfl

end SwapFutureSummaryMessage

/-- Beginning Of Options Summary Message: 1 bytes -/
structure BeginningOfOptionsSummaryMessage where
  exchangeId : ExchangeId
  deriving DecidableEq, Repr

namespace BeginningOfOptionsSummaryMessage

def encode (message : BeginningOfOptionsSummaryMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId

def decode (bytes : List UInt8) : Option (BeginningOfOptionsSummaryMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  pure ({ exchangeId }, bytes)

@[simp] theorem encode_length (message : BeginningOfOptionsSummaryMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [ExchangeId.encode_length]

theorem encode_length_pos (message : BeginningOfOptionsSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BeginningOfOptionsSummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [ExchangeId.decode_encode, some_bind]
  rfl

end BeginningOfOptionsSummaryMessage

/-- Beginning Of Future Options Summary Message: 1 bytes -/
structure BeginningOfFutureOptionsSummaryMessage where
  exchangeId : ExchangeId
  deriving DecidableEq, Repr

namespace BeginningOfFutureOptionsSummaryMessage

def encode (message : BeginningOfFutureOptionsSummaryMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId

def decode (bytes : List UInt8) : Option (BeginningOfFutureOptionsSummaryMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  pure ({ exchangeId }, bytes)

@[simp] theorem encode_length (message : BeginningOfFutureOptionsSummaryMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [ExchangeId.encode_length]

theorem encode_length_pos (message : BeginningOfFutureOptionsSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BeginningOfFutureOptionsSummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [ExchangeId.decode_encode, some_bind]
  rfl

end BeginningOfFutureOptionsSummaryMessage

/-- Beginning Of Futures Summary Message: 1 bytes -/
structure BeginningOfFuturesSummaryMessage where
  exchangeId : ExchangeId
  deriving DecidableEq, Repr

namespace BeginningOfFuturesSummaryMessage

def encode (message : BeginningOfFuturesSummaryMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId

def decode (bytes : List UInt8) : Option (BeginningOfFuturesSummaryMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  pure ({ exchangeId }, bytes)

@[simp] theorem encode_length (message : BeginningOfFuturesSummaryMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [ExchangeId.encode_length]

theorem encode_length_pos (message : BeginningOfFuturesSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BeginningOfFuturesSummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [ExchangeId.decode_encode, some_bind]
  rfl

end BeginningOfFuturesSummaryMessage

/-- Beginning Of Strategy Summary Message: 1 bytes -/
structure BeginningOfStrategySummaryMessage where
  exchangeId : ExchangeId
  deriving DecidableEq, Repr

namespace BeginningOfStrategySummaryMessage

def encode (message : BeginningOfStrategySummaryMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId

def decode (bytes : List UInt8) : Option (BeginningOfStrategySummaryMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  pure ({ exchangeId }, bytes)

@[simp] theorem encode_length (message : BeginningOfStrategySummaryMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [ExchangeId.encode_length]

theorem encode_length_pos (message : BeginningOfStrategySummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BeginningOfStrategySummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [ExchangeId.decode_encode, some_bind]
  rfl

end BeginningOfStrategySummaryMessage

/-- Swap Future Beginning Of Summary Message: 1 bytes -/
structure SwapFutureBeginningOfSummaryMessage where
  exchangeId : ExchangeId
  deriving DecidableEq, Repr

namespace SwapFutureBeginningOfSummaryMessage

def encode (message : SwapFutureBeginningOfSummaryMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId

def decode (bytes : List UInt8) : Option (SwapFutureBeginningOfSummaryMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  pure ({ exchangeId }, bytes)

@[simp] theorem encode_length (message : SwapFutureBeginningOfSummaryMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [ExchangeId.encode_length]

theorem encode_length_pos (message : SwapFutureBeginningOfSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SwapFutureBeginningOfSummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [ExchangeId.decode_encode, some_bind]
  rfl

end SwapFutureBeginningOfSummaryMessage

/-- Option Trade Correction Message: 76 bytes -/
structure OptionTradeCorrectionMessage where
  exchangeId : ExchangeId
  rootSymbol : Alpha 6
  expiryMonth : ExpiryMonth
  filler1 : Alpha 1
  strikePriceInstrumentFractionPair : StrikePriceInstrumentFractionPair
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  volume : Alpha 8
  tradePriceFractionPair : TradePriceFractionPair
  netChangeSign : NetChangeSign
  netChangeFractionPair : NetChangeFractionPair
  filler6 : Alpha 6
  timestamp : Alpha 9
  openInterest : Alpha 7
  secondFiller1 : Alpha 1
  priceIndicatorMarker : PriceIndicatorMarker
  tradeNumber : Alpha 8
  deriving DecidableEq, Repr

namespace OptionTradeCorrectionMessage

def encode (message : OptionTradeCorrectionMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (ExpiryMonth.encode message.expiryMonth
    ++ (Alpha.encode message.filler1
    ++ (StrikePriceInstrumentFractionPair.encode message.strikePriceInstrumentFractionPair
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay
    ++ (Alpha.encode message.volume
    ++ (TradePriceFractionPair.encode message.tradePriceFractionPair
    ++ (NetChangeSign.encode message.netChangeSign
    ++ (NetChangeFractionPair.encode message.netChangeFractionPair
    ++ (Alpha.encode message.filler6
    ++ (Alpha.encode message.timestamp
    ++ (Alpha.encode message.openInterest
    ++ (Alpha.encode message.secondFiller1
    ++ (PriceIndicatorMarker.encode message.priceIndicatorMarker
    ++ (Alpha.encode message.tradeNumber))))))))))))))))

def decode (bytes : List UInt8) : Option (OptionTradeCorrectionMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (expiryMonth, bytes) ← ExpiryMonth.decode bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (strikePriceInstrumentFractionPair, bytes) ← StrikePriceInstrumentFractionPair.decode bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePriceFractionPair, bytes) ← TradePriceFractionPair.decode bytes
  let (netChangeSign, bytes) ← NetChangeSign.decode bytes
  let (netChangeFractionPair, bytes) ← NetChangeFractionPair.decode bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (timestamp, bytes) ← Alpha.decode 9 bytes
  let (openInterest, bytes) ← Alpha.decode 7 bytes
  let (secondFiller1, bytes) ← Alpha.decode 1 bytes
  let (priceIndicatorMarker, bytes) ← PriceIndicatorMarker.decode bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ exchangeId, rootSymbol, expiryMonth, filler1, strikePriceInstrumentFractionPair, expiryYear, expiryDay, volume, tradePriceFractionPair, netChangeSign, netChangeFractionPair, filler6, timestamp, openInterest, secondFiller1, priceIndicatorMarker, tradeNumber }, bytes)

@[simp] theorem encode_length (message : OptionTradeCorrectionMessage) : (encode message).length = 76 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length, ExpiryMonth.encode_length, StrikePriceInstrumentFractionPair.encode_length, TradePriceFractionPair.encode_length, NetChangeSign.encode_length, NetChangeFractionPair.encode_length, PriceIndicatorMarker.encode_length]

theorem encode_length_pos (message : OptionTradeCorrectionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionTradeCorrectionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExpiryMonth.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StrikePriceInstrumentFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradePriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PriceIndicatorMarker.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OptionTradeCorrectionMessage

/-- Future Options Trade Correction Message: 77 bytes -/
structure FutureOptionsTradeCorrectionMessage where
  exchangeId : ExchangeId
  rootSymbol : Alpha 6
  contractMonthCode : ContractMonthCode
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  callPutCode : CallPutCode
  strikePriceInstrumentFractionPair : StrikePriceInstrumentFractionPair
  volume : Alpha 8
  tradePriceFractionPair : TradePriceFractionPair
  priceIndicatorMarker : PriceIndicatorMarker
  netChangeSign : NetChangeSign
  netChangeFutureOptionsTradeMessageFractionPair : NetChangeFutureOptionsTradeMessageFractionPair
  filler6 : Alpha 6
  timestamp : Alpha 9
  openInterest : Alpha 7
  filler2 : Alpha 2
  tradeNumber : Alpha 8
  deriving DecidableEq, Repr

namespace FutureOptionsTradeCorrectionMessage

def encode (message : FutureOptionsTradeCorrectionMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (ContractMonthCode.encode message.contractMonthCode
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay
    ++ (CallPutCode.encode message.callPutCode
    ++ (StrikePriceInstrumentFractionPair.encode message.strikePriceInstrumentFractionPair
    ++ (Alpha.encode message.volume
    ++ (TradePriceFractionPair.encode message.tradePriceFractionPair
    ++ (PriceIndicatorMarker.encode message.priceIndicatorMarker
    ++ (NetChangeSign.encode message.netChangeSign
    ++ (NetChangeFutureOptionsTradeMessageFractionPair.encode message.netChangeFutureOptionsTradeMessageFractionPair
    ++ (Alpha.encode message.filler6
    ++ (Alpha.encode message.timestamp
    ++ (Alpha.encode message.openInterest
    ++ (Alpha.encode message.filler2
    ++ (Alpha.encode message.tradeNumber))))))))))))))))

def decode (bytes : List UInt8) : Option (FutureOptionsTradeCorrectionMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (contractMonthCode, bytes) ← ContractMonthCode.decode bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (callPutCode, bytes) ← CallPutCode.decode bytes
  let (strikePriceInstrumentFractionPair, bytes) ← StrikePriceInstrumentFractionPair.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePriceFractionPair, bytes) ← TradePriceFractionPair.decode bytes
  let (priceIndicatorMarker, bytes) ← PriceIndicatorMarker.decode bytes
  let (netChangeSign, bytes) ← NetChangeSign.decode bytes
  let (netChangeFutureOptionsTradeMessageFractionPair, bytes) ← NetChangeFutureOptionsTradeMessageFractionPair.decode bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (timestamp, bytes) ← Alpha.decode 9 bytes
  let (openInterest, bytes) ← Alpha.decode 7 bytes
  let (filler2, bytes) ← Alpha.decode 2 bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ exchangeId, rootSymbol, contractMonthCode, expiryYear, expiryDay, callPutCode, strikePriceInstrumentFractionPair, volume, tradePriceFractionPair, priceIndicatorMarker, netChangeSign, netChangeFutureOptionsTradeMessageFractionPair, filler6, timestamp, openInterest, filler2, tradeNumber }, bytes)

@[simp] theorem encode_length (message : FutureOptionsTradeCorrectionMessage) : (encode message).length = 77 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length, ContractMonthCode.encode_length, CallPutCode.encode_length, StrikePriceInstrumentFractionPair.encode_length, TradePriceFractionPair.encode_length, PriceIndicatorMarker.encode_length, NetChangeSign.encode_length, NetChangeFutureOptionsTradeMessageFractionPair.encode_length]

theorem encode_length_pos (message : FutureOptionsTradeCorrectionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FutureOptionsTradeCorrectionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ContractMonthCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CallPutCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StrikePriceInstrumentFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradePriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PriceIndicatorMarker.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeFutureOptionsTradeMessageFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FutureOptionsTradeCorrectionMessage

/-- Futures Trade Correction Message: 59 bytes -/
structure FuturesTradeCorrectionMessage where
  exchangeId : ExchangeId
  rootSymbol : Alpha 6
  deliveryMonth : DeliveryMonth
  deliveryYearFutures : Alpha 2
  deliveryDay : Alpha 2
  volume : Alpha 8
  tradePriceFractionPair : TradePriceFractionPair
  netChangeSign : NetChangeSign
  netChangeFuturesTradeMessageFractionPair : NetChangeFuturesTradeMessageFractionPair
  filler6 : Alpha 6
  timestamp : Alpha 9
  priceIndicatorMarker : FuturesTradeMessagePriceIndicatorMarker
  tradeNumber : Alpha 8
  deriving DecidableEq, Repr

namespace FuturesTradeCorrectionMessage

def encode (message : FuturesTradeCorrectionMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (DeliveryMonth.encode message.deliveryMonth
    ++ (Alpha.encode message.deliveryYearFutures
    ++ (Alpha.encode message.deliveryDay
    ++ (Alpha.encode message.volume
    ++ (TradePriceFractionPair.encode message.tradePriceFractionPair
    ++ (NetChangeSign.encode message.netChangeSign
    ++ (NetChangeFuturesTradeMessageFractionPair.encode message.netChangeFuturesTradeMessageFractionPair
    ++ (Alpha.encode message.filler6
    ++ (Alpha.encode message.timestamp
    ++ (FuturesTradeMessagePriceIndicatorMarker.encode message.priceIndicatorMarker
    ++ (Alpha.encode message.tradeNumber))))))))))))

def decode (bytes : List UInt8) : Option (FuturesTradeCorrectionMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (deliveryMonth, bytes) ← DeliveryMonth.decode bytes
  let (deliveryYearFutures, bytes) ← Alpha.decode 2 bytes
  let (deliveryDay, bytes) ← Alpha.decode 2 bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePriceFractionPair, bytes) ← TradePriceFractionPair.decode bytes
  let (netChangeSign, bytes) ← NetChangeSign.decode bytes
  let (netChangeFuturesTradeMessageFractionPair, bytes) ← NetChangeFuturesTradeMessageFractionPair.decode bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (timestamp, bytes) ← Alpha.decode 9 bytes
  let (priceIndicatorMarker, bytes) ← FuturesTradeMessagePriceIndicatorMarker.decode bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ exchangeId, rootSymbol, deliveryMonth, deliveryYearFutures, deliveryDay, volume, tradePriceFractionPair, netChangeSign, netChangeFuturesTradeMessageFractionPair, filler6, timestamp, priceIndicatorMarker, tradeNumber }, bytes)

@[simp] theorem encode_length (message : FuturesTradeCorrectionMessage) : (encode message).length = 59 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length, DeliveryMonth.encode_length, TradePriceFractionPair.encode_length, NetChangeSign.encode_length, NetChangeFuturesTradeMessageFractionPair.encode_length, FuturesTradeMessagePriceIndicatorMarker.encode_length]

theorem encode_length_pos (message : FuturesTradeCorrectionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FuturesTradeCorrectionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DeliveryMonth.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradePriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeFuturesTradeMessageFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FuturesTradeMessagePriceIndicatorMarker.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FuturesTradeCorrectionMessage

/-- Strategy Trade Correction Message: 79 bytes -/
structure StrategyTradeCorrectionMessage where
  exchangeId : ExchangeId
  symbol : Alpha 30
  volume : Alpha 8
  tradePriceSign : TradePriceSign
  tradePriceFractionPair : TradePriceFractionPair
  netChangeSign : NetChangeSign
  netChangeFractionPair : NetChangeFractionPair
  filler6 : Alpha 6
  timestamp : Alpha 9
  priceIndicatorMarker : FuturesTradeMessagePriceIndicatorMarker
  tradeNumber : Alpha 8
  deriving DecidableEq, Repr

namespace StrategyTradeCorrectionMessage

def encode (message : StrategyTradeCorrectionMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.volume
    ++ (TradePriceSign.encode message.tradePriceSign
    ++ (TradePriceFractionPair.encode message.tradePriceFractionPair
    ++ (NetChangeSign.encode message.netChangeSign
    ++ (NetChangeFractionPair.encode message.netChangeFractionPair
    ++ (Alpha.encode message.filler6
    ++ (Alpha.encode message.timestamp
    ++ (FuturesTradeMessagePriceIndicatorMarker.encode message.priceIndicatorMarker
    ++ (Alpha.encode message.tradeNumber))))))))))

def decode (bytes : List UInt8) : Option (StrategyTradeCorrectionMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (symbol, bytes) ← Alpha.decode 30 bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePriceSign, bytes) ← TradePriceSign.decode bytes
  let (tradePriceFractionPair, bytes) ← TradePriceFractionPair.decode bytes
  let (netChangeSign, bytes) ← NetChangeSign.decode bytes
  let (netChangeFractionPair, bytes) ← NetChangeFractionPair.decode bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (timestamp, bytes) ← Alpha.decode 9 bytes
  let (priceIndicatorMarker, bytes) ← FuturesTradeMessagePriceIndicatorMarker.decode bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ exchangeId, symbol, volume, tradePriceSign, tradePriceFractionPair, netChangeSign, netChangeFractionPair, filler6, timestamp, priceIndicatorMarker, tradeNumber }, bytes)

@[simp] theorem encode_length (message : StrategyTradeCorrectionMessage) : (encode message).length = 79 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length, TradePriceSign.encode_length, TradePriceFractionPair.encode_length, NetChangeSign.encode_length, NetChangeFractionPair.encode_length, FuturesTradeMessagePriceIndicatorMarker.encode_length]

theorem encode_length_pos (message : StrategyTradeCorrectionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyTradeCorrectionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradePriceSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradePriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FuturesTradeMessagePriceIndicatorMarker.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StrategyTradeCorrectionMessage

/-- Swap Future Trade Correction Message: 61 bytes -/
structure SwapFutureTradeCorrectionMessage where
  exchangeId : ExchangeId
  rootSymbolSwapFuture : Alpha 6
  expiryMonthSwapFuture : ExpiryMonthSwapFuture
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  tenor : Alpha 2
  fixedRateFractionPair : FixedRateFractionPair
  tradeVolume : Alpha 8
  tradePriceFractionPair : TradePriceFractionPair
  netChangeSign : NetChangeSign
  netChangeFuturesTradeMessageFractionPair : NetChangeFuturesTradeMessageFractionPair
  timestamp : Alpha 9
  priceIndicatorMarker : FuturesTradeMessagePriceIndicatorMarker
  tradeNumber : Alpha 8
  deriving DecidableEq, Repr

namespace SwapFutureTradeCorrectionMessage

def encode (message : SwapFutureTradeCorrectionMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbolSwapFuture
    ++ (ExpiryMonthSwapFuture.encode message.expiryMonthSwapFuture
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay
    ++ (Alpha.encode message.tenor
    ++ (FixedRateFractionPair.encode message.fixedRateFractionPair
    ++ (Alpha.encode message.tradeVolume
    ++ (TradePriceFractionPair.encode message.tradePriceFractionPair
    ++ (NetChangeSign.encode message.netChangeSign
    ++ (NetChangeFuturesTradeMessageFractionPair.encode message.netChangeFuturesTradeMessageFractionPair
    ++ (Alpha.encode message.timestamp
    ++ (FuturesTradeMessagePriceIndicatorMarker.encode message.priceIndicatorMarker
    ++ (Alpha.encode message.tradeNumber)))))))))))))

def decode (bytes : List UInt8) : Option (SwapFutureTradeCorrectionMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (rootSymbolSwapFuture, bytes) ← Alpha.decode 6 bytes
  let (expiryMonthSwapFuture, bytes) ← ExpiryMonthSwapFuture.decode bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (tenor, bytes) ← Alpha.decode 2 bytes
  let (fixedRateFractionPair, bytes) ← FixedRateFractionPair.decode bytes
  let (tradeVolume, bytes) ← Alpha.decode 8 bytes
  let (tradePriceFractionPair, bytes) ← TradePriceFractionPair.decode bytes
  let (netChangeSign, bytes) ← NetChangeSign.decode bytes
  let (netChangeFuturesTradeMessageFractionPair, bytes) ← NetChangeFuturesTradeMessageFractionPair.decode bytes
  let (timestamp, bytes) ← Alpha.decode 9 bytes
  let (priceIndicatorMarker, bytes) ← FuturesTradeMessagePriceIndicatorMarker.decode bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ exchangeId, rootSymbolSwapFuture, expiryMonthSwapFuture, expiryYear, expiryDay, tenor, fixedRateFractionPair, tradeVolume, tradePriceFractionPair, netChangeSign, netChangeFuturesTradeMessageFractionPair, timestamp, priceIndicatorMarker, tradeNumber }, bytes)

@[simp] theorem encode_length (message : SwapFutureTradeCorrectionMessage) : (encode message).length = 61 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length, ExpiryMonthSwapFuture.encode_length, FixedRateFractionPair.encode_length, TradePriceFractionPair.encode_length, NetChangeSign.encode_length, NetChangeFuturesTradeMessageFractionPair.encode_length, FuturesTradeMessagePriceIndicatorMarker.encode_length]

theorem encode_length_pos (message : SwapFutureTradeCorrectionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SwapFutureTradeCorrectionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExpiryMonthSwapFuture.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FixedRateFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradePriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeFuturesTradeMessageFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FuturesTradeMessagePriceIndicatorMarker.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SwapFutureTradeCorrectionMessage

/-- Group Status Message: 8 bytes -/
structure GroupStatusMessage where
  exchangeId : ExchangeId
  rootSymbolGroup : Alpha 6
  groupStatus : GroupStatus
  deriving DecidableEq, Repr

namespace GroupStatusMessage

def encode (message : GroupStatusMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbolGroup
    ++ (GroupStatus.encode message.groupStatus))

def decode (bytes : List UInt8) : Option (GroupStatusMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (rootSymbolGroup, bytes) ← Alpha.decode 6 bytes
  let (groupStatus, bytes) ← GroupStatus.decode bytes
  pure ({ exchangeId, rootSymbolGroup, groupStatus }, bytes)

@[simp] theorem encode_length (message : GroupStatusMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length, GroupStatus.encode_length]

theorem encode_length_pos (message : GroupStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : GroupStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [GroupStatus.decode_encode, some_bind]
  rfl

end GroupStatusMessage

/-- Group Status Strategies Message: 4 bytes -/
structure GroupStatusStrategiesMessage where
  exchangeId : ExchangeId
  groupInstrument : Alpha 2
  groupStatus : GroupStatus
  deriving DecidableEq, Repr

namespace GroupStatusStrategiesMessage

def encode (message : GroupStatusStrategiesMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.groupInstrument
    ++ (GroupStatus.encode message.groupStatus))

def decode (bytes : List UInt8) : Option (GroupStatusStrategiesMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (groupInstrument, bytes) ← Alpha.decode 2 bytes
  let (groupStatus, bytes) ← GroupStatus.decode bytes
  pure ({ exchangeId, groupInstrument, groupStatus }, bytes)

@[simp] theorem encode_length (message : GroupStatusStrategiesMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length, GroupStatus.encode_length]

theorem encode_length_pos (message : GroupStatusStrategiesMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : GroupStatusStrategiesMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [GroupStatus.decode_encode, some_bind]
  rfl

end GroupStatusStrategiesMessage

/-- Regular Text Bulletin: 80 bytes -/
structure RegularTextBulletin where
  regularBulletinContents : Alpha 79
  continueMarker : ContinueMarker
  deriving DecidableEq, Repr

namespace RegularTextBulletin

def encode (message : RegularTextBulletin) : List UInt8 :=
  Alpha.encode message.regularBulletinContents
    ++ (ContinueMarker.encode message.continueMarker)

def decode (bytes : List UInt8) : Option (RegularTextBulletin × List UInt8) := do
  let (regularBulletinContents, bytes) ← Alpha.decode 79 bytes
  let (continueMarker, bytes) ← ContinueMarker.decode bytes
  pure ({ regularBulletinContents, continueMarker }, bytes)

@[simp] theorem encode_length (message : RegularTextBulletin) : (encode message).length = 80 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ContinueMarker.encode_length]

theorem encode_length_pos (message : RegularTextBulletin) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RegularTextBulletin) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [ContinueMarker.decode_encode, some_bind]
  rfl

end RegularTextBulletin

/-- Special Text Bulletin: 80 bytes -/
structure SpecialTextBulletin where
  symbol : Alpha 30
  specialBulletinContents : Alpha 49
  continueMarker : ContinueMarker
  deriving DecidableEq, Repr

namespace SpecialTextBulletin

def encode (message : SpecialTextBulletin) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (Alpha.encode message.specialBulletinContents
    ++ (ContinueMarker.encode message.continueMarker))

def decode (bytes : List UInt8) : Option (SpecialTextBulletin × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 30 bytes
  let (specialBulletinContents, bytes) ← Alpha.decode 49 bytes
  let (continueMarker, bytes) ← ContinueMarker.decode bytes
  pure ({ symbol, specialBulletinContents, continueMarker }, bytes)

@[simp] theorem encode_length (message : SpecialTextBulletin) : (encode message).length = 80 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ContinueMarker.encode_length]

theorem encode_length_pos (message : SpecialTextBulletin) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SpecialTextBulletin) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [ContinueMarker.decode_encode, some_bind]
  rfl

end SpecialTextBulletin

/-- Any Bulletin, selected by Bulletin Type -/
inductive Bulletin where
  | regularTextBulletin (message : RegularTextBulletin) -- "1" 0x31
  | specialTextBulletin (message : SpecialTextBulletin) -- "2" 0x32
  deriving DecidableEq, Repr

namespace Bulletin

/-- The Bulletin Type each message is sent under -/
def tag : Bulletin → BitVec 8
  | .regularTextBulletin _ => 49
  | .specialTextBulletin _ => 50

def encode : Bulletin → List UInt8
  | .regularTextBulletin message => RegularTextBulletin.encode message
  | .specialTextBulletin message => SpecialTextBulletin.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Bulletin) : (encode message).length ≤ 80 := by
  cases message with
  | regularTextBulletin inner =>
    simp only [encode, RegularTextBulletin.encode_length]
    omega
  | specialTextBulletin inner =>
    simp only [encode, SpecialTextBulletin.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Bulletin × List UInt8) :=
  if tag = 49 then (RegularTextBulletin.decode bytes).map fun (message, rest) => (.regularTextBulletin message, rest)
  else if tag = 50 then (SpecialTextBulletin.decode bytes).map fun (message, rest) => (.specialTextBulletin message, rest)
  else none

@[simp] theorem decode_encode (message : Bulletin) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Bulletin

/-- Bulletins Message -/
structure BulletinsMessage where
  reserved : Alpha 1
  bulletin : Bulletin
  deriving DecidableEq, Repr

namespace BulletinsMessage

def encode (message : BulletinsMessage) : List UInt8 :=
  Alpha.encode message.reserved
    ++ (encodeUInt 1 (Bulletin.tag message.bulletin)
    ++ (Bulletin.encode message.bulletin))

def decode (bytes : List UInt8) : Option (BulletinsMessage × List UInt8) := do
  let (reserved, bytes) ← Alpha.decode 1 bytes
  let (bulletinType, bytes) ← decodeUInt 1 bytes
  let (bulletin, bytes) ← Bulletin.decode bulletinType bytes
  pure ({ reserved, bulletin }, bytes)

theorem encode_length_pos (message : BulletinsMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : BulletinsMessage) : (encode message).length ≤ 82 := by
  unfold encode
  cases message.bulletin with
  | regularTextBulletin inner =>
    simp only [Bulletin.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, RegularTextBulletin.encode_length]
    omega
  | specialTextBulletin inner =>
    simp only [Bulletin.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, SpecialTextBulletin.encode_length]
    omega

@[simp] theorem decode_encode (message : BulletinsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Bulletin.decode_encode, some_bind]
  rfl

end BulletinsMessage

/-- End Of Sales Message: 7 bytes -/
structure EndOfSalesMessage where
  reserved : Alpha 1
  time : Alpha 6
  deriving DecidableEq, Repr

namespace EndOfSalesMessage

def encode (message : EndOfSalesMessage) : List UInt8 :=
  Alpha.encode message.reserved
    ++ (Alpha.encode message.time)

def decode (bytes : List UInt8) : Option (EndOfSalesMessage × List UInt8) := do
  let (reserved, bytes) ← Alpha.decode 1 bytes
  let (time, bytes) ← Alpha.decode 6 bytes
  pure ({ reserved, time }, bytes)

@[simp] theorem encode_length (message : EndOfSalesMessage) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : EndOfSalesMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EndOfSalesMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end EndOfSalesMessage

/-- Min Price Fraction Pair: 7 bytes -/
structure MinPriceFractionPair where
  rawMinPrice : Alpha 6
  minPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace MinPriceFractionPair

def encode (message : MinPriceFractionPair) : List UInt8 :=
  Alpha.encode message.rawMinPrice
    ++ (encodeUInt 1 message.minPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (MinPriceFractionPair × List UInt8) := do
  let (rawMinPrice, bytes) ← Alpha.decode 6 bytes
  let (minPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawMinPrice, minPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : MinPriceFractionPair) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : MinPriceFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MinPriceFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MinPriceFractionPair

/-- Tick Price Fraction Pair: 7 bytes -/
structure TickPriceFractionPair where
  rawTickPrice : Alpha 6
  tickPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace TickPriceFractionPair

def encode (message : TickPriceFractionPair) : List UInt8 :=
  Alpha.encode message.rawTickPrice
    ++ (encodeUInt 1 message.tickPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (TickPriceFractionPair × List UInt8) := do
  let (rawTickPrice, bytes) ← Alpha.decode 6 bytes
  let (tickPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawTickPrice, tickPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : TickPriceFractionPair) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : TickPriceFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TickPriceFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TickPriceFractionPair

/-- Tick Entry Group: 14 bytes -/
structure TickEntryGroup where
  minPriceFractionPair : MinPriceFractionPair
  tickPriceFractionPair : TickPriceFractionPair
  deriving DecidableEq, Repr

namespace TickEntryGroup

def encode (message : TickEntryGroup) : List UInt8 :=
  MinPriceFractionPair.encode message.minPriceFractionPair
    ++ (TickPriceFractionPair.encode message.tickPriceFractionPair)

def decode (bytes : List UInt8) : Option (TickEntryGroup × List UInt8) := do
  let (minPriceFractionPair, bytes) ← MinPriceFractionPair.decode bytes
  let (tickPriceFractionPair, bytes) ← TickPriceFractionPair.decode bytes
  pure ({ minPriceFractionPair, tickPriceFractionPair }, bytes)

@[simp] theorem encode_length (message : TickEntryGroup) : (encode message).length = 14 := by
  unfold encode
  simp only [List.length_append, MinPriceFractionPair.encode_length, TickPriceFractionPair.encode_length]

theorem encode_length_pos (message : TickEntryGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TickEntryGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, MinPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [TickPriceFractionPair.decode_encode, some_bind]
  rfl

end TickEntryGroup

/-- Tick Table Message -/
structure TickTableMessage where
  exchangeId : ExchangeId
  tickTableName : Alpha 50
  tickTableShortName : Alpha 2
  tickEntryGroup : Digited 2 TickEntryGroup
  deriving DecidableEq, Repr

namespace TickTableMessage

def encode (message : TickTableMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.tickTableName
    ++ (Alpha.encode message.tickTableShortName
    ++ (encodeDigits 2 message.tickEntryGroup.val.length
    ++ (encodeMany TickEntryGroup.encode message.tickEntryGroup.val))))

def decode (bytes : List UInt8) : Option (TickTableMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (tickTableName, bytes) ← Alpha.decode 50 bytes
  let (tickTableShortName, bytes) ← Alpha.decode 2 bytes
  let (numberOfEntries, bytes) ← decodeDigits 2 bytes
  let (tickEntryGroup_, bytes) ← decodeMany TickEntryGroup.decode numberOfEntries bytes
  if fits_tickEntryGroup : tickEntryGroup_.length < 10 ^ 2 then
    pure ({ exchangeId, tickTableName, tickTableShortName, tickEntryGroup := ⟨tickEntryGroup_, fits_tickEntryGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : TickTableMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [ExchangeId.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TickTableMessage) : (encode message).length ≤ 1441 := by
  have bound_tickEntryGroup := message.tickEntryGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, ExchangeId.encode_length, Alpha.encode_length, encodeDigits_length, encodeMany_length_const TickEntryGroup.encode 14 TickEntryGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : TickTableMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.tickEntryGroup.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany TickEntryGroup.encode TickEntryGroup.decode TickEntryGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.tickEntryGroup.length_lt]
  rfl

end TickTableMessage

/-- End Of Transmission Message: 7 bytes -/
structure EndOfTransmissionMessage where
  exchangeId : ExchangeId
  time : Alpha 6
  deriving DecidableEq, Repr

namespace EndOfTransmissionMessage

def encode (message : EndOfTransmissionMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.time)

def decode (bytes : List UInt8) : Option (EndOfTransmissionMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (time, bytes) ← Alpha.decode 6 bytes
  pure ({ exchangeId, time }, bytes)

@[simp] theorem encode_length (message : EndOfTransmissionMessage) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : EndOfTransmissionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EndOfTransmissionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end EndOfTransmissionMessage

/-- Circuit Assurance Message: 6 bytes -/
structure CircuitAssuranceMessage where
  time : Alpha 6
  deriving DecidableEq, Repr

namespace CircuitAssuranceMessage

def encode (message : CircuitAssuranceMessage) : List UInt8 :=
  Alpha.encode message.time

def decode (bytes : List UInt8) : Option (CircuitAssuranceMessage × List UInt8) := do
  let (time, bytes) ← Alpha.decode 6 bytes
  pure ({ time }, bytes)

@[simp] theorem encode_length (message : CircuitAssuranceMessage) : (encode message).length = 6 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : CircuitAssuranceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CircuitAssuranceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end CircuitAssuranceMessage

/-- Timebeat Message: 9 bytes -/
structure TimebeatMessage where
  timeWithMilliseconds : Alpha 9
  deriving DecidableEq, Repr

namespace TimebeatMessage

def encode (message : TimebeatMessage) : List UInt8 :=
  Alpha.encode message.timeWithMilliseconds

def decode (bytes : List UInt8) : Option (TimebeatMessage × List UInt8) := do
  let (timeWithMilliseconds, bytes) ← Alpha.decode 9 bytes
  pure ({ timeWithMilliseconds }, bytes)

@[simp] theorem encode_length (message : TimebeatMessage) : (encode message).length = 9 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : TimebeatMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TimebeatMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end TimebeatMessage

/-- Any Message Body, selected by Message Type -/
inductive MessageBody where
  | optionTradeMessage (message : OptionTradeMessage) -- "C " 0x4320
  | futureOptionsTradeMessage (message : FutureOptionsTradeMessage) -- "CB" 0x4342
  | futuresTradeMessage (message : FuturesTradeMessage) -- "CF" 0x4346
  | strategyTradeMessage (message : StrategyTradeMessage) -- "CS" 0x4353
  | swapFutureTradeMessage (message : SwapFutureTradeMessage) -- "CW" 0x4357
  | optionRfqMessage (message : OptionRfqMessage) -- "D " 0x4420
  | futureOptionsRfqMessage (message : FutureOptionsRfqMessage) -- "DB" 0x4442
  | futuresRfqMessage (message : FuturesRfqMessage) -- "DF" 0x4446
  | strategyRfqMessage (message : StrategyRfqMessage) -- "DS" 0x4453
  | swapFutureRfqMessage (message : SwapFutureRfqMessage) -- "DW" 0x4457
  | instrumentScheduleNoticeOptionMessage (message : InstrumentScheduleNoticeOptionMessage) -- "E " 0x4520
  | instrumentScheduleNoticeFuturesOptionMessage (message : InstrumentScheduleNoticeFuturesOptionMessage) -- "EB" 0x4542
  | instrumentScheduleNoticeFutureMessage (message : InstrumentScheduleNoticeFutureMessage) -- "EF" 0x4546
  | instrumentScheduleNoticeStrategyMessage (message : InstrumentScheduleNoticeStrategyMessage) -- "ES" 0x4553
  | instrumentScheduleNoticeSwapFutureMessage (message : InstrumentScheduleNoticeSwapFutureMessage) -- "EW" 0x4557
  | optionQuoteMessage (message : OptionQuoteMessage) -- "F " 0x4620
  | futureOptionsQuoteMessage (message : FutureOptionsQuoteMessage) -- "FB" 0x4642
  | futuresQuoteMessage (message : FuturesQuoteMessage) -- "FF" 0x4646
  | strategyQuoteMessage (message : StrategyQuoteMessage) -- "FS" 0x4653
  | swapFutureQuoteMessage (message : SwapFutureQuoteMessage) -- "FW" 0x4657
  | optionMarketDepthMessage (message : OptionMarketDepthMessage) -- "H " 0x4820
  | futureOptionsMarketDepthMessage (message : FutureOptionsMarketDepthMessage) -- "HB" 0x4842
  | futuresMarketDepthMessage (message : FuturesMarketDepthMessage) -- "HF" 0x4846
  | strategyMarketDepthMessage (message : StrategyMarketDepthMessage) -- "HS" 0x4853
  | swapFutureMarketDepthMessage (message : SwapFutureMarketDepthMessage) -- "HW" 0x4857
  | optionTradeCancellationMessage (message : OptionTradeCancellationMessage) -- "I " 0x4920
  | futureOptionsTradeCancellationMessage (message : FutureOptionsTradeCancellationMessage) -- "IB" 0x4942
  | futuresTradeCancellationMessage (message : FuturesTradeCancellationMessage) -- "IF" 0x4946
  | strategyTradeCancellationMessage (message : StrategyTradeCancellationMessage) -- "IS" 0x4953
  | swapFutureTradeCancellationMessage (message : SwapFutureTradeCancellationMessage) -- "IW" 0x4957
  | optionInstrumentKeysMessage (message : OptionInstrumentKeysMessage) -- "J " 0x4A20
  | futureOptionsInstrumentKeysMessage (message : FutureOptionsInstrumentKeysMessage) -- "JB" 0x4A42
  | underlyingInstrumentKeysMessage (message : UnderlyingInstrumentKeysMessage) -- "JE" 0x4A45
  | futuresInstrumentKeysMessage (message : FuturesInstrumentKeysMessage) -- "JF" 0x4A46
  | strategyInstrumentKeysMessage (message : StrategyInstrumentKeysMessage) -- "JS" 0x4A53
  | swapFutureInstrumentKeysMessage (message : SwapFutureInstrumentKeysMessage) -- "JW" 0x4A57
  | optionSummaryMessage (message : OptionSummaryMessage) -- "N " 0x4E20
  | futureOptionsSummaryMessage (message : FutureOptionsSummaryMessage) -- "NB" 0x4E42
  | futuresSummaryMessage (message : FuturesSummaryMessage) -- "NF" 0x4E46
  | strategySummaryMessage (message : StrategySummaryMessage) -- "NS" 0x4E53
  | swapFutureSummaryMessage (message : SwapFutureSummaryMessage) -- "NW" 0x4E57
  | beginningOfOptionsSummaryMessage (message : BeginningOfOptionsSummaryMessage) -- "Q " 0x5120
  | beginningOfFutureOptionsSummaryMessage (message : BeginningOfFutureOptionsSummaryMessage) -- "QB" 0x5142
  | beginningOfFuturesSummaryMessage (message : BeginningOfFuturesSummaryMessage) -- "QF" 0x5146
  | beginningOfStrategySummaryMessage (message : BeginningOfStrategySummaryMessage) -- "QS" 0x5153
  | swapFutureBeginningOfSummaryMessage (message : SwapFutureBeginningOfSummaryMessage) -- "QW" 0x5157
  | optionTradeCorrectionMessage (message : OptionTradeCorrectionMessage) -- "X " 0x5820
  | futureOptionsTradeCorrectionMessage (message : FutureOptionsTradeCorrectionMessage) -- "XB" 0x5842
  | futuresTradeCorrectionMessage (message : FuturesTradeCorrectionMessage) -- "XF" 0x5846
  | strategyTradeCorrectionMessage (message : StrategyTradeCorrectionMessage) -- "XS" 0x5853
  | swapFutureTradeCorrectionMessage (message : SwapFutureTradeCorrectionMessage) -- "XW" 0x5857
  | groupStatusMessage (message : GroupStatusMessage) -- "GR" 0x4752
  | groupStatusStrategiesMessage (message : GroupStatusStrategiesMessage) -- "GS" 0x4753
  | bulletinsMessage (message : BulletinsMessage) -- "L " 0x4C20
  | endOfSalesMessage (message : EndOfSalesMessage) -- "S " 0x5320
  | tickTableMessage (message : TickTableMessage) -- "TT" 0x5454
  | endOfTransmissionMessage (message : EndOfTransmissionMessage) -- "U " 0x5520
  | circuitAssuranceMessage (message : CircuitAssuranceMessage) -- "V " 0x5620
  | timebeatMessage (message : TimebeatMessage) -- "Z " 0x5A20
  deriving DecidableEq, Repr

namespace MessageBody

/-- The Message Type each message is sent under -/
def tag : MessageBody → BitVec 16
  | .optionTradeMessage _ => 17184
  | .futureOptionsTradeMessage _ => 17218
  | .futuresTradeMessage _ => 17222
  | .strategyTradeMessage _ => 17235
  | .swapFutureTradeMessage _ => 17239
  | .optionRfqMessage _ => 17440
  | .futureOptionsRfqMessage _ => 17474
  | .futuresRfqMessage _ => 17478
  | .strategyRfqMessage _ => 17491
  | .swapFutureRfqMessage _ => 17495
  | .instrumentScheduleNoticeOptionMessage _ => 17696
  | .instrumentScheduleNoticeFuturesOptionMessage _ => 17730
  | .instrumentScheduleNoticeFutureMessage _ => 17734
  | .instrumentScheduleNoticeStrategyMessage _ => 17747
  | .instrumentScheduleNoticeSwapFutureMessage _ => 17751
  | .optionQuoteMessage _ => 17952
  | .futureOptionsQuoteMessage _ => 17986
  | .futuresQuoteMessage _ => 17990
  | .strategyQuoteMessage _ => 18003
  | .swapFutureQuoteMessage _ => 18007
  | .optionMarketDepthMessage _ => 18464
  | .futureOptionsMarketDepthMessage _ => 18498
  | .futuresMarketDepthMessage _ => 18502
  | .strategyMarketDepthMessage _ => 18515
  | .swapFutureMarketDepthMessage _ => 18519
  | .optionTradeCancellationMessage _ => 18720
  | .futureOptionsTradeCancellationMessage _ => 18754
  | .futuresTradeCancellationMessage _ => 18758
  | .strategyTradeCancellationMessage _ => 18771
  | .swapFutureTradeCancellationMessage _ => 18775
  | .optionInstrumentKeysMessage _ => 18976
  | .futureOptionsInstrumentKeysMessage _ => 19010
  | .underlyingInstrumentKeysMessage _ => 19013
  | .futuresInstrumentKeysMessage _ => 19014
  | .strategyInstrumentKeysMessage _ => 19027
  | .swapFutureInstrumentKeysMessage _ => 19031
  | .optionSummaryMessage _ => 20000
  | .futureOptionsSummaryMessage _ => 20034
  | .futuresSummaryMessage _ => 20038
  | .strategySummaryMessage _ => 20051
  | .swapFutureSummaryMessage _ => 20055
  | .beginningOfOptionsSummaryMessage _ => 20768
  | .beginningOfFutureOptionsSummaryMessage _ => 20802
  | .beginningOfFuturesSummaryMessage _ => 20806
  | .beginningOfStrategySummaryMessage _ => 20819
  | .swapFutureBeginningOfSummaryMessage _ => 20823
  | .optionTradeCorrectionMessage _ => 22560
  | .futureOptionsTradeCorrectionMessage _ => 22594
  | .futuresTradeCorrectionMessage _ => 22598
  | .strategyTradeCorrectionMessage _ => 22611
  | .swapFutureTradeCorrectionMessage _ => 22615
  | .groupStatusMessage _ => 18258
  | .groupStatusStrategiesMessage _ => 18259
  | .bulletinsMessage _ => 19488
  | .endOfSalesMessage _ => 21280
  | .tickTableMessage _ => 21588
  | .endOfTransmissionMessage _ => 21792
  | .circuitAssuranceMessage _ => 22048
  | .timebeatMessage _ => 23072

def encode : MessageBody → List UInt8
  | .optionTradeMessage message => OptionTradeMessage.encode message
  | .futureOptionsTradeMessage message => FutureOptionsTradeMessage.encode message
  | .futuresTradeMessage message => FuturesTradeMessage.encode message
  | .strategyTradeMessage message => StrategyTradeMessage.encode message
  | .swapFutureTradeMessage message => SwapFutureTradeMessage.encode message
  | .optionRfqMessage message => OptionRfqMessage.encode message
  | .futureOptionsRfqMessage message => FutureOptionsRfqMessage.encode message
  | .futuresRfqMessage message => FuturesRfqMessage.encode message
  | .strategyRfqMessage message => StrategyRfqMessage.encode message
  | .swapFutureRfqMessage message => SwapFutureRfqMessage.encode message
  | .instrumentScheduleNoticeOptionMessage message => InstrumentScheduleNoticeOptionMessage.encode message
  | .instrumentScheduleNoticeFuturesOptionMessage message => InstrumentScheduleNoticeFuturesOptionMessage.encode message
  | .instrumentScheduleNoticeFutureMessage message => InstrumentScheduleNoticeFutureMessage.encode message
  | .instrumentScheduleNoticeStrategyMessage message => InstrumentScheduleNoticeStrategyMessage.encode message
  | .instrumentScheduleNoticeSwapFutureMessage message => InstrumentScheduleNoticeSwapFutureMessage.encode message
  | .optionQuoteMessage message => OptionQuoteMessage.encode message
  | .futureOptionsQuoteMessage message => FutureOptionsQuoteMessage.encode message
  | .futuresQuoteMessage message => FuturesQuoteMessage.encode message
  | .strategyQuoteMessage message => StrategyQuoteMessage.encode message
  | .swapFutureQuoteMessage message => SwapFutureQuoteMessage.encode message
  | .optionMarketDepthMessage message => OptionMarketDepthMessage.encode message
  | .futureOptionsMarketDepthMessage message => FutureOptionsMarketDepthMessage.encode message
  | .futuresMarketDepthMessage message => FuturesMarketDepthMessage.encode message
  | .strategyMarketDepthMessage message => StrategyMarketDepthMessage.encode message
  | .swapFutureMarketDepthMessage message => SwapFutureMarketDepthMessage.encode message
  | .optionTradeCancellationMessage message => OptionTradeCancellationMessage.encode message
  | .futureOptionsTradeCancellationMessage message => FutureOptionsTradeCancellationMessage.encode message
  | .futuresTradeCancellationMessage message => FuturesTradeCancellationMessage.encode message
  | .strategyTradeCancellationMessage message => StrategyTradeCancellationMessage.encode message
  | .swapFutureTradeCancellationMessage message => SwapFutureTradeCancellationMessage.encode message
  | .optionInstrumentKeysMessage message => OptionInstrumentKeysMessage.encode message
  | .futureOptionsInstrumentKeysMessage message => FutureOptionsInstrumentKeysMessage.encode message
  | .underlyingInstrumentKeysMessage message => UnderlyingInstrumentKeysMessage.encode message
  | .futuresInstrumentKeysMessage message => FuturesInstrumentKeysMessage.encode message
  | .strategyInstrumentKeysMessage message => StrategyInstrumentKeysMessage.encode message
  | .swapFutureInstrumentKeysMessage message => SwapFutureInstrumentKeysMessage.encode message
  | .optionSummaryMessage message => OptionSummaryMessage.encode message
  | .futureOptionsSummaryMessage message => FutureOptionsSummaryMessage.encode message
  | .futuresSummaryMessage message => FuturesSummaryMessage.encode message
  | .strategySummaryMessage message => StrategySummaryMessage.encode message
  | .swapFutureSummaryMessage message => SwapFutureSummaryMessage.encode message
  | .beginningOfOptionsSummaryMessage message => BeginningOfOptionsSummaryMessage.encode message
  | .beginningOfFutureOptionsSummaryMessage message => BeginningOfFutureOptionsSummaryMessage.encode message
  | .beginningOfFuturesSummaryMessage message => BeginningOfFuturesSummaryMessage.encode message
  | .beginningOfStrategySummaryMessage message => BeginningOfStrategySummaryMessage.encode message
  | .swapFutureBeginningOfSummaryMessage message => SwapFutureBeginningOfSummaryMessage.encode message
  | .optionTradeCorrectionMessage message => OptionTradeCorrectionMessage.encode message
  | .futureOptionsTradeCorrectionMessage message => FutureOptionsTradeCorrectionMessage.encode message
  | .futuresTradeCorrectionMessage message => FuturesTradeCorrectionMessage.encode message
  | .strategyTradeCorrectionMessage message => StrategyTradeCorrectionMessage.encode message
  | .swapFutureTradeCorrectionMessage message => SwapFutureTradeCorrectionMessage.encode message
  | .groupStatusMessage message => GroupStatusMessage.encode message
  | .groupStatusStrategiesMessage message => GroupStatusStrategiesMessage.encode message
  | .bulletinsMessage message => BulletinsMessage.encode message
  | .endOfSalesMessage message => EndOfSalesMessage.encode message
  | .tickTableMessage message => TickTableMessage.encode message
  | .endOfTransmissionMessage message => EndOfTransmissionMessage.encode message
  | .circuitAssuranceMessage message => CircuitAssuranceMessage.encode message
  | .timebeatMessage message => TimebeatMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : MessageBody) : (encode message).length ≤ 3375 := by
  cases message with
  | optionTradeMessage inner =>
    simp only [encode, OptionTradeMessage.encode_length]
    omega
  | futureOptionsTradeMessage inner =>
    simp only [encode, FutureOptionsTradeMessage.encode_length]
    omega
  | futuresTradeMessage inner =>
    simp only [encode, FuturesTradeMessage.encode_length]
    omega
  | strategyTradeMessage inner =>
    simp only [encode, StrategyTradeMessage.encode_length]
    omega
  | swapFutureTradeMessage inner =>
    simp only [encode, SwapFutureTradeMessage.encode_length]
    omega
  | optionRfqMessage inner =>
    simp only [encode, OptionRfqMessage.encode_length]
    omega
  | futureOptionsRfqMessage inner =>
    simp only [encode, FutureOptionsRfqMessage.encode_length]
    omega
  | futuresRfqMessage inner =>
    simp only [encode, FuturesRfqMessage.encode_length]
    omega
  | strategyRfqMessage inner =>
    simp only [encode, StrategyRfqMessage.encode_length]
    omega
  | swapFutureRfqMessage inner =>
    simp only [encode, SwapFutureRfqMessage.encode_length]
    omega
  | instrumentScheduleNoticeOptionMessage inner =>
    simp only [encode, InstrumentScheduleNoticeOptionMessage.encode_length]
    omega
  | instrumentScheduleNoticeFuturesOptionMessage inner =>
    simp only [encode, InstrumentScheduleNoticeFuturesOptionMessage.encode_length]
    omega
  | instrumentScheduleNoticeFutureMessage inner =>
    simp only [encode, InstrumentScheduleNoticeFutureMessage.encode_length]
    omega
  | instrumentScheduleNoticeStrategyMessage inner =>
    simp only [encode, InstrumentScheduleNoticeStrategyMessage.encode_length]
    omega
  | instrumentScheduleNoticeSwapFutureMessage inner =>
    simp only [encode, InstrumentScheduleNoticeSwapFutureMessage.encode_length]
    omega
  | optionQuoteMessage inner =>
    simp only [encode, OptionQuoteMessage.encode_length]
    omega
  | futureOptionsQuoteMessage inner =>
    simp only [encode, FutureOptionsQuoteMessage.encode_length]
    omega
  | futuresQuoteMessage inner =>
    simp only [encode, FuturesQuoteMessage.encode_length]
    omega
  | strategyQuoteMessage inner =>
    simp only [encode, StrategyQuoteMessage.encode_length]
    omega
  | swapFutureQuoteMessage inner =>
    simp only [encode, SwapFutureQuoteMessage.encode_length]
    omega
  | optionMarketDepthMessage inner =>
    have bound_inner := OptionMarketDepthMessage.encode_length_le inner
    simp only [encode]
    omega
  | futureOptionsMarketDepthMessage inner =>
    have bound_inner := FutureOptionsMarketDepthMessage.encode_length_le inner
    simp only [encode]
    omega
  | futuresMarketDepthMessage inner =>
    have bound_inner := FuturesMarketDepthMessage.encode_length_le inner
    simp only [encode]
    omega
  | strategyMarketDepthMessage inner =>
    have bound_inner := StrategyMarketDepthMessage.encode_length_le inner
    simp only [encode]
    omega
  | swapFutureMarketDepthMessage inner =>
    have bound_inner := SwapFutureMarketDepthMessage.encode_length_le inner
    simp only [encode]
    omega
  | optionTradeCancellationMessage inner =>
    simp only [encode, OptionTradeCancellationMessage.encode_length]
    omega
  | futureOptionsTradeCancellationMessage inner =>
    simp only [encode, FutureOptionsTradeCancellationMessage.encode_length]
    omega
  | futuresTradeCancellationMessage inner =>
    simp only [encode, FuturesTradeCancellationMessage.encode_length]
    omega
  | strategyTradeCancellationMessage inner =>
    simp only [encode, StrategyTradeCancellationMessage.encode_length]
    omega
  | swapFutureTradeCancellationMessage inner =>
    simp only [encode, SwapFutureTradeCancellationMessage.encode_length]
    omega
  | optionInstrumentKeysMessage inner =>
    simp only [encode, OptionInstrumentKeysMessage.encode_length]
    omega
  | futureOptionsInstrumentKeysMessage inner =>
    simp only [encode, FutureOptionsInstrumentKeysMessage.encode_length]
    omega
  | underlyingInstrumentKeysMessage inner =>
    simp only [encode, UnderlyingInstrumentKeysMessage.encode_length]
    omega
  | futuresInstrumentKeysMessage inner =>
    simp only [encode, FuturesInstrumentKeysMessage.encode_length]
    omega
  | strategyInstrumentKeysMessage inner =>
    simp only [encode, StrategyInstrumentKeysMessage.encode_length]
    omega
  | swapFutureInstrumentKeysMessage inner =>
    simp only [encode, SwapFutureInstrumentKeysMessage.encode_length]
    omega
  | optionSummaryMessage inner =>
    simp only [encode, OptionSummaryMessage.encode_length]
    omega
  | futureOptionsSummaryMessage inner =>
    simp only [encode, FutureOptionsSummaryMessage.encode_length]
    omega
  | futuresSummaryMessage inner =>
    simp only [encode, FuturesSummaryMessage.encode_length]
    omega
  | strategySummaryMessage inner =>
    have bound_inner := StrategySummaryMessage.encode_length_le inner
    simp only [encode]
    omega
  | swapFutureSummaryMessage inner =>
    simp only [encode, SwapFutureSummaryMessage.encode_length]
    omega
  | beginningOfOptionsSummaryMessage inner =>
    simp only [encode, BeginningOfOptionsSummaryMessage.encode_length]
    omega
  | beginningOfFutureOptionsSummaryMessage inner =>
    simp only [encode, BeginningOfFutureOptionsSummaryMessage.encode_length]
    omega
  | beginningOfFuturesSummaryMessage inner =>
    simp only [encode, BeginningOfFuturesSummaryMessage.encode_length]
    omega
  | beginningOfStrategySummaryMessage inner =>
    simp only [encode, BeginningOfStrategySummaryMessage.encode_length]
    omega
  | swapFutureBeginningOfSummaryMessage inner =>
    simp only [encode, SwapFutureBeginningOfSummaryMessage.encode_length]
    omega
  | optionTradeCorrectionMessage inner =>
    simp only [encode, OptionTradeCorrectionMessage.encode_length]
    omega
  | futureOptionsTradeCorrectionMessage inner =>
    simp only [encode, FutureOptionsTradeCorrectionMessage.encode_length]
    omega
  | futuresTradeCorrectionMessage inner =>
    simp only [encode, FuturesTradeCorrectionMessage.encode_length]
    omega
  | strategyTradeCorrectionMessage inner =>
    simp only [encode, StrategyTradeCorrectionMessage.encode_length]
    omega
  | swapFutureTradeCorrectionMessage inner =>
    simp only [encode, SwapFutureTradeCorrectionMessage.encode_length]
    omega
  | groupStatusMessage inner =>
    simp only [encode, GroupStatusMessage.encode_length]
    omega
  | groupStatusStrategiesMessage inner =>
    simp only [encode, GroupStatusStrategiesMessage.encode_length]
    omega
  | bulletinsMessage inner =>
    have bound_inner := BulletinsMessage.encode_length_le inner
    simp only [encode]
    omega
  | endOfSalesMessage inner =>
    simp only [encode, EndOfSalesMessage.encode_length]
    omega
  | tickTableMessage inner =>
    have bound_inner := TickTableMessage.encode_length_le inner
    simp only [encode]
    omega
  | endOfTransmissionMessage inner =>
    simp only [encode, EndOfTransmissionMessage.encode_length]
    omega
  | circuitAssuranceMessage inner =>
    simp only [encode, CircuitAssuranceMessage.encode_length]
    omega
  | timebeatMessage inner =>
    simp only [encode, TimebeatMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (MessageBody × List UInt8) :=
  if tag = 17184 then (OptionTradeMessage.decode bytes).map fun (message, rest) => (.optionTradeMessage message, rest)
  else if tag = 17218 then (FutureOptionsTradeMessage.decode bytes).map fun (message, rest) => (.futureOptionsTradeMessage message, rest)
  else if tag = 17222 then (FuturesTradeMessage.decode bytes).map fun (message, rest) => (.futuresTradeMessage message, rest)
  else if tag = 17235 then (StrategyTradeMessage.decode bytes).map fun (message, rest) => (.strategyTradeMessage message, rest)
  else if tag = 17239 then (SwapFutureTradeMessage.decode bytes).map fun (message, rest) => (.swapFutureTradeMessage message, rest)
  else if tag = 17440 then (OptionRfqMessage.decode bytes).map fun (message, rest) => (.optionRfqMessage message, rest)
  else if tag = 17474 then (FutureOptionsRfqMessage.decode bytes).map fun (message, rest) => (.futureOptionsRfqMessage message, rest)
  else if tag = 17478 then (FuturesRfqMessage.decode bytes).map fun (message, rest) => (.futuresRfqMessage message, rest)
  else if tag = 17491 then (StrategyRfqMessage.decode bytes).map fun (message, rest) => (.strategyRfqMessage message, rest)
  else if tag = 17495 then (SwapFutureRfqMessage.decode bytes).map fun (message, rest) => (.swapFutureRfqMessage message, rest)
  else if tag = 17696 then (InstrumentScheduleNoticeOptionMessage.decode bytes).map fun (message, rest) => (.instrumentScheduleNoticeOptionMessage message, rest)
  else if tag = 17730 then (InstrumentScheduleNoticeFuturesOptionMessage.decode bytes).map fun (message, rest) => (.instrumentScheduleNoticeFuturesOptionMessage message, rest)
  else if tag = 17734 then (InstrumentScheduleNoticeFutureMessage.decode bytes).map fun (message, rest) => (.instrumentScheduleNoticeFutureMessage message, rest)
  else if tag = 17747 then (InstrumentScheduleNoticeStrategyMessage.decode bytes).map fun (message, rest) => (.instrumentScheduleNoticeStrategyMessage message, rest)
  else if tag = 17751 then (InstrumentScheduleNoticeSwapFutureMessage.decode bytes).map fun (message, rest) => (.instrumentScheduleNoticeSwapFutureMessage message, rest)
  else if tag = 17952 then (OptionQuoteMessage.decode bytes).map fun (message, rest) => (.optionQuoteMessage message, rest)
  else if tag = 17986 then (FutureOptionsQuoteMessage.decode bytes).map fun (message, rest) => (.futureOptionsQuoteMessage message, rest)
  else if tag = 17990 then (FuturesQuoteMessage.decode bytes).map fun (message, rest) => (.futuresQuoteMessage message, rest)
  else if tag = 18003 then (StrategyQuoteMessage.decode bytes).map fun (message, rest) => (.strategyQuoteMessage message, rest)
  else if tag = 18007 then (SwapFutureQuoteMessage.decode bytes).map fun (message, rest) => (.swapFutureQuoteMessage message, rest)
  else if tag = 18464 then (OptionMarketDepthMessage.decode bytes).map fun (message, rest) => (.optionMarketDepthMessage message, rest)
  else if tag = 18498 then (FutureOptionsMarketDepthMessage.decode bytes).map fun (message, rest) => (.futureOptionsMarketDepthMessage message, rest)
  else if tag = 18502 then (FuturesMarketDepthMessage.decode bytes).map fun (message, rest) => (.futuresMarketDepthMessage message, rest)
  else if tag = 18515 then (StrategyMarketDepthMessage.decode bytes).map fun (message, rest) => (.strategyMarketDepthMessage message, rest)
  else if tag = 18519 then (SwapFutureMarketDepthMessage.decode bytes).map fun (message, rest) => (.swapFutureMarketDepthMessage message, rest)
  else if tag = 18720 then (OptionTradeCancellationMessage.decode bytes).map fun (message, rest) => (.optionTradeCancellationMessage message, rest)
  else if tag = 18754 then (FutureOptionsTradeCancellationMessage.decode bytes).map fun (message, rest) => (.futureOptionsTradeCancellationMessage message, rest)
  else if tag = 18758 then (FuturesTradeCancellationMessage.decode bytes).map fun (message, rest) => (.futuresTradeCancellationMessage message, rest)
  else if tag = 18771 then (StrategyTradeCancellationMessage.decode bytes).map fun (message, rest) => (.strategyTradeCancellationMessage message, rest)
  else if tag = 18775 then (SwapFutureTradeCancellationMessage.decode bytes).map fun (message, rest) => (.swapFutureTradeCancellationMessage message, rest)
  else if tag = 18976 then (OptionInstrumentKeysMessage.decode bytes).map fun (message, rest) => (.optionInstrumentKeysMessage message, rest)
  else if tag = 19010 then (FutureOptionsInstrumentKeysMessage.decode bytes).map fun (message, rest) => (.futureOptionsInstrumentKeysMessage message, rest)
  else if tag = 19013 then (UnderlyingInstrumentKeysMessage.decode bytes).map fun (message, rest) => (.underlyingInstrumentKeysMessage message, rest)
  else if tag = 19014 then (FuturesInstrumentKeysMessage.decode bytes).map fun (message, rest) => (.futuresInstrumentKeysMessage message, rest)
  else if tag = 19027 then (StrategyInstrumentKeysMessage.decode bytes).map fun (message, rest) => (.strategyInstrumentKeysMessage message, rest)
  else if tag = 19031 then (SwapFutureInstrumentKeysMessage.decode bytes).map fun (message, rest) => (.swapFutureInstrumentKeysMessage message, rest)
  else if tag = 20000 then (OptionSummaryMessage.decode bytes).map fun (message, rest) => (.optionSummaryMessage message, rest)
  else if tag = 20034 then (FutureOptionsSummaryMessage.decode bytes).map fun (message, rest) => (.futureOptionsSummaryMessage message, rest)
  else if tag = 20038 then (FuturesSummaryMessage.decode bytes).map fun (message, rest) => (.futuresSummaryMessage message, rest)
  else if tag = 20051 then (StrategySummaryMessage.decode bytes).map fun (message, rest) => (.strategySummaryMessage message, rest)
  else if tag = 20055 then (SwapFutureSummaryMessage.decode bytes).map fun (message, rest) => (.swapFutureSummaryMessage message, rest)
  else if tag = 20768 then (BeginningOfOptionsSummaryMessage.decode bytes).map fun (message, rest) => (.beginningOfOptionsSummaryMessage message, rest)
  else if tag = 20802 then (BeginningOfFutureOptionsSummaryMessage.decode bytes).map fun (message, rest) => (.beginningOfFutureOptionsSummaryMessage message, rest)
  else if tag = 20806 then (BeginningOfFuturesSummaryMessage.decode bytes).map fun (message, rest) => (.beginningOfFuturesSummaryMessage message, rest)
  else if tag = 20819 then (BeginningOfStrategySummaryMessage.decode bytes).map fun (message, rest) => (.beginningOfStrategySummaryMessage message, rest)
  else if tag = 20823 then (SwapFutureBeginningOfSummaryMessage.decode bytes).map fun (message, rest) => (.swapFutureBeginningOfSummaryMessage message, rest)
  else if tag = 22560 then (OptionTradeCorrectionMessage.decode bytes).map fun (message, rest) => (.optionTradeCorrectionMessage message, rest)
  else if tag = 22594 then (FutureOptionsTradeCorrectionMessage.decode bytes).map fun (message, rest) => (.futureOptionsTradeCorrectionMessage message, rest)
  else if tag = 22598 then (FuturesTradeCorrectionMessage.decode bytes).map fun (message, rest) => (.futuresTradeCorrectionMessage message, rest)
  else if tag = 22611 then (StrategyTradeCorrectionMessage.decode bytes).map fun (message, rest) => (.strategyTradeCorrectionMessage message, rest)
  else if tag = 22615 then (SwapFutureTradeCorrectionMessage.decode bytes).map fun (message, rest) => (.swapFutureTradeCorrectionMessage message, rest)
  else if tag = 18258 then (GroupStatusMessage.decode bytes).map fun (message, rest) => (.groupStatusMessage message, rest)
  else if tag = 18259 then (GroupStatusStrategiesMessage.decode bytes).map fun (message, rest) => (.groupStatusStrategiesMessage message, rest)
  else if tag = 19488 then (BulletinsMessage.decode bytes).map fun (message, rest) => (.bulletinsMessage message, rest)
  else if tag = 21280 then (EndOfSalesMessage.decode bytes).map fun (message, rest) => (.endOfSalesMessage message, rest)
  else if tag = 21588 then (TickTableMessage.decode bytes).map fun (message, rest) => (.tickTableMessage message, rest)
  else if tag = 21792 then (EndOfTransmissionMessage.decode bytes).map fun (message, rest) => (.endOfTransmissionMessage message, rest)
  else if tag = 22048 then (CircuitAssuranceMessage.decode bytes).map fun (message, rest) => (.circuitAssuranceMessage message, rest)
  else if tag = 23072 then (TimebeatMessage.decode bytes).map fun (message, rest) => (.timebeatMessage message, rest)
  else none

@[simp] theorem decode_encode (message : MessageBody) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end MessageBody

/-- Sola Frame -/
structure SolaFrame where
  solaMessageStart : BitVec 8
  sequenceNumber : Alpha 9
  messageBody : MessageBody
  solaMessageEnd : BitVec 8
  deriving DecidableEq, Repr

namespace SolaFrame

def encode (message : SolaFrame) : List UInt8 :=
  encodeUInt 1 message.solaMessageStart
    ++ (Alpha.encode message.sequenceNumber
    ++ (encodeUInt 2 (MessageBody.tag message.messageBody)
    ++ (MessageBody.encode message.messageBody
    ++ (encodeUInt 1 message.solaMessageEnd))))

def decode (bytes : List UInt8) : Option (SolaFrame × List UInt8) := do
  let (solaMessageStart, bytes) ← decodeUInt 1 bytes
  let (sequenceNumber, bytes) ← Alpha.decode 9 bytes
  let (messageType, bytes) ← decodeUInt 2 bytes
  let (messageBody, bytes) ← MessageBody.decode messageType bytes
  let (solaMessageEnd, bytes) ← decodeUInt 1 bytes
  pure ({ solaMessageStart, sequenceNumber, messageBody, solaMessageEnd }, bytes)

theorem encode_length_pos (message : SolaFrame) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SolaFrame) : (encode message).length ≤ 3388 := by
  unfold encode
  cases message.messageBody with
  | optionTradeMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OptionTradeMessage.encode_length]
    omega
  | futureOptionsTradeMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FutureOptionsTradeMessage.encode_length]
    omega
  | futuresTradeMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FuturesTradeMessage.encode_length]
    omega
  | strategyTradeMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, StrategyTradeMessage.encode_length]
    omega
  | swapFutureTradeMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, SwapFutureTradeMessage.encode_length]
    omega
  | optionRfqMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OptionRfqMessage.encode_length]
    omega
  | futureOptionsRfqMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FutureOptionsRfqMessage.encode_length]
    omega
  | futuresRfqMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FuturesRfqMessage.encode_length]
    omega
  | strategyRfqMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, StrategyRfqMessage.encode_length]
    omega
  | swapFutureRfqMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, SwapFutureRfqMessage.encode_length]
    omega
  | instrumentScheduleNoticeOptionMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, InstrumentScheduleNoticeOptionMessage.encode_length]
    omega
  | instrumentScheduleNoticeFuturesOptionMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, InstrumentScheduleNoticeFuturesOptionMessage.encode_length]
    omega
  | instrumentScheduleNoticeFutureMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, InstrumentScheduleNoticeFutureMessage.encode_length]
    omega
  | instrumentScheduleNoticeStrategyMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, InstrumentScheduleNoticeStrategyMessage.encode_length]
    omega
  | instrumentScheduleNoticeSwapFutureMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, InstrumentScheduleNoticeSwapFutureMessage.encode_length]
    omega
  | optionQuoteMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OptionQuoteMessage.encode_length]
    omega
  | futureOptionsQuoteMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FutureOptionsQuoteMessage.encode_length]
    omega
  | futuresQuoteMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FuturesQuoteMessage.encode_length]
    omega
  | strategyQuoteMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, StrategyQuoteMessage.encode_length]
    omega
  | swapFutureQuoteMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, SwapFutureQuoteMessage.encode_length]
    omega
  | optionMarketDepthMessage inner =>
    have bound_inner := OptionMarketDepthMessage.encode_length_le inner
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
    omega
  | futureOptionsMarketDepthMessage inner =>
    have bound_inner := FutureOptionsMarketDepthMessage.encode_length_le inner
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
    omega
  | futuresMarketDepthMessage inner =>
    have bound_inner := FuturesMarketDepthMessage.encode_length_le inner
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
    omega
  | strategyMarketDepthMessage inner =>
    have bound_inner := StrategyMarketDepthMessage.encode_length_le inner
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
    omega
  | swapFutureMarketDepthMessage inner =>
    have bound_inner := SwapFutureMarketDepthMessage.encode_length_le inner
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
    omega
  | optionTradeCancellationMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OptionTradeCancellationMessage.encode_length]
    omega
  | futureOptionsTradeCancellationMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FutureOptionsTradeCancellationMessage.encode_length]
    omega
  | futuresTradeCancellationMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FuturesTradeCancellationMessage.encode_length]
    omega
  | strategyTradeCancellationMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, StrategyTradeCancellationMessage.encode_length]
    omega
  | swapFutureTradeCancellationMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, SwapFutureTradeCancellationMessage.encode_length]
    omega
  | optionInstrumentKeysMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OptionInstrumentKeysMessage.encode_length]
    omega
  | futureOptionsInstrumentKeysMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FutureOptionsInstrumentKeysMessage.encode_length]
    omega
  | underlyingInstrumentKeysMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, UnderlyingInstrumentKeysMessage.encode_length]
    omega
  | futuresInstrumentKeysMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FuturesInstrumentKeysMessage.encode_length]
    omega
  | strategyInstrumentKeysMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, StrategyInstrumentKeysMessage.encode_length]
    omega
  | swapFutureInstrumentKeysMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, SwapFutureInstrumentKeysMessage.encode_length]
    omega
  | optionSummaryMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OptionSummaryMessage.encode_length]
    omega
  | futureOptionsSummaryMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FutureOptionsSummaryMessage.encode_length]
    omega
  | futuresSummaryMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FuturesSummaryMessage.encode_length]
    omega
  | strategySummaryMessage inner =>
    have bound_inner := StrategySummaryMessage.encode_length_le inner
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
    omega
  | swapFutureSummaryMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, SwapFutureSummaryMessage.encode_length]
    omega
  | beginningOfOptionsSummaryMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, BeginningOfOptionsSummaryMessage.encode_length]
    omega
  | beginningOfFutureOptionsSummaryMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, BeginningOfFutureOptionsSummaryMessage.encode_length]
    omega
  | beginningOfFuturesSummaryMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, BeginningOfFuturesSummaryMessage.encode_length]
    omega
  | beginningOfStrategySummaryMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, BeginningOfStrategySummaryMessage.encode_length]
    omega
  | swapFutureBeginningOfSummaryMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, SwapFutureBeginningOfSummaryMessage.encode_length]
    omega
  | optionTradeCorrectionMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OptionTradeCorrectionMessage.encode_length]
    omega
  | futureOptionsTradeCorrectionMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FutureOptionsTradeCorrectionMessage.encode_length]
    omega
  | futuresTradeCorrectionMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FuturesTradeCorrectionMessage.encode_length]
    omega
  | strategyTradeCorrectionMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, StrategyTradeCorrectionMessage.encode_length]
    omega
  | swapFutureTradeCorrectionMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, SwapFutureTradeCorrectionMessage.encode_length]
    omega
  | groupStatusMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, GroupStatusMessage.encode_length]
    omega
  | groupStatusStrategiesMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, GroupStatusStrategiesMessage.encode_length]
    omega
  | bulletinsMessage inner =>
    have bound_inner := BulletinsMessage.encode_length_le inner
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
    omega
  | endOfSalesMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, EndOfSalesMessage.encode_length]
    omega
  | tickTableMessage inner =>
    have bound_inner := TickTableMessage.encode_length_le inner
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
    omega
  | endOfTransmissionMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, EndOfTransmissionMessage.encode_length]
    omega
  | circuitAssuranceMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, CircuitAssuranceMessage.encode_length]
    omega
  | timebeatMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, TimebeatMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : SolaFrame) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MessageBody.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SolaFrame

/-- Packet -/
structure Packet where
  solaFrame : List SolaFrame
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeMany SolaFrame.encode message.solaFrame

def decode (bytes : List UInt8) : Option Packet := do
  let solaFrame ← decodeAll SolaFrame.decode bytes.length bytes
  pure { solaFrame }

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany SolaFrame.encode SolaFrame.decode SolaFrame.decode_encode SolaFrame.encode_length_pos message.solaFrame _ (encodeMany_length_ge SolaFrame.encode SolaFrame.encode_length_pos message.solaFrame), some_bind]
  rfl

end Packet

end Omi.TmxMxSolamulticastHsvfV111
