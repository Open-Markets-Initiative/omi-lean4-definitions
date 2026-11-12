import Wire

/-!
# TMX Group Sola Multicast v1.14.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.

Note: Strike Price Fraction Pair is 8 bytes whichever arm the model names: its arms lay their bytes
out alike and differ only in what they are called and what they mean, which Strike Price Fraction
Indicator says (Strike Price Negative Whole Pair, Strike Price Negative Ten Pair, Strike Price
Negative Hundred Pair, Strike Price Negative Thousand Pair, Strike Price Negative Ten Thousand Pair,
Strike Price Negative Hundred Thousand Pair, Strike Price Negative Million Pair, Strike Price
Numeric Pair). It is read as Strike Price Negative Whole Pair's fields, so which arm applies is left
to what is built on the definition.

Note: Trade Price Fraction Pair is 8 bytes whichever arm the model names: its arms lay their bytes
out alike and differ only in what they are called and what they mean, which Trade Price Fraction
Indicator says (Trade Price Negative Whole Pair, Trade Price Negative Ten Pair, Trade Price Negative
Hundred Pair, Trade Price Negative Thousand Pair, Trade Price Negative Ten Thousand Pair, Trade
Price Negative Hundred Thousand Pair, Trade Price Negative Million Pair, Trade Price Numeric Pair).
It is read as Trade Price Negative Whole Pair's fields, so which arm applies is left to what is
built on the definition.

Note: Net Change Fraction Pair is 8 bytes whichever arm the model names: its arms lay their bytes
out alike and differ only in what they are called and what they mean, which Net Change Fraction
Indicator says (Net Change Negative Whole Pair, Net Change Negative Ten Pair, Net Change Negative
Hundred Pair, Net Change Negative Thousand Pair, Net Change Negative Ten Thousand Pair, Net Change
Negative Hundred Thousand Pair, Net Change Negative Million Pair, Net Change Numeric Pair). It is
read as Net Change Negative Whole Pair's fields, so which arm applies is left to what is built on
the definition.

Note: Net Change Future Options Trade Message Fraction Pair is 8 bytes whichever arm the model
names: its arms lay their bytes out alike and differ only in what they are called and what they
mean, which Net Change Fraction Indicator says (Net Change Future Options Trade Message Negative
Whole Pair, Net Change Future Options Trade Message Negative Ten Pair, Net Change Future Options
Trade Message Negative Hundred Pair, Net Change Future Options Trade Message Negative Thousand Pair,
Net Change Future Options Trade Message Negative Ten Thousand Pair, Net Change Future Options Trade
Message Negative Hundred Thousand Pair, Net Change Future Options Trade Message Negative Million
Pair, Net Change Future Options Trade Message Numeric Pair). It is read as Net Change Future Options
Trade Message Negative Whole Pair's fields, so which arm applies is left to what is built on the
definition.

Note: Net Change Futures Trade Message Fraction Pair is 8 bytes whichever arm the model names: its
arms lay their bytes out alike and differ only in what they are called and what they mean, which Net
Change Fraction Indicator says (Net Change Futures Trade Message Negative Whole Pair, Net Change
Futures Trade Message Negative Ten Pair, Net Change Futures Trade Message Negative Hundred Pair, Net
Change Futures Trade Message Negative Thousand Pair, Net Change Futures Trade Message Negative Ten
Thousand Pair, Net Change Futures Trade Message Negative Hundred Thousand Pair, Net Change Futures
Trade Message Negative Million Pair, Net Change Futures Trade Message Numeric Pair). It is read as
Net Change Futures Trade Message Negative Whole Pair's fields, so which arm applies is left to what
is built on the definition.

Note: Strike Price Schedule Notice Fraction Pair is 8 bytes whichever arm the model names: its arms
lay their bytes out alike and differ only in what they are called and what they mean, which Strike
Price Fraction Indicator says (Strike Price Schedule Notice Negative Whole Pair, Strike Price
Schedule Notice Negative Ten Pair, Strike Price Schedule Notice Negative Hundred Pair, Strike Price
Schedule Notice Negative Thousand Pair, Strike Price Schedule Notice Negative Ten Thousand Pair,
Strike Price Schedule Notice Negative Hundred Thousand Pair, Strike Price Schedule Notice Negative
Million Pair, Strike Price Schedule Notice Numeric Pair). It is read as Strike Price Schedule Notice
Negative Whole Pair's fields, so which arm applies is left to what is built on the definition.

Note: Bid Price Quote is 8 bytes whichever arm the model names: its arms lay their bytes out alike
and differ only in what they are called and what they mean, which Bid Price Quote Opening says (Bid
Price Quote Opening Pair, Bid Price Quote Numeric Negative Whole Pair, Bid Price Quote Numeric
Negative Ten Pair, Bid Price Quote Numeric Negative Hundred Pair, Bid Price Quote Numeric Negative
Thousand Pair, Bid Price Quote Numeric Negative Ten Thousand Pair, Bid Price Quote Numeric Negative
Hundred Thousand Pair, Bid Price Quote Numeric Negative Million Pair, Bid Price Quote Numeric Pair).
It is read as Bid Price Quote Numeric Negative Whole Pair's fields, so which arm applies is left to
what is built on the definition.

Note: Ask Price Quote is 8 bytes whichever arm the model names: its arms lay their bytes out alike
and differ only in what they are called and what they mean, which Ask Price Quote Opening says (Ask
Price Quote Opening Pair, Ask Price Quote Numeric Negative Whole Pair, Ask Price Quote Numeric
Negative Ten Pair, Ask Price Quote Numeric Negative Hundred Pair, Ask Price Quote Numeric Negative
Thousand Pair, Ask Price Quote Numeric Negative Ten Thousand Pair, Ask Price Quote Numeric Negative
Hundred Thousand Pair, Ask Price Quote Numeric Negative Million Pair, Ask Price Quote Numeric Pair).
It is read as Ask Price Quote Numeric Negative Whole Pair's fields, so which arm applies is left to
what is built on the definition.

Note: Bid Price Quote Futures Quote Message is 8 bytes whichever arm the model names: its arms lay
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

Note: Ask Price Quote Futures Quote Message is 8 bytes whichever arm the model names: its arms lay
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

Note: Bid Price Quote Market Depth Level is 8 bytes whichever arm the model names: its arms lay
their bytes out alike and differ only in what they are called and what they mean, which Bid Price
Quote Opening says (Bid Price Quote Market Depth Level Opening Pair, Bid Price Quote Numeric Bid
Price Quote Market Depth Level Numeric Pair Negative Whole Pair, Bid Price Quote Numeric Bid Price
Quote Market Depth Level Numeric Pair Negative Ten Pair, Bid Price Quote Numeric Bid Price Quote
Market Depth Level Numeric Pair Negative Hundred Pair, Bid Price Quote Numeric Bid Price Quote
Market Depth Level Numeric Pair Negative Thousand Pair, Bid Price Quote Numeric Bid Price Quote
Market Depth Level Numeric Pair Negative Ten Thousand Pair, Bid Price Quote Numeric Bid Price Quote
Market Depth Level Numeric Pair Negative Hundred Thousand Pair, Bid Price Quote Numeric Bid Price
Quote Market Depth Level Numeric Pair Negative Million Pair, Bid Price Quote Market Depth Level
Numeric Pair). It is read as Bid Price Quote Numeric Bid Price Quote Market Depth Level Numeric Pair
Negative Whole Pair's fields, so which arm applies is left to what is built on the definition.

Note: Ask Price Quote Market Depth Level is 8 bytes whichever arm the model names: its arms lay
their bytes out alike and differ only in what they are called and what they mean, which Ask Price
Quote Opening says (Ask Price Quote Market Depth Level Opening Pair, Ask Price Quote Numeric Ask
Price Quote Market Depth Level Numeric Pair Negative Whole Pair, Ask Price Quote Numeric Ask Price
Quote Market Depth Level Numeric Pair Negative Ten Pair, Ask Price Quote Numeric Ask Price Quote
Market Depth Level Numeric Pair Negative Hundred Pair, Ask Price Quote Numeric Ask Price Quote
Market Depth Level Numeric Pair Negative Thousand Pair, Ask Price Quote Numeric Ask Price Quote
Market Depth Level Numeric Pair Negative Ten Thousand Pair, Ask Price Quote Numeric Ask Price Quote
Market Depth Level Numeric Pair Negative Hundred Thousand Pair, Ask Price Quote Numeric Ask Price
Quote Market Depth Level Numeric Pair Negative Million Pair, Ask Price Quote Market Depth Level
Numeric Pair). It is read as Ask Price Quote Numeric Ask Price Quote Market Depth Level Numeric Pair
Negative Whole Pair's fields, so which arm applies is left to what is built on the definition.

Note: Number Of Levels counts Market Depth Level in ascii digits: it is written from the list as its
digits, and a list of more than 9 could not be written

Note: Bid Price Quote Market Depth Level HB is 8 bytes whichever arm the model names: its arms lay
their bytes out alike and differ only in what they are called and what they mean, which Bid Price
Quote Opening says (Bid Price Quote Market Depth Level HB Opening Pair, Bid Price Quote Numeric Bid
Price Quote Market Depth Level HB Numeric Pair Negative Whole Pair, Bid Price Quote Numeric Bid
Price Quote Market Depth Level HB Numeric Pair Negative Ten Pair, Bid Price Quote Numeric Bid Price
Quote Market Depth Level HB Numeric Pair Negative Hundred Pair, Bid Price Quote Numeric Bid Price
Quote Market Depth Level HB Numeric Pair Negative Thousand Pair, Bid Price Quote Numeric Bid Price
Quote Market Depth Level HB Numeric Pair Negative Ten Thousand Pair, Bid Price Quote Numeric Bid
Price Quote Market Depth Level HB Numeric Pair Negative Hundred Thousand Pair, Bid Price Quote
Numeric Bid Price Quote Market Depth Level HB Numeric Pair Negative Million Pair, Bid Price Quote
Market Depth Level HB Numeric Pair). It is read as Bid Price Quote Numeric Bid Price Quote Market
Depth Level HB Numeric Pair Negative Whole Pair's fields, so which arm applies is left to what is
built on the definition.

Note: Ask Price Quote Market Depth Level HB is 8 bytes whichever arm the model names: its arms lay
their bytes out alike and differ only in what they are called and what they mean, which Ask Price
Quote Opening says (Ask Price Quote Market Depth Level HB Opening Pair, Ask Price Quote Numeric Ask
Price Quote Market Depth Level HB Numeric Pair Negative Whole Pair, Ask Price Quote Numeric Ask
Price Quote Market Depth Level HB Numeric Pair Negative Ten Pair, Ask Price Quote Numeric Ask Price
Quote Market Depth Level HB Numeric Pair Negative Hundred Pair, Ask Price Quote Numeric Ask Price
Quote Market Depth Level HB Numeric Pair Negative Thousand Pair, Ask Price Quote Numeric Ask Price
Quote Market Depth Level HB Numeric Pair Negative Ten Thousand Pair, Ask Price Quote Numeric Ask
Price Quote Market Depth Level HB Numeric Pair Negative Hundred Thousand Pair, Ask Price Quote
Numeric Ask Price Quote Market Depth Level HB Numeric Pair Negative Million Pair, Ask Price Quote
Market Depth Level HB Numeric Pair). It is read as Ask Price Quote Numeric Ask Price Quote Market
Depth Level HB Numeric Pair Negative Whole Pair's fields, so which arm applies is left to what is
built on the definition.

Note: Number Of Levels counts Future Options Market Depth Level in ascii digits: it is written from
the list as its digits, and a list of more than 9 could not be written

Note: Bid Price Quote Market Depth Level HF is 8 bytes whichever arm the model names: its arms lay
their bytes out alike and differ only in what they are called and what they mean, which Bid Price
Quote Opening says (Bid Price Quote Market Depth Level HF Opening Pair, Bid Price Quote Numeric Bid
Price Quote Market Depth Level HF Numeric Pair Negative Whole Pair, Bid Price Quote Numeric Bid
Price Quote Market Depth Level HF Numeric Pair Negative Ten Pair, Bid Price Quote Numeric Bid Price
Quote Market Depth Level HF Numeric Pair Negative Hundred Pair, Bid Price Quote Numeric Bid Price
Quote Market Depth Level HF Numeric Pair Negative Thousand Pair, Bid Price Quote Numeric Bid Price
Quote Market Depth Level HF Numeric Pair Negative Ten Thousand Pair, Bid Price Quote Numeric Bid
Price Quote Market Depth Level HF Numeric Pair Negative Hundred Thousand Pair, Bid Price Quote
Numeric Bid Price Quote Market Depth Level HF Numeric Pair Negative Million Pair, Bid Price Quote
Market Depth Level HF Numeric Pair). It is read as Bid Price Quote Numeric Bid Price Quote Market
Depth Level HF Numeric Pair Negative Whole Pair's fields, so which arm applies is left to what is
built on the definition.

Note: Ask Price Futures Depth Market Depth Level HF is 8 bytes whichever arm the model names: its
arms lay their bytes out alike and differ only in what they are called and what they mean, which Ask
Price Futures Depth Opening says (Ask Price Futures Depth Market Depth Level HF Opening Pair, Ask
Price Futures Depth Numeric Negative Whole Pair, Ask Price Futures Depth Numeric Negative Ten Pair,
Ask Price Futures Depth Numeric Negative Hundred Pair, Ask Price Futures Depth Numeric Negative
Thousand Pair, Ask Price Futures Depth Numeric Negative Ten Thousand Pair, Ask Price Futures Depth
Numeric Negative Hundred Thousand Pair, Ask Price Futures Depth Numeric Negative Million Pair, Ask
Price Futures Depth Market Depth Level HF Numeric Pair). It is read as Ask Price Futures Depth
Numeric Negative Whole Pair's fields, so which arm applies is left to what is built on the
definition.

Note: Number Of Levels counts Futures Market Depth Level in ascii digits: it is written from the
list as its digits, and a list of more than 9 could not be written

Note: Bid Price Quote Strategy Market Depth Level is 8 bytes whichever arm the model names: its arms
lay their bytes out alike and differ only in what they are called and what they mean, which Bid
Price Quote Opening says (Bid Price Quote Strategy Market Depth Level Opening Pair, Bid Price Quote
Numeric Bid Price Quote Strategy Market Depth Level Numeric Pair Negative Whole Pair, Bid Price
Quote Numeric Bid Price Quote Strategy Market Depth Level Numeric Pair Negative Ten Pair, Bid Price
Quote Numeric Bid Price Quote Strategy Market Depth Level Numeric Pair Negative Hundred Pair, Bid
Price Quote Numeric Bid Price Quote Strategy Market Depth Level Numeric Pair Negative Thousand Pair,
Bid Price Quote Numeric Bid Price Quote Strategy Market Depth Level Numeric Pair Negative Ten
Thousand Pair, Bid Price Quote Numeric Bid Price Quote Strategy Market Depth Level Numeric Pair
Negative Hundred Thousand Pair, Bid Price Quote Numeric Bid Price Quote Strategy Market Depth Level
Numeric Pair Negative Million Pair, Bid Price Quote Strategy Market Depth Level Numeric Pair). It is
read as Bid Price Quote Numeric Bid Price Quote Strategy Market Depth Level Numeric Pair Negative
Whole Pair's fields, so which arm applies is left to what is built on the definition.

Note: Ask Price Quote Strategy Market Depth Level is 8 bytes whichever arm the model names: its arms
lay their bytes out alike and differ only in what they are called and what they mean, which Ask
Price Quote Opening says (Ask Price Quote Strategy Market Depth Level Opening Pair, Ask Price Quote
Numeric Ask Price Quote Strategy Market Depth Level Numeric Pair Negative Whole Pair, Ask Price
Quote Numeric Ask Price Quote Strategy Market Depth Level Numeric Pair Negative Ten Pair, Ask Price
Quote Numeric Ask Price Quote Strategy Market Depth Level Numeric Pair Negative Hundred Pair, Ask
Price Quote Numeric Ask Price Quote Strategy Market Depth Level Numeric Pair Negative Thousand Pair,
Ask Price Quote Numeric Ask Price Quote Strategy Market Depth Level Numeric Pair Negative Ten
Thousand Pair, Ask Price Quote Numeric Ask Price Quote Strategy Market Depth Level Numeric Pair
Negative Hundred Thousand Pair, Ask Price Quote Numeric Ask Price Quote Strategy Market Depth Level
Numeric Pair Negative Million Pair, Ask Price Quote Strategy Market Depth Level Numeric Pair). It is
read as Ask Price Quote Numeric Ask Price Quote Strategy Market Depth Level Numeric Pair Negative
Whole Pair's fields, so which arm applies is left to what is built on the definition.

Note: Number Of Levels counts Strategy Market Depth Level in ascii digits: it is written from the
list as its digits, and a list of more than 9 could not be written

Note: Maximum Threshold Price Fraction Pair is 8 bytes whichever arm the model names: its arms lay
their bytes out alike and differ only in what they are called and what they mean, which Maximum
Threshold Price Fraction Indicator says (Maximum Threshold Price Negative Whole Pair, Maximum
Threshold Price Negative Ten Pair, Maximum Threshold Price Negative Hundred Pair, Maximum Threshold
Price Negative Thousand Pair, Maximum Threshold Price Negative Ten Thousand Pair, Maximum Threshold
Price Negative Hundred Thousand Pair, Maximum Threshold Price Negative Million Pair, Maximum
Threshold Price Numeric Pair). It is read as Maximum Threshold Price Negative Whole Pair's fields,
so which arm applies is left to what is built on the definition.

Note: Minimum Threshold Price Instrument Fraction Pair is 8 bytes whichever arm the model names: its
arms lay their bytes out alike and differ only in what they are called and what they mean, which
Minimum Threshold Price Fraction Indicator says (Minimum Threshold Price Instrument Negative Whole
Pair, Minimum Threshold Price Instrument Negative Ten Pair, Minimum Threshold Price Instrument
Negative Hundred Pair, Minimum Threshold Price Instrument Negative Thousand Pair, Minimum Threshold
Price Instrument Negative Ten Thousand Pair, Minimum Threshold Price Instrument Negative Hundred
Thousand Pair, Minimum Threshold Price Instrument Negative Million Pair, Minimum Threshold Price
Instrument Numeric Pair). It is read as Minimum Threshold Price Instrument Negative Whole Pair's
fields, so which arm applies is left to what is built on the definition.

Note: Tick Increment is 8 bytes whichever arm the model names: its arms lay their bytes out alike
and differ only in what they are called and what they mean, which Tick Increment Fraction Indicator
says (Tick Increment Numeric Pair, Tick Increment Numeric Negative Whole Pair, Tick Increment
Numeric Negative Ten Pair, Tick Increment Numeric Negative Hundred Pair, Tick Increment Numeric
Negative Thousand Pair, Tick Increment Numeric Negative Ten Thousand Pair, Tick Increment Numeric
Negative Hundred Thousand Pair, Tick Increment Numeric Negative Million Pair, Tick Increment Raw
Pair). It is read as Tick Increment Numeric Pair's fields, so which arm applies is left to what is
built on the definition.

Note: Tick Value Fraction Pair is 8 bytes whichever arm the model names: its arms lay their bytes
out alike and differ only in what they are called and what they mean, which Tick Value Fraction
Indicator says (Tick Value Negative Whole Pair, Tick Value Negative Ten Pair, Tick Value Negative
Hundred Pair, Tick Value Negative Thousand Pair, Tick Value Negative Ten Thousand Pair, Tick Value
Negative Hundred Thousand Pair, Tick Value Negative Million Pair, Tick Value Numeric Pair). It is
read as Tick Value Negative Whole Pair's fields, so which arm applies is left to what is built on
the definition.

Note: Maximum Threshold Price Futures Fraction Pair is 8 bytes whichever arm the model names: its
arms lay their bytes out alike and differ only in what they are called and what they mean, which
Maximum Threshold Price Fraction Indicator says (Maximum Threshold Price Futures Negative Whole
Pair, Maximum Threshold Price Futures Negative Ten Pair, Maximum Threshold Price Futures Negative
Hundred Pair, Maximum Threshold Price Futures Negative Thousand Pair, Maximum Threshold Price
Futures Negative Ten Thousand Pair, Maximum Threshold Price Futures Negative Hundred Thousand Pair,
Maximum Threshold Price Futures Negative Million Pair, Maximum Threshold Price Futures Numeric
Pair). It is read as Maximum Threshold Price Futures Negative Whole Pair's fields, so which arm
applies is left to what is built on the definition.

Note: Minimum Threshold Price Futures Fraction Pair is 8 bytes whichever arm the model names: its
arms lay their bytes out alike and differ only in what they are called and what they mean, which
Minimum Threshold Price Fraction Indicator says (Minimum Threshold Price Futures Negative Whole
Pair, Minimum Threshold Price Futures Negative Ten Pair, Minimum Threshold Price Futures Negative
Hundred Pair, Minimum Threshold Price Futures Negative Thousand Pair, Minimum Threshold Price
Futures Negative Ten Thousand Pair, Minimum Threshold Price Futures Negative Hundred Thousand Pair,
Minimum Threshold Price Futures Negative Million Pair, Minimum Threshold Price Futures Numeric
Pair). It is read as Minimum Threshold Price Futures Negative Whole Pair's fields, so which arm
applies is left to what is built on the definition.

Note: Minimum Threshold Price Strategy Fraction Pair is 8 bytes whichever arm the model names: its
arms lay their bytes out alike and differ only in what they are called and what they mean, which
Minimum Threshold Price Fraction Indicator says (Minimum Threshold Price Strategy Negative Whole
Pair, Minimum Threshold Price Strategy Negative Ten Pair, Minimum Threshold Price Strategy Negative
Hundred Pair, Minimum Threshold Price Strategy Negative Thousand Pair, Minimum Threshold Price
Strategy Negative Ten Thousand Pair, Minimum Threshold Price Strategy Negative Hundred Thousand
Pair, Minimum Threshold Price Strategy Negative Million Pair, Minimum Threshold Price Strategy
Numeric Pair). It is read as Minimum Threshold Price Strategy Negative Whole Pair's fields, so which
arm applies is left to what is built on the definition.

Note: Leg Ratio Or Delta Fraction Pair is 5 bytes whichever arm the model names: its arms lay their
bytes out alike and differ only in what they are called and what they mean, which Leg Ratio Or Delta
Fraction Indicator says (Leg Ratio Or Delta Negative Whole Pair, Leg Ratio Or Delta Negative Ten
Pair, Leg Ratio Or Delta Negative Hundred Pair, Leg Ratio Or Delta Negative Thousand Pair, Leg Ratio
Or Delta Negative Ten Thousand Pair, Leg Ratio Or Delta Negative Hundred Thousand Pair, Leg Ratio Or
Delta Negative Million Pair, Leg Ratio Or Delta Numeric Pair). It is read as Leg Ratio Or Delta
Negative Whole Pair's fields, so which arm applies is left to what is built on the definition.

Note: Leg Price Fraction Pair is 8 bytes whichever arm the model names: its arms lay their bytes out
alike and differ only in what they are called and what they mean, which Leg Price Fraction Indicator
says (Leg Price Negative Whole Pair, Leg Price Negative Ten Pair, Leg Price Negative Hundred Pair,
Leg Price Negative Thousand Pair, Leg Price Negative Ten Thousand Pair, Leg Price Negative Hundred
Thousand Pair, Leg Price Negative Million Pair, Leg Price Numeric Pair). It is read as Leg Price
Negative Whole Pair's fields, so which arm applies is left to what is built on the definition.

Note: Number Of Legs counts Strategy Instrument Leg in ascii digits: it is written from the list as
its digits, and a list of more than 99 could not be written

Note: Initial Order Price Fraction Pair is 8 bytes whichever arm the model names: its arms lay their
bytes out alike and differ only in what they are called and what they mean, which Initial Order
Price Fraction Indicator says (Initial Order Price Negative Whole Pair, Initial Order Price Negative
Ten Pair, Initial Order Price Negative Hundred Pair, Initial Order Price Negative Thousand Pair,
Initial Order Price Negative Ten Thousand Pair, Initial Order Price Negative Hundred Thousand Pair,
Initial Order Price Negative Million Pair, Initial Order Price Numeric Pair). It is read as Initial
Order Price Negative Whole Pair's fields, so which arm applies is left to what is built on the
definition.

Note: Bid Price Summary Fraction Pair is 8 bytes whichever arm the model names: its arms lay their
bytes out alike and differ only in what they are called and what they mean, which Bid Price Fraction
Indicator says (Bid Price Summary Negative Whole Pair, Bid Price Summary Negative Ten Pair, Bid
Price Summary Negative Hundred Pair, Bid Price Summary Negative Thousand Pair, Bid Price Summary
Negative Ten Thousand Pair, Bid Price Summary Negative Hundred Thousand Pair, Bid Price Summary
Negative Million Pair, Bid Price Summary Numeric Pair). It is read as Bid Price Summary Negative
Whole Pair's fields, so which arm applies is left to what is built on the definition.

Note: Ask Price Summary Fraction Pair is 8 bytes whichever arm the model names: its arms lay their
bytes out alike and differ only in what they are called and what they mean, which Ask Price Fraction
Indicator says (Ask Price Summary Negative Whole Pair, Ask Price Summary Negative Ten Pair, Ask
Price Summary Negative Hundred Pair, Ask Price Summary Negative Thousand Pair, Ask Price Summary
Negative Ten Thousand Pair, Ask Price Summary Negative Hundred Thousand Pair, Ask Price Summary
Negative Million Pair, Ask Price Summary Numeric Pair). It is read as Ask Price Summary Negative
Whole Pair's fields, so which arm applies is left to what is built on the definition.

Note: Last Price Fraction Pair is 8 bytes whichever arm the model names: its arms lay their bytes
out alike and differ only in what they are called and what they mean, which Last Price Fraction
Indicator says (Last Price Negative Whole Pair, Last Price Negative Ten Pair, Last Price Negative
Hundred Pair, Last Price Negative Thousand Pair, Last Price Negative Ten Thousand Pair, Last Price
Negative Hundred Thousand Pair, Last Price Negative Million Pair, Last Price Numeric Pair). It is
read as Last Price Negative Whole Pair's fields, so which arm applies is left to what is built on
the definition.

Note: Net Change Option Summary Message Fraction Pair is 8 bytes whichever arm the model names: its
arms lay their bytes out alike and differ only in what they are called and what they mean, which Net
Change Fraction Indicator says (Net Change Option Summary Message Negative Whole Pair, Net Change
Option Summary Message Negative Ten Pair, Net Change Option Summary Message Negative Hundred Pair,
Net Change Option Summary Message Negative Thousand Pair, Net Change Option Summary Message Negative
Ten Thousand Pair, Net Change Option Summary Message Negative Hundred Thousand Pair, Net Change
Option Summary Message Negative Million Pair, Net Change Option Summary Message Numeric Pair). It is
read as Net Change Option Summary Message Negative Whole Pair's fields, so which arm applies is left
to what is built on the definition.

Note: Open Price Fraction Pair is 8 bytes whichever arm the model names: its arms lay their bytes
out alike and differ only in what they are called and what they mean, which Open Price Fraction
Indicator says (Open Price Negative Whole Pair, Open Price Negative Ten Pair, Open Price Negative
Hundred Pair, Open Price Negative Thousand Pair, Open Price Negative Ten Thousand Pair, Open Price
Negative Hundred Thousand Pair, Open Price Negative Million Pair, Open Price Numeric Pair). It is
read as Open Price Negative Whole Pair's fields, so which arm applies is left to what is built on
the definition.

Note: High Price Fraction Pair is 8 bytes whichever arm the model names: its arms lay their bytes
out alike and differ only in what they are called and what they mean, which High Price Fraction
Indicator says (High Price Negative Whole Pair, High Price Negative Ten Pair, High Price Negative
Hundred Pair, High Price Negative Thousand Pair, High Price Negative Ten Thousand Pair, High Price
Negative Hundred Thousand Pair, High Price Negative Million Pair, High Price Numeric Pair). It is
read as High Price Negative Whole Pair's fields, so which arm applies is left to what is built on
the definition.

Note: Low Price Fraction Pair is 8 bytes whichever arm the model names: its arms lay their bytes out
alike and differ only in what they are called and what they mean, which Low Price Fraction Indicator
says (Low Price Negative Whole Pair, Low Price Negative Ten Pair, Low Price Negative Hundred Pair,
Low Price Negative Thousand Pair, Low Price Negative Ten Thousand Pair, Low Price Negative Hundred
Thousand Pair, Low Price Negative Million Pair, Low Price Numeric Pair). It is read as Low Price
Negative Whole Pair's fields, so which arm applies is left to what is built on the definition.

Note: Closing Price Fraction Pair is 8 bytes whichever arm the model names: its arms lay their bytes
out alike and differ only in what they are called and what they mean, which Closing Price Fraction
Indicator says (Closing Price Negative Whole Pair, Closing Price Negative Ten Pair, Closing Price
Negative Hundred Pair, Closing Price Negative Thousand Pair, Closing Price Negative Ten Thousand
Pair, Closing Price Negative Hundred Thousand Pair, Closing Price Negative Million Pair, Closing
Price Numeric Pair). It is read as Closing Price Negative Whole Pair's fields, so which arm applies
is left to what is built on the definition.

Note: Previous Closing Price Fraction Pair is 8 bytes whichever arm the model names: its arms lay
their bytes out alike and differ only in what they are called and what they mean, which Previous
Closing Price Fraction Indicator says (Previous Closing Price Negative Whole Pair, Previous Closing
Price Negative Ten Pair, Previous Closing Price Negative Hundred Pair, Previous Closing Price
Negative Thousand Pair, Previous Closing Price Negative Ten Thousand Pair, Previous Closing Price
Negative Hundred Thousand Pair, Previous Closing Price Negative Million Pair, Previous Closing Price
Numeric Pair). It is read as Previous Closing Price Negative Whole Pair's fields, so which arm
applies is left to what is built on the definition.

Note: Net Change Future Options Summary Message Fraction Pair is 8 bytes whichever arm the model
names: its arms lay their bytes out alike and differ only in what they are called and what they
mean, which Net Change Fraction Indicator says (Net Change Future Options Summary Message Negative
Whole Pair, Net Change Future Options Summary Message Negative Ten Pair, Net Change Future Options
Summary Message Negative Hundred Pair, Net Change Future Options Summary Message Negative Thousand
Pair, Net Change Future Options Summary Message Negative Ten Thousand Pair, Net Change Future
Options Summary Message Negative Hundred Thousand Pair, Net Change Future Options Summary Message
Negative Million Pair, Net Change Future Options Summary Message Numeric Pair). It is read as Net
Change Future Options Summary Message Negative Whole Pair's fields, so which arm applies is left to
what is built on the definition.

Note: Opening Price Fraction Pair is 8 bytes whichever arm the model names: its arms lay their bytes
out alike and differ only in what they are called and what they mean, which Opening Price Fraction
Indicator says (Opening Price Negative Whole Pair, Opening Price Negative Ten Pair, Opening Price
Negative Hundred Pair, Opening Price Negative Thousand Pair, Opening Price Negative Ten Thousand
Pair, Opening Price Negative Hundred Thousand Pair, Opening Price Negative Million Pair, Opening
Price Numeric Pair). It is read as Opening Price Negative Whole Pair's fields, so which arm applies
is left to what is built on the definition.

Note: Settlement Price Fraction Pair is 8 bytes whichever arm the model names: its arms lay their
bytes out alike and differ only in what they are called and what they mean, which Settlement Price
Fraction Indicator says (Settlement Price Negative Whole Pair, Settlement Price Negative Ten Pair,
Settlement Price Negative Hundred Pair, Settlement Price Negative Thousand Pair, Settlement Price
Negative Ten Thousand Pair, Settlement Price Negative Hundred Thousand Pair, Settlement Price
Negative Million Pair, Settlement Price Numeric Pair). It is read as Settlement Price Negative Whole
Pair's fields, so which arm applies is left to what is built on the definition.

Note: Previous Settlement Price Fraction Pair is 8 bytes whichever arm the model names: its arms lay
their bytes out alike and differ only in what they are called and what they mean, which Previous
Settlement Price Fraction Indicator says (Previous Settlement Price Negative Whole Pair, Previous
Settlement Price Negative Ten Pair, Previous Settlement Price Negative Hundred Pair, Previous
Settlement Price Negative Thousand Pair, Previous Settlement Price Negative Ten Thousand Pair,
Previous Settlement Price Negative Hundred Thousand Pair, Previous Settlement Price Negative Million
Pair, Previous Settlement Price Numeric Pair). It is read as Previous Settlement Price Negative
Whole Pair's fields, so which arm applies is left to what is built on the definition.

Note: Net Change Futures Summary Message Fraction Pair is 8 bytes whichever arm the model names: its
arms lay their bytes out alike and differ only in what they are called and what they mean, which Net
Change Fraction Indicator says (Net Change Futures Summary Message Negative Whole Pair, Net Change
Futures Summary Message Negative Ten Pair, Net Change Futures Summary Message Negative Hundred Pair,
Net Change Futures Summary Message Negative Thousand Pair, Net Change Futures Summary Message
Negative Ten Thousand Pair, Net Change Futures Summary Message Negative Hundred Thousand Pair, Net
Change Futures Summary Message Negative Million Pair, Net Change Futures Summary Message Numeric
Pair). It is read as Net Change Futures Summary Message Negative Whole Pair's fields, so which arm
applies is left to what is built on the definition.

Note: Previous Settlement Fraction Pair is 8 bytes whichever arm the model names: its arms lay their
bytes out alike and differ only in what they are called and what they mean, which Previous
Settlement Fraction Indicator says (Previous Settlement Negative Whole Pair, Previous Settlement
Negative Ten Pair, Previous Settlement Negative Hundred Pair, Previous Settlement Negative Thousand
Pair, Previous Settlement Negative Ten Thousand Pair, Previous Settlement Negative Hundred Thousand
Pair, Previous Settlement Negative Million Pair, Previous Settlement Numeric Pair). It is read as
Previous Settlement Negative Whole Pair's fields, so which arm applies is left to what is built on
the definition.

Note: External Price At Source Fraction Pair is 8 bytes whichever arm the model names: its arms lay
their bytes out alike and differ only in what they are called and what they mean, which External
Price Fraction Indicator says (External Price At Source Negative Whole Pair, External Price At
Source Negative Ten Pair, External Price At Source Negative Hundred Pair, External Price At Source
Negative Thousand Pair, External Price At Source Negative Ten Thousand Pair, External Price At
Source Negative Hundred Thousand Pair, External Price At Source Negative Million Pair, External
Price At Source Numeric Pair). It is read as External Price At Source Negative Whole Pair's fields,
so which arm applies is left to what is built on the definition.

Note: Net Change Strategy Summary Message Fraction Pair is 8 bytes whichever arm the model names:
its arms lay their bytes out alike and differ only in what they are called and what they mean, which
Net Change Fraction Indicator says (Net Change Strategy Summary Message Negative Whole Pair, Net
Change Strategy Summary Message Negative Ten Pair, Net Change Strategy Summary Message Negative
Hundred Pair, Net Change Strategy Summary Message Negative Thousand Pair, Net Change Strategy
Summary Message Negative Ten Thousand Pair, Net Change Strategy Summary Message Negative Hundred
Thousand Pair, Net Change Strategy Summary Message Negative Million Pair, Net Change Strategy
Summary Message Numeric Pair). It is read as Net Change Strategy Summary Message Negative Whole
Pair's fields, so which arm applies is left to what is built on the definition.

Note: Order Price Fraction Pair is 8 bytes whichever arm the model names: its arms lay their bytes
out alike and differ only in what they are called and what they mean, which Order Price Fraction
Indicator says (Order Price Negative Whole Pair, Order Price Negative Ten Pair, Order Price Negative
Hundred Pair, Order Price Negative Thousand Pair, Order Price Negative Ten Thousand Pair, Order
Price Negative Hundred Thousand Pair, Order Price Negative Million Pair, Order Price Numeric Pair).
It is read as Order Price Negative Whole Pair's fields, so which arm applies is left to what is
built on the definition.

Note: Net Change Futures Trade Correction Message Fraction Pair is 8 bytes whichever arm the model
names: its arms lay their bytes out alike and differ only in what they are called and what they
mean, which Net Change Fraction Indicator says (Net Change Futures Trade Correction Message Negative
Whole Pair, Net Change Futures Trade Correction Message Negative Ten Pair, Net Change Futures Trade
Correction Message Negative Hundred Pair, Net Change Futures Trade Correction Message Negative
Thousand Pair, Net Change Futures Trade Correction Message Negative Ten Thousand Pair, Net Change
Futures Trade Correction Message Negative Hundred Thousand Pair, Net Change Futures Trade Correction
Message Negative Million Pair, Net Change Futures Trade Correction Message Numeric Pair). It is read
as Net Change Futures Trade Correction Message Negative Whole Pair's fields, so which arm applies is
left to what is built on the definition.

Note: Coupon Fraction Pair is 8 bytes whichever arm the model names: its arms lay their bytes out
alike and differ only in what they are called and what they mean, which Coupon Fraction Indicator
says (Coupon Negative Whole Pair, Coupon Negative Ten Pair, Coupon Negative Hundred Pair, Coupon
Negative Thousand Pair, Coupon Negative Ten Thousand Pair, Coupon Negative Hundred Thousand Pair,
Coupon Negative Million Pair, Coupon Numeric Pair). It is read as Coupon Negative Whole Pair's
fields, so which arm applies is left to what is built on the definition.

Note: Conversion Factor Fraction Pair is 8 bytes whichever arm the model names: its arms lay their
bytes out alike and differ only in what they are called and what they mean, which Conversion Factor
Fraction Indicator says (Conversion Factor Negative Whole Pair, Conversion Factor Negative Ten Pair,
Conversion Factor Negative Hundred Pair, Conversion Factor Negative Thousand Pair, Conversion Factor
Negative Ten Thousand Pair, Conversion Factor Negative Hundred Thousand Pair, Conversion Factor
Negative Million Pair, Conversion Factor Numeric Pair). It is read as Conversion Factor Negative
Whole Pair's fields, so which arm applies is left to what is built on the definition.

Note: Number Of Bonds counts Bond Definition in ascii digits: it is written from the list as its
digits, and a list of more than 99 could not be written

Note: Min Price Fraction Pair is 8 bytes whichever arm the model names: its arms lay their bytes out
alike and differ only in what they are called and what they mean, which Min Price Fraction Indicator
says (Min Price Negative Whole Pair, Min Price Negative Ten Pair, Min Price Negative Hundred Pair,
Min Price Negative Thousand Pair, Min Price Negative Ten Thousand Pair, Min Price Negative Hundred
Thousand Pair, Min Price Negative Million Pair, Min Price Numeric Pair). It is read as Min Price
Negative Whole Pair's fields, so which arm applies is left to what is built on the definition.

Note: Tick Price Fraction Pair is 8 bytes whichever arm the model names: its arms lay their bytes
out alike and differ only in what they are called and what they mean, which Tick Price Fraction
Indicator says (Tick Price Negative Whole Pair, Tick Price Negative Ten Pair, Tick Price Negative
Hundred Pair, Tick Price Negative Thousand Pair, Tick Price Negative Ten Thousand Pair, Tick Price
Negative Hundred Thousand Pair, Tick Price Negative Million Pair, Tick Price Numeric Pair). It is
read as Tick Price Negative Whole Pair's fields, so which arm applies is left to what is built on
the definition.

Note: Number Of Entries counts Tick Entry in ascii digits: it is written from the list as its
digits, and a list of more than 99 could not be written

License: MIT No Attribution
-/

namespace Omi.TmxMxSolamulticastHsvfV1141

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

/-- Symbol Month: one byte code -/
def SymbolMonth.codes : List UInt8 :=
  [0x46, 0x47, 0x48, 0x4A, 0x4B, 0x4D, 0x4E, 0x51, 0x55, 0x56, 0x58, 0x5A]

inductive SymbolMonth where
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
  | unlisted (byte : { byte : UInt8 // byte ∉ SymbolMonth.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SymbolMonth

def toByte : SymbolMonth → UInt8
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
def listed (byte : UInt8) : SymbolMonth :=
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

def ofByte (byte : UInt8) : SymbolMonth :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SymbolMonth) : ofByte value.toByte = value := by
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

def encode (value : SymbolMonth) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SymbolMonth × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SymbolMonth) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SymbolMonth) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SymbolMonth) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SymbolMonth

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

/-- Price Indicator Marker: one byte code -/
def FuturesTradeMessagePriceIndicatorMarker.codes : List UInt8 :=
  [0x41, 0x42, 0x20, 0x44, 0x45, 0x47, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x50, 0x51, 0x52, 0x53, 0x74, 0x54, 0x55, 0x56, 0x59, 0x5A]

inductive FuturesTradeMessagePriceIndicatorMarker where
  | asofTrade -- Asof Trade
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
  | .asofTrade => 0x41
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
  if byte = 0x41 then .asofTrade
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
  | asofTrade => decide
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
  [0x59, 0x4F, 0x54, 0x46, 0x45, 0x48, 0x52, 0x53, 0x41, 0x43, 0x20]

inductive SeriesStatus where
  | preOpening -- Pre Opening
  | opening -- Opening
  | continuousTrading -- Continuous Trading
  | forbidden -- Forbidden
  | interventionBeforeOpening -- Intervention Before Opening
  | haltedTrading -- Halted Trading
  | reserved -- Reserved
  | suspended -- Suspended
  | surveillanceIntervention -- Surveillance Intervention
  | endOfDayInquiries -- End Of Day Inquiries
  | ifNotUsed -- If Not Used
  | unlisted (byte : { byte : UInt8 // byte ∉ SeriesStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SeriesStatus

def toByte : SeriesStatus → UInt8
  | .preOpening => 0x59
  | .opening => 0x4F
  | .continuousTrading => 0x54
  | .forbidden => 0x46
  | .interventionBeforeOpening => 0x45
  | .haltedTrading => 0x48
  | .reserved => 0x52
  | .suspended => 0x53
  | .surveillanceIntervention => 0x41
  | .endOfDayInquiries => 0x43
  | .ifNotUsed => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SeriesStatus :=
  if byte = 0x59 then .preOpening
  else if byte = 0x4F then .opening
  else if byte = 0x54 then .continuousTrading
  else if byte = 0x46 then .forbidden
  else if byte = 0x45 then .interventionBeforeOpening
  else if byte = 0x48 then .haltedTrading
  else if byte = 0x52 then .reserved
  else if byte = 0x53 then .suspended
  else if byte = 0x41 then .surveillanceIntervention
  else if byte = 0x43 then .endOfDayInquiries
  else .ifNotUsed

def ofByte (byte : UInt8) : SeriesStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SeriesStatus) : ofByte value.toByte = value := by
  cases value with
  | preOpening => decide
  | opening => decide
  | continuousTrading => decide
  | forbidden => decide
  | interventionBeforeOpening => decide
  | haltedTrading => decide
  | reserved => decide
  | suspended => decide
  | surveillanceIntervention => decide
  | endOfDayInquiries => decide
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
  [0x59, 0x4F, 0x54, 0x46, 0x45, 0x48, 0x52, 0x53, 0x41, 0x43, 0x20]

inductive InstrumentStatusMarker where
  | preopening -- Preopening
  | opening -- Opening
  | continuousTrading -- Continuous Trading
  | forbidden -- Forbidden
  | interventionBeforeOpening -- Intervention Before Opening
  | haltedTrading -- Halted Trading
  | reserved -- Reserved
  | suspended -- Suspended
  | surveillanceIntervention -- Surveillance Intervention
  | endofDayInquiries -- Endof Day Inquiries
  | ifNotUsed -- If Not Used
  | unlisted (byte : { byte : UInt8 // byte ∉ InstrumentStatusMarker.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InstrumentStatusMarker

def toByte : InstrumentStatusMarker → UInt8
  | .preopening => 0x59
  | .opening => 0x4F
  | .continuousTrading => 0x54
  | .forbidden => 0x46
  | .interventionBeforeOpening => 0x45
  | .haltedTrading => 0x48
  | .reserved => 0x52
  | .suspended => 0x53
  | .surveillanceIntervention => 0x41
  | .endofDayInquiries => 0x43
  | .ifNotUsed => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : InstrumentStatusMarker :=
  if byte = 0x59 then .preopening
  else if byte = 0x4F then .opening
  else if byte = 0x54 then .continuousTrading
  else if byte = 0x46 then .forbidden
  else if byte = 0x45 then .interventionBeforeOpening
  else if byte = 0x48 then .haltedTrading
  else if byte = 0x52 then .reserved
  else if byte = 0x53 then .suspended
  else if byte = 0x41 then .surveillanceIntervention
  else if byte = 0x43 then .endofDayInquiries
  else .ifNotUsed

def ofByte (byte : UInt8) : InstrumentStatusMarker :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InstrumentStatusMarker) : ofByte value.toByte = value := by
  cases value with
  | preopening => decide
  | opening => decide
  | continuousTrading => decide
  | forbidden => decide
  | interventionBeforeOpening => decide
  | haltedTrading => decide
  | reserved => decide
  | suspended => decide
  | surveillanceIntervention => decide
  | endofDayInquiries => decide
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

/-- Underlying Symbol Month: one byte code -/
def UnderlyingSymbolMonth.codes : List UInt8 :=
  [0x46, 0x47, 0x48, 0x4A, 0x4B, 0x4D, 0x4E, 0x51, 0x55, 0x56, 0x58, 0x5A]

inductive UnderlyingSymbolMonth where
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
  | unlisted (byte : { byte : UInt8 // byte ∉ UnderlyingSymbolMonth.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace UnderlyingSymbolMonth

def toByte : UnderlyingSymbolMonth → UInt8
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
def listed (byte : UInt8) : UnderlyingSymbolMonth :=
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

def ofByte (byte : UInt8) : UnderlyingSymbolMonth :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : UnderlyingSymbolMonth) : ofByte value.toByte = value := by
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

def encode (value : UnderlyingSymbolMonth) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (UnderlyingSymbolMonth × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : UnderlyingSymbolMonth) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : UnderlyingSymbolMonth) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : UnderlyingSymbolMonth) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end UnderlyingSymbolMonth

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

/-- Strategy Type: one byte code -/
def StrategyType.codes : List UInt8 :=
  [0x43, 0x53, 0x56, 0x52, 0x55]

inductive StrategyType where
  | classic -- Classic
  | strip -- Strip
  | coveredRegular -- Covered Regular
  | coveredReferenceFixed -- Covered Reference Fixed
  | coveredWithStock -- Covered With Stock
  | unlisted (byte : { byte : UInt8 // byte ∉ StrategyType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace StrategyType

def toByte : StrategyType → UInt8
  | .classic => 0x43
  | .strip => 0x53
  | .coveredRegular => 0x56
  | .coveredReferenceFixed => 0x52
  | .coveredWithStock => 0x55
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : StrategyType :=
  if byte = 0x43 then .classic
  else if byte = 0x53 then .strip
  else if byte = 0x56 then .coveredRegular
  else if byte = 0x52 then .coveredReferenceFixed
  else .coveredWithStock

def ofByte (byte : UInt8) : StrategyType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : StrategyType) : ofByte value.toByte = value := by
  cases value with
  | classic => decide
  | strip => decide
  | coveredRegular => decide
  | coveredReferenceFixed => decide
  | coveredWithStock => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : StrategyType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (StrategyType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : StrategyType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : StrategyType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : StrategyType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end StrategyType

/-- Initial Order Side: one byte code -/
def InitialOrderSide.codes : List UInt8 :=
  [0x42, 0x53]

inductive InitialOrderSide where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ InitialOrderSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InitialOrderSide

def toByte : InitialOrderSide → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : InitialOrderSide :=
  if byte = 0x42 then .buy
  else .sell

def ofByte (byte : UInt8) : InitialOrderSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InitialOrderSide) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : InitialOrderSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (InitialOrderSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : InitialOrderSide) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : InitialOrderSide) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : InitialOrderSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end InitialOrderSide

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

/-- Order Side: one byte code -/
def OrderSide.codes : List UInt8 :=
  [0x42, 0x53]

inductive OrderSide where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderSide

def toByte : OrderSide → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderSide :=
  if byte = 0x42 then .buy
  else .sell

def ofByte (byte : UInt8) : OrderSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderSide) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrderSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrderSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrderSide) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OrderSide) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OrderSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderSide

/-- Order Type: one byte code -/
def OrderType.codes : List UInt8 :=
  [0x41, 0x42]

inductive OrderType where
  | initialOrder -- Initial Order
  | improvementOrder -- Improvement Order
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderType

def toByte : OrderType → UInt8
  | .initialOrder => 0x41
  | .improvementOrder => 0x42
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderType :=
  if byte = 0x41 then .initialOrder
  else .improvementOrder

def ofByte (byte : UInt8) : OrderType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderType) : ofByte value.toByte = value := by
  cases value with
  | initialOrder => decide
  | improvementOrder => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrderType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrderType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrderType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OrderType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OrderType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderType

/-- Group Status: one byte code -/
def GroupStatus.codes : List UInt8 :=
  [0x59, 0x4F, 0x54, 0x46, 0x45, 0x48, 0x41, 0x43, 0x20]

inductive GroupStatus where
  | preOpening -- Pre Opening
  | opening -- Opening
  | continuousTrading -- Continuous Trading
  | forbidden -- Forbidden
  | interventionBeforeOpening -- Intervention Before Opening
  | haltedTrading -- Halted Trading
  | surveillanceIntervention -- Surveillance Intervention
  | endOfDayInquiries -- End Of Day Inquiries
  | ifNotUsed -- If Not Used
  | unlisted (byte : { byte : UInt8 // byte ∉ GroupStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace GroupStatus

def toByte : GroupStatus → UInt8
  | .preOpening => 0x59
  | .opening => 0x4F
  | .continuousTrading => 0x54
  | .forbidden => 0x46
  | .interventionBeforeOpening => 0x45
  | .haltedTrading => 0x48
  | .surveillanceIntervention => 0x41
  | .endOfDayInquiries => 0x43
  | .ifNotUsed => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : GroupStatus :=
  if byte = 0x59 then .preOpening
  else if byte = 0x4F then .opening
  else if byte = 0x54 then .continuousTrading
  else if byte = 0x46 then .forbidden
  else if byte = 0x45 then .interventionBeforeOpening
  else if byte = 0x48 then .haltedTrading
  else if byte = 0x41 then .surveillanceIntervention
  else if byte = 0x43 then .endOfDayInquiries
  else .ifNotUsed

def ofByte (byte : UInt8) : GroupStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : GroupStatus) : ofByte value.toByte = value := by
  cases value with
  | preOpening => decide
  | opening => decide
  | continuousTrading => decide
  | forbidden => decide
  | interventionBeforeOpening => decide
  | haltedTrading => decide
  | surveillanceIntervention => decide
  | endOfDayInquiries => decide
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

/-- Strike Price Fraction Pair: 8 bytes -/
structure StrikePriceFractionPair where
  rawStrikePrice : Alpha 7
  strikePriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace StrikePriceFractionPair

def encode (message : StrikePriceFractionPair) : List UInt8 :=
  Alpha.encode message.rawStrikePrice
    ++ (encodeUInt 1 message.strikePriceFractionIndicator)

def decode (bytes : List UInt8) : Option (StrikePriceFractionPair × List UInt8) := do
  let (rawStrikePrice, bytes) ← Alpha.decode 7 bytes
  let (strikePriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawStrikePrice, strikePriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : StrikePriceFractionPair) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : StrikePriceFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrikePriceFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end StrikePriceFractionPair

/-- Option Symbol: 19 bytes -/
structure OptionSymbol where
  rootSymbol : Alpha 6
  expiryMonth : ExpiryMonth
  strikePriceFractionPair : StrikePriceFractionPair
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  deriving DecidableEq, Repr

namespace OptionSymbol

def encode (message : OptionSymbol) : List UInt8 :=
  Alpha.encode message.rootSymbol
    ++ (ExpiryMonth.encode message.expiryMonth
    ++ (StrikePriceFractionPair.encode message.strikePriceFractionPair
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay))))

def decode (bytes : List UInt8) : Option (OptionSymbol × List UInt8) := do
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (expiryMonth, bytes) ← ExpiryMonth.decode bytes
  let (strikePriceFractionPair, bytes) ← StrikePriceFractionPair.decode bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  pure ({ rootSymbol, expiryMonth, strikePriceFractionPair, expiryYear, expiryDay }, bytes)

@[simp] theorem encode_length (message : OptionSymbol) : (encode message).length = 19 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ExpiryMonth.encode_length, StrikePriceFractionPair.encode_length]

theorem encode_length_pos (message : OptionSymbol) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionSymbol) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExpiryMonth.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StrikePriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OptionSymbol

/-- Trade Price Fraction Pair: 8 bytes -/
structure TradePriceFractionPair where
  rawTradePrice : Alpha 7
  tradePriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace TradePriceFractionPair

def encode (message : TradePriceFractionPair) : List UInt8 :=
  Alpha.encode message.rawTradePrice
    ++ (encodeUInt 1 message.tradePriceFractionIndicator)

def decode (bytes : List UInt8) : Option (TradePriceFractionPair × List UInt8) := do
  let (rawTradePrice, bytes) ← Alpha.decode 7 bytes
  let (tradePriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawTradePrice, tradePriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : TradePriceFractionPair) : (encode message).length = 8 := by
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

/-- Net Change Fraction Pair: 8 bytes -/
structure NetChangeFractionPair where
  rawNetChange : Alpha 7
  netChangeFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace NetChangeFractionPair

def encode (message : NetChangeFractionPair) : List UInt8 :=
  Alpha.encode message.rawNetChange
    ++ (encodeUInt 1 message.netChangeFractionIndicator)

def decode (bytes : List UInt8) : Option (NetChangeFractionPair × List UInt8) := do
  let (rawNetChange, bytes) ← Alpha.decode 7 bytes
  let (netChangeFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawNetChange, netChangeFractionIndicator }, bytes)

@[simp] theorem encode_length (message : NetChangeFractionPair) : (encode message).length = 8 := by
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

/-- Option Trade Message: 60 bytes -/
structure OptionTradeMessage where
  exchangeId : ExchangeId
  optionSymbol : OptionSymbol
  volume : Alpha 8
  tradePriceFractionPair : TradePriceFractionPair
  netChangeSign : NetChangeSign
  netChangeFractionPair : NetChangeFractionPair
  priceIndicatorMarker : PriceIndicatorMarker
  tradeNumber : Alpha 8
  auctionId : Alpha 6
  deriving DecidableEq, Repr

namespace OptionTradeMessage

def encode (message : OptionTradeMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (OptionSymbol.encode message.optionSymbol
    ++ (Alpha.encode message.volume
    ++ (TradePriceFractionPair.encode message.tradePriceFractionPair
    ++ (NetChangeSign.encode message.netChangeSign
    ++ (NetChangeFractionPair.encode message.netChangeFractionPair
    ++ (PriceIndicatorMarker.encode message.priceIndicatorMarker
    ++ (Alpha.encode message.tradeNumber
    ++ (Alpha.encode message.auctionId))))))))

def decode (bytes : List UInt8) : Option (OptionTradeMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (optionSymbol, bytes) ← OptionSymbol.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePriceFractionPair, bytes) ← TradePriceFractionPair.decode bytes
  let (netChangeSign, bytes) ← NetChangeSign.decode bytes
  let (netChangeFractionPair, bytes) ← NetChangeFractionPair.decode bytes
  let (priceIndicatorMarker, bytes) ← PriceIndicatorMarker.decode bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  let (auctionId, bytes) ← Alpha.decode 6 bytes
  pure ({ exchangeId, optionSymbol, volume, tradePriceFractionPair, netChangeSign, netChangeFractionPair, priceIndicatorMarker, tradeNumber, auctionId }, bytes)

@[simp] theorem encode_length (message : OptionTradeMessage) : (encode message).length = 60 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, OptionSymbol.encode_length, Alpha.encode_length, TradePriceFractionPair.encode_length, NetChangeSign.encode_length, NetChangeFractionPair.encode_length, PriceIndicatorMarker.encode_length]

theorem encode_length_pos (message : OptionTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradePriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PriceIndicatorMarker.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OptionTradeMessage

/-- Future Option Symbol: 20 bytes -/
structure FutureOptionSymbol where
  rootSymbol : Alpha 6
  symbolMonth : SymbolMonth
  symbolYear : Alpha 2
  expiryDay : Alpha 2
  callPutCode : CallPutCode
  strikePriceFractionPair : StrikePriceFractionPair
  deriving DecidableEq, Repr

namespace FutureOptionSymbol

def encode (message : FutureOptionSymbol) : List UInt8 :=
  Alpha.encode message.rootSymbol
    ++ (SymbolMonth.encode message.symbolMonth
    ++ (Alpha.encode message.symbolYear
    ++ (Alpha.encode message.expiryDay
    ++ (CallPutCode.encode message.callPutCode
    ++ (StrikePriceFractionPair.encode message.strikePriceFractionPair)))))

def decode (bytes : List UInt8) : Option (FutureOptionSymbol × List UInt8) := do
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (symbolMonth, bytes) ← SymbolMonth.decode bytes
  let (symbolYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (callPutCode, bytes) ← CallPutCode.decode bytes
  let (strikePriceFractionPair, bytes) ← StrikePriceFractionPair.decode bytes
  pure ({ rootSymbol, symbolMonth, symbolYear, expiryDay, callPutCode, strikePriceFractionPair }, bytes)

@[simp] theorem encode_length (message : FutureOptionSymbol) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, SymbolMonth.encode_length, CallPutCode.encode_length, StrikePriceFractionPair.encode_length]

theorem encode_length_pos (message : FutureOptionSymbol) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FutureOptionSymbol) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SymbolMonth.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CallPutCode.decode_encode, some_bind]
  dsimp only
  rw [StrikePriceFractionPair.decode_encode, some_bind]
  rfl

end FutureOptionSymbol

/-- Net Change Future Options Trade Message Fraction Pair: 8 bytes -/
structure NetChangeFutureOptionsTradeMessageFractionPair where
  rawNetChangeFutureOptionsTradeMessage : Alpha 7
  netChangeFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace NetChangeFutureOptionsTradeMessageFractionPair

def encode (message : NetChangeFutureOptionsTradeMessageFractionPair) : List UInt8 :=
  Alpha.encode message.rawNetChangeFutureOptionsTradeMessage
    ++ (encodeUInt 1 message.netChangeFractionIndicator)

def decode (bytes : List UInt8) : Option (NetChangeFutureOptionsTradeMessageFractionPair × List UInt8) := do
  let (rawNetChangeFutureOptionsTradeMessage, bytes) ← Alpha.decode 7 bytes
  let (netChangeFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawNetChangeFutureOptionsTradeMessage, netChangeFractionIndicator }, bytes)

@[simp] theorem encode_length (message : NetChangeFutureOptionsTradeMessageFractionPair) : (encode message).length = 8 := by
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

/-- Future Options Trade Message: 61 bytes -/
structure FutureOptionsTradeMessage where
  exchangeId : ExchangeId
  futureOptionSymbol : FutureOptionSymbol
  volume : Alpha 8
  tradePriceFractionPair : TradePriceFractionPair
  priceIndicatorMarker : PriceIndicatorMarker
  netChangeSign : NetChangeSign
  netChangeFutureOptionsTradeMessageFractionPair : NetChangeFutureOptionsTradeMessageFractionPair
  tradeNumber : Alpha 8
  auctionId : Alpha 6
  deriving DecidableEq, Repr

namespace FutureOptionsTradeMessage

def encode (message : FutureOptionsTradeMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (FutureOptionSymbol.encode message.futureOptionSymbol
    ++ (Alpha.encode message.volume
    ++ (TradePriceFractionPair.encode message.tradePriceFractionPair
    ++ (PriceIndicatorMarker.encode message.priceIndicatorMarker
    ++ (NetChangeSign.encode message.netChangeSign
    ++ (NetChangeFutureOptionsTradeMessageFractionPair.encode message.netChangeFutureOptionsTradeMessageFractionPair
    ++ (Alpha.encode message.tradeNumber
    ++ (Alpha.encode message.auctionId))))))))

def decode (bytes : List UInt8) : Option (FutureOptionsTradeMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (futureOptionSymbol, bytes) ← FutureOptionSymbol.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePriceFractionPair, bytes) ← TradePriceFractionPair.decode bytes
  let (priceIndicatorMarker, bytes) ← PriceIndicatorMarker.decode bytes
  let (netChangeSign, bytes) ← NetChangeSign.decode bytes
  let (netChangeFutureOptionsTradeMessageFractionPair, bytes) ← NetChangeFutureOptionsTradeMessageFractionPair.decode bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  let (auctionId, bytes) ← Alpha.decode 6 bytes
  pure ({ exchangeId, futureOptionSymbol, volume, tradePriceFractionPair, priceIndicatorMarker, netChangeSign, netChangeFutureOptionsTradeMessageFractionPair, tradeNumber, auctionId }, bytes)

@[simp] theorem encode_length (message : FutureOptionsTradeMessage) : (encode message).length = 61 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, FutureOptionSymbol.encode_length, Alpha.encode_length, TradePriceFractionPair.encode_length, PriceIndicatorMarker.encode_length, NetChangeSign.encode_length, NetChangeFutureOptionsTradeMessageFractionPair.encode_length]

theorem encode_length_pos (message : FutureOptionsTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FutureOptionsTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureOptionSymbol.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end FutureOptionsTradeMessage

/-- Future Product: 11 bytes -/
structure FutureProduct where
  rootSymbol : Alpha 6
  symbolMonth : SymbolMonth
  symbolYear : Alpha 2
  expiryDay : Alpha 2
  deriving DecidableEq, Repr

namespace FutureProduct

def encode (message : FutureProduct) : List UInt8 :=
  Alpha.encode message.rootSymbol
    ++ (SymbolMonth.encode message.symbolMonth
    ++ (Alpha.encode message.symbolYear
    ++ (Alpha.encode message.expiryDay)))

def decode (bytes : List UInt8) : Option (FutureProduct × List UInt8) := do
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (symbolMonth, bytes) ← SymbolMonth.decode bytes
  let (symbolYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  pure ({ rootSymbol, symbolMonth, symbolYear, expiryDay }, bytes)

@[simp] theorem encode_length (message : FutureProduct) : (encode message).length = 11 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, SymbolMonth.encode_length]

theorem encode_length_pos (message : FutureProduct) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FutureProduct) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SymbolMonth.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FutureProduct

/-- Net Change Futures Trade Message Fraction Pair: 8 bytes -/
structure NetChangeFuturesTradeMessageFractionPair where
  rawNetChangeFuturesTradeMessage : Alpha 7
  netChangeFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace NetChangeFuturesTradeMessageFractionPair

def encode (message : NetChangeFuturesTradeMessageFractionPair) : List UInt8 :=
  Alpha.encode message.rawNetChangeFuturesTradeMessage
    ++ (encodeUInt 1 message.netChangeFractionIndicator)

def decode (bytes : List UInt8) : Option (NetChangeFuturesTradeMessageFractionPair × List UInt8) := do
  let (rawNetChangeFuturesTradeMessage, bytes) ← Alpha.decode 7 bytes
  let (netChangeFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawNetChangeFuturesTradeMessage, netChangeFractionIndicator }, bytes)

@[simp] theorem encode_length (message : NetChangeFuturesTradeMessageFractionPair) : (encode message).length = 8 := by
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

/-- Futures Trade Message: 52 bytes -/
structure FuturesTradeMessage where
  exchangeId : ExchangeId
  futureProduct : FutureProduct
  volume : Alpha 8
  tradePriceFractionPair : TradePriceFractionPair
  netChangeSign : NetChangeSign
  netChangeFuturesTradeMessageFractionPair : NetChangeFuturesTradeMessageFractionPair
  priceIndicatorMarker : FuturesTradeMessagePriceIndicatorMarker
  tradeNumber : Alpha 8
  auctionId : Alpha 6
  deriving DecidableEq, Repr

namespace FuturesTradeMessage

def encode (message : FuturesTradeMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (FutureProduct.encode message.futureProduct
    ++ (Alpha.encode message.volume
    ++ (TradePriceFractionPair.encode message.tradePriceFractionPair
    ++ (NetChangeSign.encode message.netChangeSign
    ++ (NetChangeFuturesTradeMessageFractionPair.encode message.netChangeFuturesTradeMessageFractionPair
    ++ (FuturesTradeMessagePriceIndicatorMarker.encode message.priceIndicatorMarker
    ++ (Alpha.encode message.tradeNumber
    ++ (Alpha.encode message.auctionId))))))))

def decode (bytes : List UInt8) : Option (FuturesTradeMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (futureProduct, bytes) ← FutureProduct.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePriceFractionPair, bytes) ← TradePriceFractionPair.decode bytes
  let (netChangeSign, bytes) ← NetChangeSign.decode bytes
  let (netChangeFuturesTradeMessageFractionPair, bytes) ← NetChangeFuturesTradeMessageFractionPair.decode bytes
  let (priceIndicatorMarker, bytes) ← FuturesTradeMessagePriceIndicatorMarker.decode bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  let (auctionId, bytes) ← Alpha.decode 6 bytes
  pure ({ exchangeId, futureProduct, volume, tradePriceFractionPair, netChangeSign, netChangeFuturesTradeMessageFractionPair, priceIndicatorMarker, tradeNumber, auctionId }, bytes)

@[simp] theorem encode_length (message : FuturesTradeMessage) : (encode message).length = 52 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, FutureProduct.encode_length, Alpha.encode_length, TradePriceFractionPair.encode_length, NetChangeSign.encode_length, NetChangeFuturesTradeMessageFractionPair.encode_length, FuturesTradeMessagePriceIndicatorMarker.encode_length]

theorem encode_length_pos (message : FuturesTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FuturesTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureProduct.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradePriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeFuturesTradeMessageFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FuturesTradeMessagePriceIndicatorMarker.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FuturesTradeMessage

/-- Strategy Trade Message: 72 bytes -/
structure StrategyTradeMessage where
  exchangeId : ExchangeId
  symbol : Alpha 30
  volume : Alpha 8
  tradePriceSign : TradePriceSign
  tradePriceFractionPair : TradePriceFractionPair
  netChangeSign : NetChangeSign
  netChangeFractionPair : NetChangeFractionPair
  priceIndicatorMarker : FuturesTradeMessagePriceIndicatorMarker
  tradeNumber : Alpha 8
  auctionId : Alpha 6
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
    ++ (FuturesTradeMessagePriceIndicatorMarker.encode message.priceIndicatorMarker
    ++ (Alpha.encode message.tradeNumber
    ++ (Alpha.encode message.auctionId)))))))))

def decode (bytes : List UInt8) : Option (StrategyTradeMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (symbol, bytes) ← Alpha.decode 30 bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePriceSign, bytes) ← TradePriceSign.decode bytes
  let (tradePriceFractionPair, bytes) ← TradePriceFractionPair.decode bytes
  let (netChangeSign, bytes) ← NetChangeSign.decode bytes
  let (netChangeFractionPair, bytes) ← NetChangeFractionPair.decode bytes
  let (priceIndicatorMarker, bytes) ← FuturesTradeMessagePriceIndicatorMarker.decode bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  let (auctionId, bytes) ← Alpha.decode 6 bytes
  pure ({ exchangeId, symbol, volume, tradePriceSign, tradePriceFractionPair, netChangeSign, netChangeFractionPair, priceIndicatorMarker, tradeNumber, auctionId }, bytes)

@[simp] theorem encode_length (message : StrategyTradeMessage) : (encode message).length = 72 := by
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
  rw [List.append_assoc, FuturesTradeMessagePriceIndicatorMarker.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StrategyTradeMessage

/-- Option Request For Quote Message: 29 bytes -/
structure OptionRequestForQuoteMessage where
  exchangeId : ExchangeId
  optionSymbol : OptionSymbol
  requestedSize : Alpha 8
  requestedMarketSide : RequestedMarketSide
  deriving DecidableEq, Repr

namespace OptionRequestForQuoteMessage

def encode (message : OptionRequestForQuoteMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (OptionSymbol.encode message.optionSymbol
    ++ (Alpha.encode message.requestedSize
    ++ (RequestedMarketSide.encode message.requestedMarketSide)))

def decode (bytes : List UInt8) : Option (OptionRequestForQuoteMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (optionSymbol, bytes) ← OptionSymbol.decode bytes
  let (requestedSize, bytes) ← Alpha.decode 8 bytes
  let (requestedMarketSide, bytes) ← RequestedMarketSide.decode bytes
  pure ({ exchangeId, optionSymbol, requestedSize, requestedMarketSide }, bytes)

@[simp] theorem encode_length (message : OptionRequestForQuoteMessage) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, OptionSymbol.encode_length, Alpha.encode_length, RequestedMarketSide.encode_length]

theorem encode_length_pos (message : OptionRequestForQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionRequestForQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [RequestedMarketSide.decode_encode, some_bind]
  rfl

end OptionRequestForQuoteMessage

/-- Future Options Request For Quote Message: 30 bytes -/
structure FutureOptionsRequestForQuoteMessage where
  exchangeId : ExchangeId
  futureOptionSymbol : FutureOptionSymbol
  requestedSize : Alpha 8
  requestedMarketSide : RequestedMarketSide
  deriving DecidableEq, Repr

namespace FutureOptionsRequestForQuoteMessage

def encode (message : FutureOptionsRequestForQuoteMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (FutureOptionSymbol.encode message.futureOptionSymbol
    ++ (Alpha.encode message.requestedSize
    ++ (RequestedMarketSide.encode message.requestedMarketSide)))

def decode (bytes : List UInt8) : Option (FutureOptionsRequestForQuoteMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (futureOptionSymbol, bytes) ← FutureOptionSymbol.decode bytes
  let (requestedSize, bytes) ← Alpha.decode 8 bytes
  let (requestedMarketSide, bytes) ← RequestedMarketSide.decode bytes
  pure ({ exchangeId, futureOptionSymbol, requestedSize, requestedMarketSide }, bytes)

@[simp] theorem encode_length (message : FutureOptionsRequestForQuoteMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, FutureOptionSymbol.encode_length, Alpha.encode_length, RequestedMarketSide.encode_length]

theorem encode_length_pos (message : FutureOptionsRequestForQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FutureOptionsRequestForQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureOptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [RequestedMarketSide.decode_encode, some_bind]
  rfl

end FutureOptionsRequestForQuoteMessage

/-- Future Request For Quote Message: 21 bytes -/
structure FutureRequestForQuoteMessage where
  exchangeId : ExchangeId
  futureProduct : FutureProduct
  requestedSize : Alpha 8
  requestedMarketSide : RequestedMarketSide
  deriving DecidableEq, Repr

namespace FutureRequestForQuoteMessage

def encode (message : FutureRequestForQuoteMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (FutureProduct.encode message.futureProduct
    ++ (Alpha.encode message.requestedSize
    ++ (RequestedMarketSide.encode message.requestedMarketSide)))

def decode (bytes : List UInt8) : Option (FutureRequestForQuoteMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (futureProduct, bytes) ← FutureProduct.decode bytes
  let (requestedSize, bytes) ← Alpha.decode 8 bytes
  let (requestedMarketSide, bytes) ← RequestedMarketSide.decode bytes
  pure ({ exchangeId, futureProduct, requestedSize, requestedMarketSide }, bytes)

@[simp] theorem encode_length (message : FutureRequestForQuoteMessage) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, FutureProduct.encode_length, Alpha.encode_length, RequestedMarketSide.encode_length]

theorem encode_length_pos (message : FutureRequestForQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FutureRequestForQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureProduct.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [RequestedMarketSide.decode_encode, some_bind]
  rfl

end FutureRequestForQuoteMessage

/-- Strategy Request For Quote Message: 40 bytes -/
structure StrategyRequestForQuoteMessage where
  exchangeId : ExchangeId
  symbol : Alpha 30
  requestedSize : Alpha 8
  requestedMarketSide : RequestedMarketSide
  deriving DecidableEq, Repr

namespace StrategyRequestForQuoteMessage

def encode (message : StrategyRequestForQuoteMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.requestedSize
    ++ (RequestedMarketSide.encode message.requestedMarketSide)))

def decode (bytes : List UInt8) : Option (StrategyRequestForQuoteMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (symbol, bytes) ← Alpha.decode 30 bytes
  let (requestedSize, bytes) ← Alpha.decode 8 bytes
  let (requestedMarketSide, bytes) ← RequestedMarketSide.decode bytes
  pure ({ exchangeId, symbol, requestedSize, requestedMarketSide }, bytes)

@[simp] theorem encode_length (message : StrategyRequestForQuoteMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length, RequestedMarketSide.encode_length]

theorem encode_length_pos (message : StrategyRequestForQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyRequestForQuoteMessage) (rest : List UInt8) :
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

end StrategyRequestForQuoteMessage

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

/-- Option Symbol Schedule Notice: 19 bytes -/
structure OptionSymbolScheduleNotice where
  rootSymbol : Alpha 6
  expiryMonth : ExpiryMonth
  strikePriceScheduleNoticeFractionPair : StrikePriceScheduleNoticeFractionPair
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  deriving DecidableEq, Repr

namespace OptionSymbolScheduleNotice

def encode (message : OptionSymbolScheduleNotice) : List UInt8 :=
  Alpha.encode message.rootSymbol
    ++ (ExpiryMonth.encode message.expiryMonth
    ++ (StrikePriceScheduleNoticeFractionPair.encode message.strikePriceScheduleNoticeFractionPair
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay))))

def decode (bytes : List UInt8) : Option (OptionSymbolScheduleNotice × List UInt8) := do
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (expiryMonth, bytes) ← ExpiryMonth.decode bytes
  let (strikePriceScheduleNoticeFractionPair, bytes) ← StrikePriceScheduleNoticeFractionPair.decode bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  pure ({ rootSymbol, expiryMonth, strikePriceScheduleNoticeFractionPair, expiryYear, expiryDay }, bytes)

@[simp] theorem encode_length (message : OptionSymbolScheduleNotice) : (encode message).length = 19 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ExpiryMonth.encode_length, StrikePriceScheduleNoticeFractionPair.encode_length]

theorem encode_length_pos (message : OptionSymbolScheduleNotice) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionSymbolScheduleNotice) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExpiryMonth.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StrikePriceScheduleNoticeFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OptionSymbolScheduleNotice

/-- Instrument Schedule Notice Option Message: 27 bytes -/
structure InstrumentScheduleNoticeOptionMessage where
  exchangeId : ExchangeId
  optionSymbolScheduleNotice : OptionSymbolScheduleNotice
  seriesStatus : SeriesStatus
  scheduledStatusChangeTime : Alpha 6
  deriving DecidableEq, Repr

namespace InstrumentScheduleNoticeOptionMessage

def encode (message : InstrumentScheduleNoticeOptionMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (OptionSymbolScheduleNotice.encode message.optionSymbolScheduleNotice
    ++ (SeriesStatus.encode message.seriesStatus
    ++ (Alpha.encode message.scheduledStatusChangeTime)))

def decode (bytes : List UInt8) : Option (InstrumentScheduleNoticeOptionMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (optionSymbolScheduleNotice, bytes) ← OptionSymbolScheduleNotice.decode bytes
  let (seriesStatus, bytes) ← SeriesStatus.decode bytes
  let (scheduledStatusChangeTime, bytes) ← Alpha.decode 6 bytes
  pure ({ exchangeId, optionSymbolScheduleNotice, seriesStatus, scheduledStatusChangeTime }, bytes)

@[simp] theorem encode_length (message : InstrumentScheduleNoticeOptionMessage) : (encode message).length = 27 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, OptionSymbolScheduleNotice.encode_length, SeriesStatus.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : InstrumentScheduleNoticeOptionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentScheduleNoticeOptionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OptionSymbolScheduleNotice.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SeriesStatus.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end InstrumentScheduleNoticeOptionMessage

/-- Instrument Schedule Notice Futures Option Message: 28 bytes -/
structure InstrumentScheduleNoticeFuturesOptionMessage where
  exchangeId : ExchangeId
  futureOptionSymbol : FutureOptionSymbol
  seriesStatus : SeriesStatus
  scheduledStatusChangeTime : Alpha 6
  deriving DecidableEq, Repr

namespace InstrumentScheduleNoticeFuturesOptionMessage

def encode (message : InstrumentScheduleNoticeFuturesOptionMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (FutureOptionSymbol.encode message.futureOptionSymbol
    ++ (SeriesStatus.encode message.seriesStatus
    ++ (Alpha.encode message.scheduledStatusChangeTime)))

def decode (bytes : List UInt8) : Option (InstrumentScheduleNoticeFuturesOptionMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (futureOptionSymbol, bytes) ← FutureOptionSymbol.decode bytes
  let (seriesStatus, bytes) ← SeriesStatus.decode bytes
  let (scheduledStatusChangeTime, bytes) ← Alpha.decode 6 bytes
  pure ({ exchangeId, futureOptionSymbol, seriesStatus, scheduledStatusChangeTime }, bytes)

@[simp] theorem encode_length (message : InstrumentScheduleNoticeFuturesOptionMessage) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, FutureOptionSymbol.encode_length, SeriesStatus.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : InstrumentScheduleNoticeFuturesOptionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentScheduleNoticeFuturesOptionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureOptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SeriesStatus.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end InstrumentScheduleNoticeFuturesOptionMessage

/-- Instrument Schedule Notice Future Message: 19 bytes -/
structure InstrumentScheduleNoticeFutureMessage where
  exchangeId : ExchangeId
  futureProduct : FutureProduct
  seriesStatus : SeriesStatus
  scheduledStatusChangeTime : Alpha 6
  deriving DecidableEq, Repr

namespace InstrumentScheduleNoticeFutureMessage

def encode (message : InstrumentScheduleNoticeFutureMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (FutureProduct.encode message.futureProduct
    ++ (SeriesStatus.encode message.seriesStatus
    ++ (Alpha.encode message.scheduledStatusChangeTime)))

def decode (bytes : List UInt8) : Option (InstrumentScheduleNoticeFutureMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (futureProduct, bytes) ← FutureProduct.decode bytes
  let (seriesStatus, bytes) ← SeriesStatus.decode bytes
  let (scheduledStatusChangeTime, bytes) ← Alpha.decode 6 bytes
  pure ({ exchangeId, futureProduct, seriesStatus, scheduledStatusChangeTime }, bytes)

@[simp] theorem encode_length (message : InstrumentScheduleNoticeFutureMessage) : (encode message).length = 19 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, FutureProduct.encode_length, SeriesStatus.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : InstrumentScheduleNoticeFutureMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentScheduleNoticeFutureMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureProduct.decode_encode, some_bind]
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

/-- Bid Price Quote: 8 bytes -/
structure BidPriceQuote where
  rawBidPriceQuoteNumeric : Alpha 7
  bidPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace BidPriceQuote

def encode (message : BidPriceQuote) : List UInt8 :=
  Alpha.encode message.rawBidPriceQuoteNumeric
    ++ (encodeUInt 1 message.bidPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (BidPriceQuote × List UInt8) := do
  let (rawBidPriceQuoteNumeric, bytes) ← Alpha.decode 7 bytes
  let (bidPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawBidPriceQuoteNumeric, bidPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : BidPriceQuote) : (encode message).length = 8 := by
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

/-- Ask Price Quote: 8 bytes -/
structure AskPriceQuote where
  rawAskPriceQuoteNumeric : Alpha 7
  askPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace AskPriceQuote

def encode (message : AskPriceQuote) : List UInt8 :=
  Alpha.encode message.rawAskPriceQuoteNumeric
    ++ (encodeUInt 1 message.askPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (AskPriceQuote × List UInt8) := do
  let (rawAskPriceQuoteNumeric, bytes) ← Alpha.decode 7 bytes
  let (askPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawAskPriceQuoteNumeric, askPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : AskPriceQuote) : (encode message).length = 8 := by
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
  optionSymbol : OptionSymbol
  bidPriceQuote : BidPriceQuote
  bidSize : Alpha 5
  askPriceQuote : AskPriceQuote
  askSize : Alpha 5
  instrumentStatusMarker : InstrumentStatusMarker
  deriving DecidableEq, Repr

namespace OptionQuoteMessage

def encode (message : OptionQuoteMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (OptionSymbol.encode message.optionSymbol
    ++ (BidPriceQuote.encode message.bidPriceQuote
    ++ (Alpha.encode message.bidSize
    ++ (AskPriceQuote.encode message.askPriceQuote
    ++ (Alpha.encode message.askSize
    ++ (InstrumentStatusMarker.encode message.instrumentStatusMarker))))))

def decode (bytes : List UInt8) : Option (OptionQuoteMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (optionSymbol, bytes) ← OptionSymbol.decode bytes
  let (bidPriceQuote, bytes) ← BidPriceQuote.decode bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPriceQuote, bytes) ← AskPriceQuote.decode bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (instrumentStatusMarker, bytes) ← InstrumentStatusMarker.decode bytes
  pure ({ exchangeId, optionSymbol, bidPriceQuote, bidSize, askPriceQuote, askSize, instrumentStatusMarker }, bytes)

@[simp] theorem encode_length (message : OptionQuoteMessage) : (encode message).length = 47 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, OptionSymbol.encode_length, BidPriceQuote.encode_length, Alpha.encode_length, AskPriceQuote.encode_length, InstrumentStatusMarker.encode_length]

theorem encode_length_pos (message : OptionQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BidPriceQuote.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskPriceQuote.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [InstrumentStatusMarker.decode_encode, some_bind]
  rfl

end OptionQuoteMessage

/-- Future Options Quote Message: 48 bytes -/
structure FutureOptionsQuoteMessage where
  exchangeId : ExchangeId
  futureOptionSymbol : FutureOptionSymbol
  bidPriceQuote : BidPriceQuote
  bidSize : Alpha 5
  askPriceQuote : AskPriceQuote
  askSize : Alpha 5
  instrumentStatusMarker : InstrumentStatusMarker
  deriving DecidableEq, Repr

namespace FutureOptionsQuoteMessage

def encode (message : FutureOptionsQuoteMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (FutureOptionSymbol.encode message.futureOptionSymbol
    ++ (BidPriceQuote.encode message.bidPriceQuote
    ++ (Alpha.encode message.bidSize
    ++ (AskPriceQuote.encode message.askPriceQuote
    ++ (Alpha.encode message.askSize
    ++ (InstrumentStatusMarker.encode message.instrumentStatusMarker))))))

def decode (bytes : List UInt8) : Option (FutureOptionsQuoteMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (futureOptionSymbol, bytes) ← FutureOptionSymbol.decode bytes
  let (bidPriceQuote, bytes) ← BidPriceQuote.decode bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPriceQuote, bytes) ← AskPriceQuote.decode bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (instrumentStatusMarker, bytes) ← InstrumentStatusMarker.decode bytes
  pure ({ exchangeId, futureOptionSymbol, bidPriceQuote, bidSize, askPriceQuote, askSize, instrumentStatusMarker }, bytes)

@[simp] theorem encode_length (message : FutureOptionsQuoteMessage) : (encode message).length = 48 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, FutureOptionSymbol.encode_length, BidPriceQuote.encode_length, Alpha.encode_length, AskPriceQuote.encode_length, InstrumentStatusMarker.encode_length]

theorem encode_length_pos (message : FutureOptionsQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FutureOptionsQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureOptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BidPriceQuote.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskPriceQuote.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [InstrumentStatusMarker.decode_encode, some_bind]
  rfl

end FutureOptionsQuoteMessage

/-- Bid Price Quote Futures Quote Message: 8 bytes -/
structure BidPriceQuoteFuturesQuoteMessage where
  rawBidPriceQuoteNumericBidPriceQuoteFuturesQuoteMessageNumericPair : Alpha 7
  bidPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace BidPriceQuoteFuturesQuoteMessage

def encode (message : BidPriceQuoteFuturesQuoteMessage) : List UInt8 :=
  Alpha.encode message.rawBidPriceQuoteNumericBidPriceQuoteFuturesQuoteMessageNumericPair
    ++ (encodeUInt 1 message.bidPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (BidPriceQuoteFuturesQuoteMessage × List UInt8) := do
  let (rawBidPriceQuoteNumericBidPriceQuoteFuturesQuoteMessageNumericPair, bytes) ← Alpha.decode 7 bytes
  let (bidPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawBidPriceQuoteNumericBidPriceQuoteFuturesQuoteMessageNumericPair, bidPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : BidPriceQuoteFuturesQuoteMessage) : (encode message).length = 8 := by
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

/-- Ask Price Quote Futures Quote Message: 8 bytes -/
structure AskPriceQuoteFuturesQuoteMessage where
  rawAskPriceQuoteNumericAskPriceQuoteFuturesQuoteMessageNumericPair : Alpha 7
  askPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace AskPriceQuoteFuturesQuoteMessage

def encode (message : AskPriceQuoteFuturesQuoteMessage) : List UInt8 :=
  Alpha.encode message.rawAskPriceQuoteNumericAskPriceQuoteFuturesQuoteMessageNumericPair
    ++ (encodeUInt 1 message.askPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (AskPriceQuoteFuturesQuoteMessage × List UInt8) := do
  let (rawAskPriceQuoteNumericAskPriceQuoteFuturesQuoteMessageNumericPair, bytes) ← Alpha.decode 7 bytes
  let (askPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawAskPriceQuoteNumericAskPriceQuoteFuturesQuoteMessageNumericPair, askPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : AskPriceQuoteFuturesQuoteMessage) : (encode message).length = 8 := by
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

/-- Futures Quote Message: 39 bytes -/
structure FuturesQuoteMessage where
  exchangeId : ExchangeId
  futureProduct : FutureProduct
  bidPriceQuoteFuturesQuoteMessage : BidPriceQuoteFuturesQuoteMessage
  bidSize : Alpha 5
  askPriceQuoteFuturesQuoteMessage : AskPriceQuoteFuturesQuoteMessage
  askSize : Alpha 5
  instrumentStatusMarker : InstrumentStatusMarker
  deriving DecidableEq, Repr

namespace FuturesQuoteMessage

def encode (message : FuturesQuoteMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (FutureProduct.encode message.futureProduct
    ++ (BidPriceQuoteFuturesQuoteMessage.encode message.bidPriceQuoteFuturesQuoteMessage
    ++ (Alpha.encode message.bidSize
    ++ (AskPriceQuoteFuturesQuoteMessage.encode message.askPriceQuoteFuturesQuoteMessage
    ++ (Alpha.encode message.askSize
    ++ (InstrumentStatusMarker.encode message.instrumentStatusMarker))))))

def decode (bytes : List UInt8) : Option (FuturesQuoteMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (futureProduct, bytes) ← FutureProduct.decode bytes
  let (bidPriceQuoteFuturesQuoteMessage, bytes) ← BidPriceQuoteFuturesQuoteMessage.decode bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPriceQuoteFuturesQuoteMessage, bytes) ← AskPriceQuoteFuturesQuoteMessage.decode bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (instrumentStatusMarker, bytes) ← InstrumentStatusMarker.decode bytes
  pure ({ exchangeId, futureProduct, bidPriceQuoteFuturesQuoteMessage, bidSize, askPriceQuoteFuturesQuoteMessage, askSize, instrumentStatusMarker }, bytes)

@[simp] theorem encode_length (message : FuturesQuoteMessage) : (encode message).length = 39 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, FutureProduct.encode_length, BidPriceQuoteFuturesQuoteMessage.encode_length, Alpha.encode_length, AskPriceQuoteFuturesQuoteMessage.encode_length, InstrumentStatusMarker.encode_length]

theorem encode_length_pos (message : FuturesQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FuturesQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureProduct.decode_encode, some_bind]
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

/-- Strategy Quote Message: 60 bytes -/
structure StrategyQuoteMessage where
  exchangeId : ExchangeId
  symbol : Alpha 30
  bidPriceSign : BidPriceSign
  bidPriceQuote : BidPriceQuote
  bidSize : Alpha 5
  askPriceSign : AskPriceSign
  askPriceQuote : AskPriceQuote
  askSize : Alpha 5
  instrumentStatusMarker : InstrumentStatusMarker
  deriving DecidableEq, Repr

namespace StrategyQuoteMessage

def encode (message : StrategyQuoteMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.symbol
    ++ (BidPriceSign.encode message.bidPriceSign
    ++ (BidPriceQuote.encode message.bidPriceQuote
    ++ (Alpha.encode message.bidSize
    ++ (AskPriceSign.encode message.askPriceSign
    ++ (AskPriceQuote.encode message.askPriceQuote
    ++ (Alpha.encode message.askSize
    ++ (InstrumentStatusMarker.encode message.instrumentStatusMarker))))))))

def decode (bytes : List UInt8) : Option (StrategyQuoteMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (symbol, bytes) ← Alpha.decode 30 bytes
  let (bidPriceSign, bytes) ← BidPriceSign.decode bytes
  let (bidPriceQuote, bytes) ← BidPriceQuote.decode bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPriceSign, bytes) ← AskPriceSign.decode bytes
  let (askPriceQuote, bytes) ← AskPriceQuote.decode bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (instrumentStatusMarker, bytes) ← InstrumentStatusMarker.decode bytes
  pure ({ exchangeId, symbol, bidPriceSign, bidPriceQuote, bidSize, askPriceSign, askPriceQuote, askSize, instrumentStatusMarker }, bytes)

@[simp] theorem encode_length (message : StrategyQuoteMessage) : (encode message).length = 60 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length, BidPriceSign.encode_length, BidPriceQuote.encode_length, AskPriceSign.encode_length, AskPriceQuote.encode_length, InstrumentStatusMarker.encode_length]

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
  rw [List.append_assoc, BidPriceQuote.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskPriceSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskPriceQuote.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [InstrumentStatusMarker.decode_encode, some_bind]
  rfl

end StrategyQuoteMessage

/-- Bid Price Quote Market Depth Level: 8 bytes -/
structure BidPriceQuoteMarketDepthLevel where
  rawBidPriceQuoteNumericBidPriceQuoteMarketDepthLevelNumericPair : Alpha 7
  bidPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace BidPriceQuoteMarketDepthLevel

def encode (message : BidPriceQuoteMarketDepthLevel) : List UInt8 :=
  Alpha.encode message.rawBidPriceQuoteNumericBidPriceQuoteMarketDepthLevelNumericPair
    ++ (encodeUInt 1 message.bidPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (BidPriceQuoteMarketDepthLevel × List UInt8) := do
  let (rawBidPriceQuoteNumericBidPriceQuoteMarketDepthLevelNumericPair, bytes) ← Alpha.decode 7 bytes
  let (bidPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawBidPriceQuoteNumericBidPriceQuoteMarketDepthLevelNumericPair, bidPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : BidPriceQuoteMarketDepthLevel) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : BidPriceQuoteMarketDepthLevel) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BidPriceQuoteMarketDepthLevel) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end BidPriceQuoteMarketDepthLevel

/-- Ask Price Quote Market Depth Level: 8 bytes -/
structure AskPriceQuoteMarketDepthLevel where
  rawAskPriceQuoteNumericAskPriceQuoteMarketDepthLevelNumericPair : Alpha 7
  askPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace AskPriceQuoteMarketDepthLevel

def encode (message : AskPriceQuoteMarketDepthLevel) : List UInt8 :=
  Alpha.encode message.rawAskPriceQuoteNumericAskPriceQuoteMarketDepthLevelNumericPair
    ++ (encodeUInt 1 message.askPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (AskPriceQuoteMarketDepthLevel × List UInt8) := do
  let (rawAskPriceQuoteNumericAskPriceQuoteMarketDepthLevelNumericPair, bytes) ← Alpha.decode 7 bytes
  let (askPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawAskPriceQuoteNumericAskPriceQuoteMarketDepthLevelNumericPair, askPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : AskPriceQuoteMarketDepthLevel) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : AskPriceQuoteMarketDepthLevel) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AskPriceQuoteMarketDepthLevel) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end AskPriceQuoteMarketDepthLevel

/-- Market Depth Level: 31 bytes -/
structure MarketDepthLevel where
  levelOfMarketDepth : LevelOfMarketDepth
  bidPriceQuoteMarketDepthLevel : BidPriceQuoteMarketDepthLevel
  bidSize : Alpha 5
  numberOfBidOrders : Alpha 2
  askPriceQuoteMarketDepthLevel : AskPriceQuoteMarketDepthLevel
  askSize : Alpha 5
  numberOfAskOrders : Alpha 2
  deriving DecidableEq, Repr

namespace MarketDepthLevel

def encode (message : MarketDepthLevel) : List UInt8 :=
  LevelOfMarketDepth.encode message.levelOfMarketDepth
    ++ (BidPriceQuoteMarketDepthLevel.encode message.bidPriceQuoteMarketDepthLevel
    ++ (Alpha.encode message.bidSize
    ++ (Alpha.encode message.numberOfBidOrders
    ++ (AskPriceQuoteMarketDepthLevel.encode message.askPriceQuoteMarketDepthLevel
    ++ (Alpha.encode message.askSize
    ++ (Alpha.encode message.numberOfAskOrders))))))

def decode (bytes : List UInt8) : Option (MarketDepthLevel × List UInt8) := do
  let (levelOfMarketDepth, bytes) ← LevelOfMarketDepth.decode bytes
  let (bidPriceQuoteMarketDepthLevel, bytes) ← BidPriceQuoteMarketDepthLevel.decode bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (numberOfBidOrders, bytes) ← Alpha.decode 2 bytes
  let (askPriceQuoteMarketDepthLevel, bytes) ← AskPriceQuoteMarketDepthLevel.decode bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (numberOfAskOrders, bytes) ← Alpha.decode 2 bytes
  pure ({ levelOfMarketDepth, bidPriceQuoteMarketDepthLevel, bidSize, numberOfBidOrders, askPriceQuoteMarketDepthLevel, askSize, numberOfAskOrders }, bytes)

@[simp] theorem encode_length (message : MarketDepthLevel) : (encode message).length = 31 := by
  unfold encode
  simp only [List.length_append, LevelOfMarketDepth.encode_length, BidPriceQuoteMarketDepthLevel.encode_length, Alpha.encode_length, AskPriceQuoteMarketDepthLevel.encode_length]

theorem encode_length_pos (message : MarketDepthLevel) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketDepthLevel) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LevelOfMarketDepth.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BidPriceQuoteMarketDepthLevel.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskPriceQuoteMarketDepthLevel.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end MarketDepthLevel

/-- Option Market Depth Message -/
structure OptionMarketDepthMessage where
  exchangeId : ExchangeId
  optionSymbol : OptionSymbol
  instrumentStatusMarker : InstrumentStatusMarker
  marketDepthLevel : Digited 1 MarketDepthLevel
  deriving DecidableEq, Repr

namespace OptionMarketDepthMessage

def encode (message : OptionMarketDepthMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (OptionSymbol.encode message.optionSymbol
    ++ (InstrumentStatusMarker.encode message.instrumentStatusMarker
    ++ (encodeDigits 1 message.marketDepthLevel.val.length
    ++ (encodeMany MarketDepthLevel.encode message.marketDepthLevel.val))))

def decode (bytes : List UInt8) : Option (OptionMarketDepthMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (optionSymbol, bytes) ← OptionSymbol.decode bytes
  let (instrumentStatusMarker, bytes) ← InstrumentStatusMarker.decode bytes
  let (numberOfLevels, bytes) ← decodeDigits 1 bytes
  let (marketDepthLevel_, bytes) ← decodeMany MarketDepthLevel.decode numberOfLevels bytes
  if fits_marketDepthLevel : marketDepthLevel_.length < 10 ^ 1 then
    pure ({ exchangeId, optionSymbol, instrumentStatusMarker, marketDepthLevel := ⟨marketDepthLevel_, fits_marketDepthLevel⟩ }, bytes)
  else none

theorem encode_length_pos (message : OptionMarketDepthMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [ExchangeId.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OptionMarketDepthMessage) : (encode message).length ≤ 301 := by
  have bound_marketDepthLevel := message.marketDepthLevel.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, ExchangeId.encode_length, OptionSymbol.encode_length, InstrumentStatusMarker.encode_length, encodeDigits_length, encodeMany_length_const MarketDepthLevel.encode 31 MarketDepthLevel.encode_length]
  omega

@[simp] theorem decode_encode (message : OptionMarketDepthMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentStatusMarker.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.marketDepthLevel.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany MarketDepthLevel.encode MarketDepthLevel.decode MarketDepthLevel.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.marketDepthLevel.length_lt]
  rfl

end OptionMarketDepthMessage

/-- Bid Price Quote Market Depth Level HB: 8 bytes -/
structure BidPriceQuoteMarketDepthLevelHb where
  rawBidPriceQuoteNumericBidPriceQuoteMarketDepthLevelHbNumericPair : Alpha 7
  bidPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace BidPriceQuoteMarketDepthLevelHb

def encode (message : BidPriceQuoteMarketDepthLevelHb) : List UInt8 :=
  Alpha.encode message.rawBidPriceQuoteNumericBidPriceQuoteMarketDepthLevelHbNumericPair
    ++ (encodeUInt 1 message.bidPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (BidPriceQuoteMarketDepthLevelHb × List UInt8) := do
  let (rawBidPriceQuoteNumericBidPriceQuoteMarketDepthLevelHbNumericPair, bytes) ← Alpha.decode 7 bytes
  let (bidPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawBidPriceQuoteNumericBidPriceQuoteMarketDepthLevelHbNumericPair, bidPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : BidPriceQuoteMarketDepthLevelHb) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : BidPriceQuoteMarketDepthLevelHb) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BidPriceQuoteMarketDepthLevelHb) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end BidPriceQuoteMarketDepthLevelHb

/-- Ask Price Quote Market Depth Level HB: 8 bytes -/
structure AskPriceQuoteMarketDepthLevelHb where
  rawAskPriceQuoteNumericAskPriceQuoteMarketDepthLevelHbNumericPair : Alpha 7
  askPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace AskPriceQuoteMarketDepthLevelHb

def encode (message : AskPriceQuoteMarketDepthLevelHb) : List UInt8 :=
  Alpha.encode message.rawAskPriceQuoteNumericAskPriceQuoteMarketDepthLevelHbNumericPair
    ++ (encodeUInt 1 message.askPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (AskPriceQuoteMarketDepthLevelHb × List UInt8) := do
  let (rawAskPriceQuoteNumericAskPriceQuoteMarketDepthLevelHbNumericPair, bytes) ← Alpha.decode 7 bytes
  let (askPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawAskPriceQuoteNumericAskPriceQuoteMarketDepthLevelHbNumericPair, askPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : AskPriceQuoteMarketDepthLevelHb) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : AskPriceQuoteMarketDepthLevelHb) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AskPriceQuoteMarketDepthLevelHb) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end AskPriceQuoteMarketDepthLevelHb

/-- Future Options Market Depth Level: 31 bytes -/
structure FutureOptionsMarketDepthLevel where
  levelOfMarketDepth : LevelOfMarketDepth
  bidPriceQuoteMarketDepthLevelHb : BidPriceQuoteMarketDepthLevelHb
  bidSize : Alpha 5
  numberOfBidOrders : Alpha 2
  askPriceQuoteMarketDepthLevelHb : AskPriceQuoteMarketDepthLevelHb
  askSize : Alpha 5
  numberOfAskOrders : Alpha 2
  deriving DecidableEq, Repr

namespace FutureOptionsMarketDepthLevel

def encode (message : FutureOptionsMarketDepthLevel) : List UInt8 :=
  LevelOfMarketDepth.encode message.levelOfMarketDepth
    ++ (BidPriceQuoteMarketDepthLevelHb.encode message.bidPriceQuoteMarketDepthLevelHb
    ++ (Alpha.encode message.bidSize
    ++ (Alpha.encode message.numberOfBidOrders
    ++ (AskPriceQuoteMarketDepthLevelHb.encode message.askPriceQuoteMarketDepthLevelHb
    ++ (Alpha.encode message.askSize
    ++ (Alpha.encode message.numberOfAskOrders))))))

def decode (bytes : List UInt8) : Option (FutureOptionsMarketDepthLevel × List UInt8) := do
  let (levelOfMarketDepth, bytes) ← LevelOfMarketDepth.decode bytes
  let (bidPriceQuoteMarketDepthLevelHb, bytes) ← BidPriceQuoteMarketDepthLevelHb.decode bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (numberOfBidOrders, bytes) ← Alpha.decode 2 bytes
  let (askPriceQuoteMarketDepthLevelHb, bytes) ← AskPriceQuoteMarketDepthLevelHb.decode bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (numberOfAskOrders, bytes) ← Alpha.decode 2 bytes
  pure ({ levelOfMarketDepth, bidPriceQuoteMarketDepthLevelHb, bidSize, numberOfBidOrders, askPriceQuoteMarketDepthLevelHb, askSize, numberOfAskOrders }, bytes)

@[simp] theorem encode_length (message : FutureOptionsMarketDepthLevel) : (encode message).length = 31 := by
  unfold encode
  simp only [List.length_append, LevelOfMarketDepth.encode_length, BidPriceQuoteMarketDepthLevelHb.encode_length, Alpha.encode_length, AskPriceQuoteMarketDepthLevelHb.encode_length]

theorem encode_length_pos (message : FutureOptionsMarketDepthLevel) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FutureOptionsMarketDepthLevel) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LevelOfMarketDepth.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BidPriceQuoteMarketDepthLevelHb.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskPriceQuoteMarketDepthLevelHb.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FutureOptionsMarketDepthLevel

/-- Future Options Market Depth Message -/
structure FutureOptionsMarketDepthMessage where
  exchangeId : ExchangeId
  futureOptionSymbol : FutureOptionSymbol
  instrumentStatusMarker : InstrumentStatusMarker
  futureOptionsMarketDepthLevel : Digited 1 FutureOptionsMarketDepthLevel
  deriving DecidableEq, Repr

namespace FutureOptionsMarketDepthMessage

def encode (message : FutureOptionsMarketDepthMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (FutureOptionSymbol.encode message.futureOptionSymbol
    ++ (InstrumentStatusMarker.encode message.instrumentStatusMarker
    ++ (encodeDigits 1 message.futureOptionsMarketDepthLevel.val.length
    ++ (encodeMany FutureOptionsMarketDepthLevel.encode message.futureOptionsMarketDepthLevel.val))))

def decode (bytes : List UInt8) : Option (FutureOptionsMarketDepthMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (futureOptionSymbol, bytes) ← FutureOptionSymbol.decode bytes
  let (instrumentStatusMarker, bytes) ← InstrumentStatusMarker.decode bytes
  let (numberOfLevels, bytes) ← decodeDigits 1 bytes
  let (futureOptionsMarketDepthLevel_, bytes) ← decodeMany FutureOptionsMarketDepthLevel.decode numberOfLevels bytes
  if fits_futureOptionsMarketDepthLevel : futureOptionsMarketDepthLevel_.length < 10 ^ 1 then
    pure ({ exchangeId, futureOptionSymbol, instrumentStatusMarker, futureOptionsMarketDepthLevel := ⟨futureOptionsMarketDepthLevel_, fits_futureOptionsMarketDepthLevel⟩ }, bytes)
  else none

theorem encode_length_pos (message : FutureOptionsMarketDepthMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [ExchangeId.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : FutureOptionsMarketDepthMessage) : (encode message).length ≤ 302 := by
  have bound_futureOptionsMarketDepthLevel := message.futureOptionsMarketDepthLevel.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, ExchangeId.encode_length, FutureOptionSymbol.encode_length, InstrumentStatusMarker.encode_length, encodeDigits_length, encodeMany_length_const FutureOptionsMarketDepthLevel.encode 31 FutureOptionsMarketDepthLevel.encode_length]
  omega

@[simp] theorem decode_encode (message : FutureOptionsMarketDepthMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureOptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentStatusMarker.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.futureOptionsMarketDepthLevel.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany FutureOptionsMarketDepthLevel.encode FutureOptionsMarketDepthLevel.decode FutureOptionsMarketDepthLevel.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.futureOptionsMarketDepthLevel.length_lt]
  rfl

end FutureOptionsMarketDepthMessage

/-- Bid Price Quote Market Depth Level HF: 8 bytes -/
structure BidPriceQuoteMarketDepthLevelHf where
  rawBidPriceQuoteNumericBidPriceQuoteMarketDepthLevelHfNumericPair : Alpha 7
  bidPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace BidPriceQuoteMarketDepthLevelHf

def encode (message : BidPriceQuoteMarketDepthLevelHf) : List UInt8 :=
  Alpha.encode message.rawBidPriceQuoteNumericBidPriceQuoteMarketDepthLevelHfNumericPair
    ++ (encodeUInt 1 message.bidPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (BidPriceQuoteMarketDepthLevelHf × List UInt8) := do
  let (rawBidPriceQuoteNumericBidPriceQuoteMarketDepthLevelHfNumericPair, bytes) ← Alpha.decode 7 bytes
  let (bidPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawBidPriceQuoteNumericBidPriceQuoteMarketDepthLevelHfNumericPair, bidPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : BidPriceQuoteMarketDepthLevelHf) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : BidPriceQuoteMarketDepthLevelHf) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BidPriceQuoteMarketDepthLevelHf) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end BidPriceQuoteMarketDepthLevelHf

/-- Ask Price Futures Depth Market Depth Level HF: 8 bytes -/
structure AskPriceFuturesDepthMarketDepthLevelHf where
  rawAskPriceFuturesDepthNumeric : Alpha 7
  askPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace AskPriceFuturesDepthMarketDepthLevelHf

def encode (message : AskPriceFuturesDepthMarketDepthLevelHf) : List UInt8 :=
  Alpha.encode message.rawAskPriceFuturesDepthNumeric
    ++ (encodeUInt 1 message.askPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (AskPriceFuturesDepthMarketDepthLevelHf × List UInt8) := do
  let (rawAskPriceFuturesDepthNumeric, bytes) ← Alpha.decode 7 bytes
  let (askPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawAskPriceFuturesDepthNumeric, askPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : AskPriceFuturesDepthMarketDepthLevelHf) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : AskPriceFuturesDepthMarketDepthLevelHf) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AskPriceFuturesDepthMarketDepthLevelHf) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end AskPriceFuturesDepthMarketDepthLevelHf

/-- Futures Market Depth Level: 31 bytes -/
structure FuturesMarketDepthLevel where
  levelOfMarketDepth : LevelOfMarketDepth
  bidPriceQuoteMarketDepthLevelHf : BidPriceQuoteMarketDepthLevelHf
  bidSize : Alpha 5
  numberOfBidOrders : Alpha 2
  askPriceFuturesDepthMarketDepthLevelHf : AskPriceFuturesDepthMarketDepthLevelHf
  askSize : Alpha 5
  numberOfAskOrders : Alpha 2
  deriving DecidableEq, Repr

namespace FuturesMarketDepthLevel

def encode (message : FuturesMarketDepthLevel) : List UInt8 :=
  LevelOfMarketDepth.encode message.levelOfMarketDepth
    ++ (BidPriceQuoteMarketDepthLevelHf.encode message.bidPriceQuoteMarketDepthLevelHf
    ++ (Alpha.encode message.bidSize
    ++ (Alpha.encode message.numberOfBidOrders
    ++ (AskPriceFuturesDepthMarketDepthLevelHf.encode message.askPriceFuturesDepthMarketDepthLevelHf
    ++ (Alpha.encode message.askSize
    ++ (Alpha.encode message.numberOfAskOrders))))))

def decode (bytes : List UInt8) : Option (FuturesMarketDepthLevel × List UInt8) := do
  let (levelOfMarketDepth, bytes) ← LevelOfMarketDepth.decode bytes
  let (bidPriceQuoteMarketDepthLevelHf, bytes) ← BidPriceQuoteMarketDepthLevelHf.decode bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (numberOfBidOrders, bytes) ← Alpha.decode 2 bytes
  let (askPriceFuturesDepthMarketDepthLevelHf, bytes) ← AskPriceFuturesDepthMarketDepthLevelHf.decode bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (numberOfAskOrders, bytes) ← Alpha.decode 2 bytes
  pure ({ levelOfMarketDepth, bidPriceQuoteMarketDepthLevelHf, bidSize, numberOfBidOrders, askPriceFuturesDepthMarketDepthLevelHf, askSize, numberOfAskOrders }, bytes)

@[simp] theorem encode_length (message : FuturesMarketDepthLevel) : (encode message).length = 31 := by
  unfold encode
  simp only [List.length_append, LevelOfMarketDepth.encode_length, BidPriceQuoteMarketDepthLevelHf.encode_length, Alpha.encode_length, AskPriceFuturesDepthMarketDepthLevelHf.encode_length]

theorem encode_length_pos (message : FuturesMarketDepthLevel) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FuturesMarketDepthLevel) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LevelOfMarketDepth.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BidPriceQuoteMarketDepthLevelHf.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskPriceFuturesDepthMarketDepthLevelHf.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FuturesMarketDepthLevel

/-- Futures Market Depth Message -/
structure FuturesMarketDepthMessage where
  exchangeId : ExchangeId
  futureProduct : FutureProduct
  instrumentStatusMarker : InstrumentStatusMarker
  futuresMarketDepthLevel : Digited 1 FuturesMarketDepthLevel
  deriving DecidableEq, Repr

namespace FuturesMarketDepthMessage

def encode (message : FuturesMarketDepthMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (FutureProduct.encode message.futureProduct
    ++ (InstrumentStatusMarker.encode message.instrumentStatusMarker
    ++ (encodeDigits 1 message.futuresMarketDepthLevel.val.length
    ++ (encodeMany FuturesMarketDepthLevel.encode message.futuresMarketDepthLevel.val))))

def decode (bytes : List UInt8) : Option (FuturesMarketDepthMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (futureProduct, bytes) ← FutureProduct.decode bytes
  let (instrumentStatusMarker, bytes) ← InstrumentStatusMarker.decode bytes
  let (numberOfLevels, bytes) ← decodeDigits 1 bytes
  let (futuresMarketDepthLevel_, bytes) ← decodeMany FuturesMarketDepthLevel.decode numberOfLevels bytes
  if fits_futuresMarketDepthLevel : futuresMarketDepthLevel_.length < 10 ^ 1 then
    pure ({ exchangeId, futureProduct, instrumentStatusMarker, futuresMarketDepthLevel := ⟨futuresMarketDepthLevel_, fits_futuresMarketDepthLevel⟩ }, bytes)
  else none

theorem encode_length_pos (message : FuturesMarketDepthMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [ExchangeId.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : FuturesMarketDepthMessage) : (encode message).length ≤ 293 := by
  have bound_futuresMarketDepthLevel := message.futuresMarketDepthLevel.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, ExchangeId.encode_length, FutureProduct.encode_length, InstrumentStatusMarker.encode_length, encodeDigits_length, encodeMany_length_const FuturesMarketDepthLevel.encode 31 FuturesMarketDepthLevel.encode_length]
  omega

@[simp] theorem decode_encode (message : FuturesMarketDepthMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureProduct.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentStatusMarker.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.futuresMarketDepthLevel.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany FuturesMarketDepthLevel.encode FuturesMarketDepthLevel.decode FuturesMarketDepthLevel.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.futuresMarketDepthLevel.length_lt]
  rfl

end FuturesMarketDepthMessage

/-- Bid Price Quote Strategy Market Depth Level: 8 bytes -/
structure BidPriceQuoteStrategyMarketDepthLevel where
  rawBidPriceQuoteNumericBidPriceQuoteStrategyMarketDepthLevelNumericPair : Alpha 7
  bidPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace BidPriceQuoteStrategyMarketDepthLevel

def encode (message : BidPriceQuoteStrategyMarketDepthLevel) : List UInt8 :=
  Alpha.encode message.rawBidPriceQuoteNumericBidPriceQuoteStrategyMarketDepthLevelNumericPair
    ++ (encodeUInt 1 message.bidPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (BidPriceQuoteStrategyMarketDepthLevel × List UInt8) := do
  let (rawBidPriceQuoteNumericBidPriceQuoteStrategyMarketDepthLevelNumericPair, bytes) ← Alpha.decode 7 bytes
  let (bidPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawBidPriceQuoteNumericBidPriceQuoteStrategyMarketDepthLevelNumericPair, bidPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : BidPriceQuoteStrategyMarketDepthLevel) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : BidPriceQuoteStrategyMarketDepthLevel) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BidPriceQuoteStrategyMarketDepthLevel) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end BidPriceQuoteStrategyMarketDepthLevel

/-- Ask Price Quote Strategy Market Depth Level: 8 bytes -/
structure AskPriceQuoteStrategyMarketDepthLevel where
  rawAskPriceQuoteNumericAskPriceQuoteStrategyMarketDepthLevelNumericPair : Alpha 7
  askPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace AskPriceQuoteStrategyMarketDepthLevel

def encode (message : AskPriceQuoteStrategyMarketDepthLevel) : List UInt8 :=
  Alpha.encode message.rawAskPriceQuoteNumericAskPriceQuoteStrategyMarketDepthLevelNumericPair
    ++ (encodeUInt 1 message.askPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (AskPriceQuoteStrategyMarketDepthLevel × List UInt8) := do
  let (rawAskPriceQuoteNumericAskPriceQuoteStrategyMarketDepthLevelNumericPair, bytes) ← Alpha.decode 7 bytes
  let (askPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawAskPriceQuoteNumericAskPriceQuoteStrategyMarketDepthLevelNumericPair, askPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : AskPriceQuoteStrategyMarketDepthLevel) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : AskPriceQuoteStrategyMarketDepthLevel) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AskPriceQuoteStrategyMarketDepthLevel) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end AskPriceQuoteStrategyMarketDepthLevel

/-- Strategy Market Depth Level: 33 bytes -/
structure StrategyMarketDepthLevel where
  levelOfMarketDepth : LevelOfMarketDepth
  bidPriceSign : BidPriceSign
  bidPriceQuoteStrategyMarketDepthLevel : BidPriceQuoteStrategyMarketDepthLevel
  bidSize : Alpha 5
  numberOfBidOrders : Alpha 2
  askPriceSign : AskPriceSign
  askPriceQuoteStrategyMarketDepthLevel : AskPriceQuoteStrategyMarketDepthLevel
  askSize : Alpha 5
  numberOfAskOrders : Alpha 2
  deriving DecidableEq, Repr

namespace StrategyMarketDepthLevel

def encode (message : StrategyMarketDepthLevel) : List UInt8 :=
  LevelOfMarketDepth.encode message.levelOfMarketDepth
    ++ (BidPriceSign.encode message.bidPriceSign
    ++ (BidPriceQuoteStrategyMarketDepthLevel.encode message.bidPriceQuoteStrategyMarketDepthLevel
    ++ (Alpha.encode message.bidSize
    ++ (Alpha.encode message.numberOfBidOrders
    ++ (AskPriceSign.encode message.askPriceSign
    ++ (AskPriceQuoteStrategyMarketDepthLevel.encode message.askPriceQuoteStrategyMarketDepthLevel
    ++ (Alpha.encode message.askSize
    ++ (Alpha.encode message.numberOfAskOrders))))))))

def decode (bytes : List UInt8) : Option (StrategyMarketDepthLevel × List UInt8) := do
  let (levelOfMarketDepth, bytes) ← LevelOfMarketDepth.decode bytes
  let (bidPriceSign, bytes) ← BidPriceSign.decode bytes
  let (bidPriceQuoteStrategyMarketDepthLevel, bytes) ← BidPriceQuoteStrategyMarketDepthLevel.decode bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (numberOfBidOrders, bytes) ← Alpha.decode 2 bytes
  let (askPriceSign, bytes) ← AskPriceSign.decode bytes
  let (askPriceQuoteStrategyMarketDepthLevel, bytes) ← AskPriceQuoteStrategyMarketDepthLevel.decode bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (numberOfAskOrders, bytes) ← Alpha.decode 2 bytes
  pure ({ levelOfMarketDepth, bidPriceSign, bidPriceQuoteStrategyMarketDepthLevel, bidSize, numberOfBidOrders, askPriceSign, askPriceQuoteStrategyMarketDepthLevel, askSize, numberOfAskOrders }, bytes)

@[simp] theorem encode_length (message : StrategyMarketDepthLevel) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, LevelOfMarketDepth.encode_length, BidPriceSign.encode_length, BidPriceQuoteStrategyMarketDepthLevel.encode_length, Alpha.encode_length, AskPriceSign.encode_length, AskPriceQuoteStrategyMarketDepthLevel.encode_length]

theorem encode_length_pos (message : StrategyMarketDepthLevel) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyMarketDepthLevel) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LevelOfMarketDepth.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BidPriceSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BidPriceQuoteStrategyMarketDepthLevel.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskPriceSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskPriceQuoteStrategyMarketDepthLevel.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StrategyMarketDepthLevel

/-- Strategy Market Depth Message -/
structure StrategyMarketDepthMessage where
  exchangeId : ExchangeId
  symbol : Alpha 30
  instrumentStatusMarker : InstrumentStatusMarker
  strategyMarketDepthLevel : Digited 1 StrategyMarketDepthLevel
  deriving DecidableEq, Repr

namespace StrategyMarketDepthMessage

def encode (message : StrategyMarketDepthMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.symbol
    ++ (InstrumentStatusMarker.encode message.instrumentStatusMarker
    ++ (encodeDigits 1 message.strategyMarketDepthLevel.val.length
    ++ (encodeMany StrategyMarketDepthLevel.encode message.strategyMarketDepthLevel.val))))

def decode (bytes : List UInt8) : Option (StrategyMarketDepthMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (symbol, bytes) ← Alpha.decode 30 bytes
  let (instrumentStatusMarker, bytes) ← InstrumentStatusMarker.decode bytes
  let (numberOfLevels, bytes) ← decodeDigits 1 bytes
  let (strategyMarketDepthLevel_, bytes) ← decodeMany StrategyMarketDepthLevel.decode numberOfLevels bytes
  if fits_strategyMarketDepthLevel : strategyMarketDepthLevel_.length < 10 ^ 1 then
    pure ({ exchangeId, symbol, instrumentStatusMarker, strategyMarketDepthLevel := ⟨strategyMarketDepthLevel_, fits_strategyMarketDepthLevel⟩ }, bytes)
  else none

theorem encode_length_pos (message : StrategyMarketDepthMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [ExchangeId.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : StrategyMarketDepthMessage) : (encode message).length ≤ 330 := by
  have bound_strategyMarketDepthLevel := message.strategyMarketDepthLevel.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, ExchangeId.encode_length, Alpha.encode_length, InstrumentStatusMarker.encode_length, encodeDigits_length, encodeMany_length_const StrategyMarketDepthLevel.encode 33 StrategyMarketDepthLevel.encode_length]
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
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.strategyMarketDepthLevel.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany StrategyMarketDepthLevel.encode StrategyMarketDepthLevel.decode StrategyMarketDepthLevel.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.strategyMarketDepthLevel.length_lt]
  rfl

end StrategyMarketDepthMessage

/-- Option Trade Cancellation Message: 51 bytes -/
structure OptionTradeCancellationMessage where
  exchangeId : ExchangeId
  optionSymbol : OptionSymbol
  volume : Alpha 8
  tradePriceFractionPair : TradePriceFractionPair
  priceIndicatorMarker : PriceIndicatorMarker
  tradeNumber : Alpha 8
  auctionId : Alpha 6
  deriving DecidableEq, Repr

namespace OptionTradeCancellationMessage

def encode (message : OptionTradeCancellationMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (OptionSymbol.encode message.optionSymbol
    ++ (Alpha.encode message.volume
    ++ (TradePriceFractionPair.encode message.tradePriceFractionPair
    ++ (PriceIndicatorMarker.encode message.priceIndicatorMarker
    ++ (Alpha.encode message.tradeNumber
    ++ (Alpha.encode message.auctionId))))))

def decode (bytes : List UInt8) : Option (OptionTradeCancellationMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (optionSymbol, bytes) ← OptionSymbol.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePriceFractionPair, bytes) ← TradePriceFractionPair.decode bytes
  let (priceIndicatorMarker, bytes) ← PriceIndicatorMarker.decode bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  let (auctionId, bytes) ← Alpha.decode 6 bytes
  pure ({ exchangeId, optionSymbol, volume, tradePriceFractionPair, priceIndicatorMarker, tradeNumber, auctionId }, bytes)

@[simp] theorem encode_length (message : OptionTradeCancellationMessage) : (encode message).length = 51 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, OptionSymbol.encode_length, Alpha.encode_length, TradePriceFractionPair.encode_length, PriceIndicatorMarker.encode_length]

theorem encode_length_pos (message : OptionTradeCancellationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionTradeCancellationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradePriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PriceIndicatorMarker.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OptionTradeCancellationMessage

/-- Future Options Trade Cancellation Message: 52 bytes -/
structure FutureOptionsTradeCancellationMessage where
  exchangeId : ExchangeId
  futureOptionSymbol : FutureOptionSymbol
  volume : Alpha 8
  tradePriceFractionPair : TradePriceFractionPair
  priceIndicatorMarker : PriceIndicatorMarker
  tradeNumber : Alpha 8
  auctionId : Alpha 6
  deriving DecidableEq, Repr

namespace FutureOptionsTradeCancellationMessage

def encode (message : FutureOptionsTradeCancellationMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (FutureOptionSymbol.encode message.futureOptionSymbol
    ++ (Alpha.encode message.volume
    ++ (TradePriceFractionPair.encode message.tradePriceFractionPair
    ++ (PriceIndicatorMarker.encode message.priceIndicatorMarker
    ++ (Alpha.encode message.tradeNumber
    ++ (Alpha.encode message.auctionId))))))

def decode (bytes : List UInt8) : Option (FutureOptionsTradeCancellationMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (futureOptionSymbol, bytes) ← FutureOptionSymbol.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePriceFractionPair, bytes) ← TradePriceFractionPair.decode bytes
  let (priceIndicatorMarker, bytes) ← PriceIndicatorMarker.decode bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  let (auctionId, bytes) ← Alpha.decode 6 bytes
  pure ({ exchangeId, futureOptionSymbol, volume, tradePriceFractionPair, priceIndicatorMarker, tradeNumber, auctionId }, bytes)

@[simp] theorem encode_length (message : FutureOptionsTradeCancellationMessage) : (encode message).length = 52 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, FutureOptionSymbol.encode_length, Alpha.encode_length, TradePriceFractionPair.encode_length, PriceIndicatorMarker.encode_length]

theorem encode_length_pos (message : FutureOptionsTradeCancellationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FutureOptionsTradeCancellationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureOptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradePriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PriceIndicatorMarker.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FutureOptionsTradeCancellationMessage

/-- Future Trade Cancellation Message: 43 bytes -/
structure FutureTradeCancellationMessage where
  exchangeId : ExchangeId
  futureProduct : FutureProduct
  volume : Alpha 8
  tradePriceFractionPair : TradePriceFractionPair
  priceIndicatorMarker : FuturesTradeMessagePriceIndicatorMarker
  tradeNumber : Alpha 8
  auctionId : Alpha 6
  deriving DecidableEq, Repr

namespace FutureTradeCancellationMessage

def encode (message : FutureTradeCancellationMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (FutureProduct.encode message.futureProduct
    ++ (Alpha.encode message.volume
    ++ (TradePriceFractionPair.encode message.tradePriceFractionPair
    ++ (FuturesTradeMessagePriceIndicatorMarker.encode message.priceIndicatorMarker
    ++ (Alpha.encode message.tradeNumber
    ++ (Alpha.encode message.auctionId))))))

def decode (bytes : List UInt8) : Option (FutureTradeCancellationMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (futureProduct, bytes) ← FutureProduct.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePriceFractionPair, bytes) ← TradePriceFractionPair.decode bytes
  let (priceIndicatorMarker, bytes) ← FuturesTradeMessagePriceIndicatorMarker.decode bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  let (auctionId, bytes) ← Alpha.decode 6 bytes
  pure ({ exchangeId, futureProduct, volume, tradePriceFractionPair, priceIndicatorMarker, tradeNumber, auctionId }, bytes)

@[simp] theorem encode_length (message : FutureTradeCancellationMessage) : (encode message).length = 43 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, FutureProduct.encode_length, Alpha.encode_length, TradePriceFractionPair.encode_length, FuturesTradeMessagePriceIndicatorMarker.encode_length]

theorem encode_length_pos (message : FutureTradeCancellationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FutureTradeCancellationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureProduct.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradePriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FuturesTradeMessagePriceIndicatorMarker.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FutureTradeCancellationMessage

/-- Strategy Trade Cancellation Message: 62 bytes -/
structure StrategyTradeCancellationMessage where
  exchangeId : ExchangeId
  symbol : Alpha 30
  volume : Alpha 8
  tradePriceSign : TradePriceSign
  tradePriceFractionPair : TradePriceFractionPair
  tradeNumber : Alpha 8
  auctionId : Alpha 6
  deriving DecidableEq, Repr

namespace StrategyTradeCancellationMessage

def encode (message : StrategyTradeCancellationMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.volume
    ++ (TradePriceSign.encode message.tradePriceSign
    ++ (TradePriceFractionPair.encode message.tradePriceFractionPair
    ++ (Alpha.encode message.tradeNumber
    ++ (Alpha.encode message.auctionId))))))

def decode (bytes : List UInt8) : Option (StrategyTradeCancellationMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (symbol, bytes) ← Alpha.decode 30 bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePriceSign, bytes) ← TradePriceSign.decode bytes
  let (tradePriceFractionPair, bytes) ← TradePriceFractionPair.decode bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  let (auctionId, bytes) ← Alpha.decode 6 bytes
  pure ({ exchangeId, symbol, volume, tradePriceSign, tradePriceFractionPair, tradeNumber, auctionId }, bytes)

@[simp] theorem encode_length (message : StrategyTradeCancellationMessage) : (encode message).length = 62 := by
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end StrategyTradeCancellationMessage

/-- Maximum Threshold Price Fraction Pair: 8 bytes -/
structure MaximumThresholdPriceFractionPair where
  rawMaximumThresholdPrice : Alpha 7
  maximumThresholdPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace MaximumThresholdPriceFractionPair

def encode (message : MaximumThresholdPriceFractionPair) : List UInt8 :=
  Alpha.encode message.rawMaximumThresholdPrice
    ++ (encodeUInt 1 message.maximumThresholdPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (MaximumThresholdPriceFractionPair × List UInt8) := do
  let (rawMaximumThresholdPrice, bytes) ← Alpha.decode 7 bytes
  let (maximumThresholdPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawMaximumThresholdPrice, maximumThresholdPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : MaximumThresholdPriceFractionPair) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : MaximumThresholdPriceFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MaximumThresholdPriceFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MaximumThresholdPriceFractionPair

/-- Minimum Threshold Price Instrument Fraction Pair: 8 bytes -/
structure MinimumThresholdPriceInstrumentFractionPair where
  rawMinimumThresholdPriceInstrument : Alpha 7
  minimumThresholdPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace MinimumThresholdPriceInstrumentFractionPair

def encode (message : MinimumThresholdPriceInstrumentFractionPair) : List UInt8 :=
  Alpha.encode message.rawMinimumThresholdPriceInstrument
    ++ (encodeUInt 1 message.minimumThresholdPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (MinimumThresholdPriceInstrumentFractionPair × List UInt8) := do
  let (rawMinimumThresholdPriceInstrument, bytes) ← Alpha.decode 7 bytes
  let (minimumThresholdPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawMinimumThresholdPriceInstrument, minimumThresholdPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : MinimumThresholdPriceInstrumentFractionPair) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : MinimumThresholdPriceInstrumentFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MinimumThresholdPriceInstrumentFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MinimumThresholdPriceInstrumentFractionPair

/-- Tick Increment: 8 bytes -/
structure TickIncrement where
  tickIncrementNumeric : Alpha 7
  tickIncrementFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace TickIncrement

def encode (message : TickIncrement) : List UInt8 :=
  Alpha.encode message.tickIncrementNumeric
    ++ (encodeUInt 1 message.tickIncrementFractionIndicator)

def decode (bytes : List UInt8) : Option (TickIncrement × List UInt8) := do
  let (tickIncrementNumeric, bytes) ← Alpha.decode 7 bytes
  let (tickIncrementFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ tickIncrementNumeric, tickIncrementFractionIndicator }, bytes)

@[simp] theorem encode_length (message : TickIncrement) : (encode message).length = 8 := by
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

/-- Tick Value Fraction Pair: 8 bytes -/
structure TickValueFractionPair where
  rawTickValue : Alpha 7
  tickValueFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace TickValueFractionPair

def encode (message : TickValueFractionPair) : List UInt8 :=
  Alpha.encode message.rawTickValue
    ++ (encodeUInt 1 message.tickValueFractionIndicator)

def decode (bytes : List UInt8) : Option (TickValueFractionPair × List UInt8) := do
  let (rawTickValue, bytes) ← Alpha.decode 7 bytes
  let (tickValueFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawTickValue, tickValueFractionIndicator }, bytes)

@[simp] theorem encode_length (message : TickValueFractionPair) : (encode message).length = 8 := by
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

/-- Option Instrument Keys Message: 146 bytes -/
structure OptionInstrumentKeysMessage where
  exchangeId : ExchangeId
  optionSymbol : OptionSymbol
  strikePriceCurrency : Alpha 3
  maximumNumberOfContractsPerOrder : Alpha 6
  minimumNumberOfContractsPerOrder : Alpha 6
  maximumThresholdPriceFractionPair : MaximumThresholdPriceFractionPair
  minimumThresholdPriceInstrumentFractionPair : MinimumThresholdPriceInstrumentFractionPair
  tickIncrement : TickIncrement
  optionType : OptionType
  marketFlowIndicator : Alpha 2
  groupInstrument : Alpha 2
  instrument : Alpha 4
  instrumentExternalCode : Alpha 30
  optionMarker : Alpha 2
  underlyingSymbolRoot : Alpha 12
  contractSize : Alpha 8
  tickValueFractionPair : TickValueFractionPair
  currency : Alpha 3
  deliveryType : DeliveryType
  lastTradingDatetime : Alpha 14
  deriving DecidableEq, Repr

namespace OptionInstrumentKeysMessage

def encode (message : OptionInstrumentKeysMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (OptionSymbol.encode message.optionSymbol
    ++ (Alpha.encode message.strikePriceCurrency
    ++ (Alpha.encode message.maximumNumberOfContractsPerOrder
    ++ (Alpha.encode message.minimumNumberOfContractsPerOrder
    ++ (MaximumThresholdPriceFractionPair.encode message.maximumThresholdPriceFractionPair
    ++ (MinimumThresholdPriceInstrumentFractionPair.encode message.minimumThresholdPriceInstrumentFractionPair
    ++ (TickIncrement.encode message.tickIncrement
    ++ (OptionType.encode message.optionType
    ++ (Alpha.encode message.marketFlowIndicator
    ++ (Alpha.encode message.groupInstrument
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.instrumentExternalCode
    ++ (Alpha.encode message.optionMarker
    ++ (Alpha.encode message.underlyingSymbolRoot
    ++ (Alpha.encode message.contractSize
    ++ (TickValueFractionPair.encode message.tickValueFractionPair
    ++ (Alpha.encode message.currency
    ++ (DeliveryType.encode message.deliveryType
    ++ (Alpha.encode message.lastTradingDatetime)))))))))))))))))))

def decode (bytes : List UInt8) : Option (OptionInstrumentKeysMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (optionSymbol, bytes) ← OptionSymbol.decode bytes
  let (strikePriceCurrency, bytes) ← Alpha.decode 3 bytes
  let (maximumNumberOfContractsPerOrder, bytes) ← Alpha.decode 6 bytes
  let (minimumNumberOfContractsPerOrder, bytes) ← Alpha.decode 6 bytes
  let (maximumThresholdPriceFractionPair, bytes) ← MaximumThresholdPriceFractionPair.decode bytes
  let (minimumThresholdPriceInstrumentFractionPair, bytes) ← MinimumThresholdPriceInstrumentFractionPair.decode bytes
  let (tickIncrement, bytes) ← TickIncrement.decode bytes
  let (optionType, bytes) ← OptionType.decode bytes
  let (marketFlowIndicator, bytes) ← Alpha.decode 2 bytes
  let (groupInstrument, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (instrumentExternalCode, bytes) ← Alpha.decode 30 bytes
  let (optionMarker, bytes) ← Alpha.decode 2 bytes
  let (underlyingSymbolRoot, bytes) ← Alpha.decode 12 bytes
  let (contractSize, bytes) ← Alpha.decode 8 bytes
  let (tickValueFractionPair, bytes) ← TickValueFractionPair.decode bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (deliveryType, bytes) ← DeliveryType.decode bytes
  let (lastTradingDatetime, bytes) ← Alpha.decode 14 bytes
  pure ({ exchangeId, optionSymbol, strikePriceCurrency, maximumNumberOfContractsPerOrder, minimumNumberOfContractsPerOrder, maximumThresholdPriceFractionPair, minimumThresholdPriceInstrumentFractionPair, tickIncrement, optionType, marketFlowIndicator, groupInstrument, instrument, instrumentExternalCode, optionMarker, underlyingSymbolRoot, contractSize, tickValueFractionPair, currency, deliveryType, lastTradingDatetime }, bytes)

@[simp] theorem encode_length (message : OptionInstrumentKeysMessage) : (encode message).length = 146 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, OptionSymbol.encode_length, Alpha.encode_length, MaximumThresholdPriceFractionPair.encode_length, MinimumThresholdPriceInstrumentFractionPair.encode_length, TickIncrement.encode_length, OptionType.encode_length, TickValueFractionPair.encode_length, DeliveryType.encode_length]

theorem encode_length_pos (message : OptionInstrumentKeysMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionInstrumentKeysMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MaximumThresholdPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MinimumThresholdPriceInstrumentFractionPair.decode_encode, some_bind]
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
  rw [List.append_assoc, DeliveryType.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OptionInstrumentKeysMessage

/-- Future Options Instrument Keys Message: 147 bytes -/
structure FutureOptionsInstrumentKeysMessage where
  exchangeId : ExchangeId
  futureOptionSymbol : FutureOptionSymbol
  expiryDate : Alpha 6
  strikePriceCurrency : Alpha 3
  maximumNumberOfContractsPerOrder : Alpha 6
  minimumNumberOfContractsPerOrder : Alpha 6
  maximumThresholdPriceFractionPair : MaximumThresholdPriceFractionPair
  minimumThresholdPriceInstrumentFractionPair : MinimumThresholdPriceInstrumentFractionPair
  tickIncrement : TickIncrement
  marketFlowIndicator : Alpha 2
  groupInstrument : Alpha 2
  instrument : Alpha 4
  instrumentExternalCode : Alpha 30
  contractSize : Alpha 8
  tickValueFractionPair : TickValueFractionPair
  currency : Alpha 3
  deliveryType : DeliveryType
  underlyingRootSymbol : Alpha 6
  underlyingSymbolMonth : UnderlyingSymbolMonth
  underlyingSymbolYear : Alpha 2
  lastTradingDatetime : Alpha 14
  deriving DecidableEq, Repr

namespace FutureOptionsInstrumentKeysMessage

def encode (message : FutureOptionsInstrumentKeysMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (FutureOptionSymbol.encode message.futureOptionSymbol
    ++ (Alpha.encode message.expiryDate
    ++ (Alpha.encode message.strikePriceCurrency
    ++ (Alpha.encode message.maximumNumberOfContractsPerOrder
    ++ (Alpha.encode message.minimumNumberOfContractsPerOrder
    ++ (MaximumThresholdPriceFractionPair.encode message.maximumThresholdPriceFractionPair
    ++ (MinimumThresholdPriceInstrumentFractionPair.encode message.minimumThresholdPriceInstrumentFractionPair
    ++ (TickIncrement.encode message.tickIncrement
    ++ (Alpha.encode message.marketFlowIndicator
    ++ (Alpha.encode message.groupInstrument
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.instrumentExternalCode
    ++ (Alpha.encode message.contractSize
    ++ (TickValueFractionPair.encode message.tickValueFractionPair
    ++ (Alpha.encode message.currency
    ++ (DeliveryType.encode message.deliveryType
    ++ (Alpha.encode message.underlyingRootSymbol
    ++ (UnderlyingSymbolMonth.encode message.underlyingSymbolMonth
    ++ (Alpha.encode message.underlyingSymbolYear
    ++ (Alpha.encode message.lastTradingDatetime))))))))))))))))))))

def decode (bytes : List UInt8) : Option (FutureOptionsInstrumentKeysMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (futureOptionSymbol, bytes) ← FutureOptionSymbol.decode bytes
  let (expiryDate, bytes) ← Alpha.decode 6 bytes
  let (strikePriceCurrency, bytes) ← Alpha.decode 3 bytes
  let (maximumNumberOfContractsPerOrder, bytes) ← Alpha.decode 6 bytes
  let (minimumNumberOfContractsPerOrder, bytes) ← Alpha.decode 6 bytes
  let (maximumThresholdPriceFractionPair, bytes) ← MaximumThresholdPriceFractionPair.decode bytes
  let (minimumThresholdPriceInstrumentFractionPair, bytes) ← MinimumThresholdPriceInstrumentFractionPair.decode bytes
  let (tickIncrement, bytes) ← TickIncrement.decode bytes
  let (marketFlowIndicator, bytes) ← Alpha.decode 2 bytes
  let (groupInstrument, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (instrumentExternalCode, bytes) ← Alpha.decode 30 bytes
  let (contractSize, bytes) ← Alpha.decode 8 bytes
  let (tickValueFractionPair, bytes) ← TickValueFractionPair.decode bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (deliveryType, bytes) ← DeliveryType.decode bytes
  let (underlyingRootSymbol, bytes) ← Alpha.decode 6 bytes
  let (underlyingSymbolMonth, bytes) ← UnderlyingSymbolMonth.decode bytes
  let (underlyingSymbolYear, bytes) ← Alpha.decode 2 bytes
  let (lastTradingDatetime, bytes) ← Alpha.decode 14 bytes
  pure ({ exchangeId, futureOptionSymbol, expiryDate, strikePriceCurrency, maximumNumberOfContractsPerOrder, minimumNumberOfContractsPerOrder, maximumThresholdPriceFractionPair, minimumThresholdPriceInstrumentFractionPair, tickIncrement, marketFlowIndicator, groupInstrument, instrument, instrumentExternalCode, contractSize, tickValueFractionPair, currency, deliveryType, underlyingRootSymbol, underlyingSymbolMonth, underlyingSymbolYear, lastTradingDatetime }, bytes)

@[simp] theorem encode_length (message : FutureOptionsInstrumentKeysMessage) : (encode message).length = 147 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, FutureOptionSymbol.encode_length, Alpha.encode_length, MaximumThresholdPriceFractionPair.encode_length, MinimumThresholdPriceInstrumentFractionPair.encode_length, TickIncrement.encode_length, TickValueFractionPair.encode_length, DeliveryType.encode_length, UnderlyingSymbolMonth.encode_length]

theorem encode_length_pos (message : FutureOptionsInstrumentKeysMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FutureOptionsInstrumentKeysMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureOptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MaximumThresholdPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MinimumThresholdPriceInstrumentFractionPair.decode_encode, some_bind]
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
  rw [List.append_assoc, DeliveryType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, UnderlyingSymbolMonth.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FutureOptionsInstrumentKeysMessage

/-- Underlying Instrument Keys Message: 39 bytes -/
structure UnderlyingInstrumentKeysMessage where
  exchangeId : ExchangeId
  groupInstrument : Alpha 2
  instrument : Alpha 4
  instrumentExternalCode : Alpha 30
  marketFlowIndicator : Alpha 2
  deriving DecidableEq, Repr

namespace UnderlyingInstrumentKeysMessage

def encode (message : UnderlyingInstrumentKeysMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.groupInstrument
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.instrumentExternalCode
    ++ (Alpha.encode message.marketFlowIndicator))))

def decode (bytes : List UInt8) : Option (UnderlyingInstrumentKeysMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (groupInstrument, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (instrumentExternalCode, bytes) ← Alpha.decode 30 bytes
  let (marketFlowIndicator, bytes) ← Alpha.decode 2 bytes
  pure ({ exchangeId, groupInstrument, instrument, instrumentExternalCode, marketFlowIndicator }, bytes)

@[simp] theorem encode_length (message : UnderlyingInstrumentKeysMessage) : (encode message).length = 39 := by
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end UnderlyingInstrumentKeysMessage

/-- Maximum Threshold Price Futures Fraction Pair: 8 bytes -/
structure MaximumThresholdPriceFuturesFractionPair where
  rawMaximumThresholdPriceFutures : Alpha 7
  maximumThresholdPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace MaximumThresholdPriceFuturesFractionPair

def encode (message : MaximumThresholdPriceFuturesFractionPair) : List UInt8 :=
  Alpha.encode message.rawMaximumThresholdPriceFutures
    ++ (encodeUInt 1 message.maximumThresholdPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (MaximumThresholdPriceFuturesFractionPair × List UInt8) := do
  let (rawMaximumThresholdPriceFutures, bytes) ← Alpha.decode 7 bytes
  let (maximumThresholdPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawMaximumThresholdPriceFutures, maximumThresholdPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : MaximumThresholdPriceFuturesFractionPair) : (encode message).length = 8 := by
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

/-- Minimum Threshold Price Futures Fraction Pair: 8 bytes -/
structure MinimumThresholdPriceFuturesFractionPair where
  rawMinimumThresholdPriceFutures : Alpha 7
  minimumThresholdPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace MinimumThresholdPriceFuturesFractionPair

def encode (message : MinimumThresholdPriceFuturesFractionPair) : List UInt8 :=
  Alpha.encode message.rawMinimumThresholdPriceFutures
    ++ (encodeUInt 1 message.minimumThresholdPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (MinimumThresholdPriceFuturesFractionPair × List UInt8) := do
  let (rawMinimumThresholdPriceFutures, bytes) ← Alpha.decode 7 bytes
  let (minimumThresholdPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawMinimumThresholdPriceFutures, minimumThresholdPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : MinimumThresholdPriceFuturesFractionPair) : (encode message).length = 8 := by
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

/-- Associated Product: 11 bytes -/
structure AssociatedProduct where
  root : Alpha 6
  symbolMonth : SymbolMonth
  symbolYear : Alpha 2
  expiryDay : Alpha 2
  deriving DecidableEq, Repr

namespace AssociatedProduct

def encode (message : AssociatedProduct) : List UInt8 :=
  Alpha.encode message.root
    ++ (SymbolMonth.encode message.symbolMonth
    ++ (Alpha.encode message.symbolYear
    ++ (Alpha.encode message.expiryDay)))

def decode (bytes : List UInt8) : Option (AssociatedProduct × List UInt8) := do
  let (root, bytes) ← Alpha.decode 6 bytes
  let (symbolMonth, bytes) ← SymbolMonth.decode bytes
  let (symbolYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  pure ({ root, symbolMonth, symbolYear, expiryDay }, bytes)

@[simp] theorem encode_length (message : AssociatedProduct) : (encode message).length = 11 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, SymbolMonth.encode_length]

theorem encode_length_pos (message : AssociatedProduct) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AssociatedProduct) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SymbolMonth.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end AssociatedProduct

/-- Futures Instrument Keys Message: 149 bytes -/
structure FuturesInstrumentKeysMessage where
  exchangeId : ExchangeId
  futureProduct : FutureProduct
  expiryDate : Alpha 6
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
  underlyingSymbol : Alpha 12
  deliveryType : DeliveryType
  associatedProduct : AssociatedProduct
  lastTradingDatetime : Alpha 14
  deriving DecidableEq, Repr

namespace FuturesInstrumentKeysMessage

def encode (message : FuturesInstrumentKeysMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (FutureProduct.encode message.futureProduct
    ++ (Alpha.encode message.expiryDate
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
    ++ (AssociatedProduct.encode message.associatedProduct
    ++ (Alpha.encode message.lastTradingDatetime))))))))))))))))))

def decode (bytes : List UInt8) : Option (FuturesInstrumentKeysMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (futureProduct, bytes) ← FutureProduct.decode bytes
  let (expiryDate, bytes) ← Alpha.decode 6 bytes
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
  let (underlyingSymbol, bytes) ← Alpha.decode 12 bytes
  let (deliveryType, bytes) ← DeliveryType.decode bytes
  let (associatedProduct, bytes) ← AssociatedProduct.decode bytes
  let (lastTradingDatetime, bytes) ← Alpha.decode 14 bytes
  pure ({ exchangeId, futureProduct, expiryDate, maximumNumberOfContractsPerOrder, minimumNumberOfContractsPerOrder, maximumThresholdPriceFuturesFractionPair, minimumThresholdPriceFuturesFractionPair, tickIncrement, marketFlowIndicator, groupInstrument, instrument, instrumentExternalCode, contractSize, tickValueFractionPair, currency, underlyingSymbol, deliveryType, associatedProduct, lastTradingDatetime }, bytes)

@[simp] theorem encode_length (message : FuturesInstrumentKeysMessage) : (encode message).length = 149 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, FutureProduct.encode_length, Alpha.encode_length, MaximumThresholdPriceFuturesFractionPair.encode_length, MinimumThresholdPriceFuturesFractionPair.encode_length, TickIncrement.encode_length, TickValueFractionPair.encode_length, DeliveryType.encode_length, AssociatedProduct.encode_length]

theorem encode_length_pos (message : FuturesInstrumentKeysMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FuturesInstrumentKeysMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureProduct.decode_encode, some_bind]
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
  rw [List.append_assoc, AssociatedProduct.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FuturesInstrumentKeysMessage

/-- Minimum Threshold Price Strategy Fraction Pair: 8 bytes -/
structure MinimumThresholdPriceStrategyFractionPair where
  rawMinimumThresholdPriceStrategy : Alpha 7
  minimumThresholdPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace MinimumThresholdPriceStrategyFractionPair

def encode (message : MinimumThresholdPriceStrategyFractionPair) : List UInt8 :=
  Alpha.encode message.rawMinimumThresholdPriceStrategy
    ++ (encodeUInt 1 message.minimumThresholdPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (MinimumThresholdPriceStrategyFractionPair × List UInt8) := do
  let (rawMinimumThresholdPriceStrategy, bytes) ← Alpha.decode 7 bytes
  let (minimumThresholdPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawMinimumThresholdPriceStrategy, minimumThresholdPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : MinimumThresholdPriceStrategyFractionPair) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : MinimumThresholdPriceStrategyFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MinimumThresholdPriceStrategyFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MinimumThresholdPriceStrategyFractionPair

/-- Leg Ratio Or Delta Fraction Pair: 5 bytes -/
structure LegRatioOrDeltaFractionPair where
  rawLegRatioOrDelta : Alpha 4
  legRatioOrDeltaFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace LegRatioOrDeltaFractionPair

def encode (message : LegRatioOrDeltaFractionPair) : List UInt8 :=
  Alpha.encode message.rawLegRatioOrDelta
    ++ (encodeUInt 1 message.legRatioOrDeltaFractionIndicator)

def decode (bytes : List UInt8) : Option (LegRatioOrDeltaFractionPair × List UInt8) := do
  let (rawLegRatioOrDelta, bytes) ← Alpha.decode 4 bytes
  let (legRatioOrDeltaFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawLegRatioOrDelta, legRatioOrDeltaFractionIndicator }, bytes)

@[simp] theorem encode_length (message : LegRatioOrDeltaFractionPair) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : LegRatioOrDeltaFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LegRatioOrDeltaFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end LegRatioOrDeltaFractionPair

/-- Leg Price Fraction Pair: 8 bytes -/
structure LegPriceFractionPair where
  rawLegPrice : Alpha 7
  legPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace LegPriceFractionPair

def encode (message : LegPriceFractionPair) : List UInt8 :=
  Alpha.encode message.rawLegPrice
    ++ (encodeUInt 1 message.legPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (LegPriceFractionPair × List UInt8) := do
  let (rawLegPrice, bytes) ← Alpha.decode 7 bytes
  let (legPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawLegPrice, legPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : LegPriceFractionPair) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : LegPriceFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LegPriceFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end LegPriceFractionPair

/-- Strategy Instrument Leg: 19 bytes -/
structure StrategyInstrumentLeg where
  legGroupInstrument : Alpha 2
  legInstrument : Alpha 4
  legRatioOrDeltaFractionPair : LegRatioOrDeltaFractionPair
  legPriceFractionPair : LegPriceFractionPair
  deriving DecidableEq, Repr

namespace StrategyInstrumentLeg

def encode (message : StrategyInstrumentLeg) : List UInt8 :=
  Alpha.encode message.legGroupInstrument
    ++ (Alpha.encode message.legInstrument
    ++ (LegRatioOrDeltaFractionPair.encode message.legRatioOrDeltaFractionPair
    ++ (LegPriceFractionPair.encode message.legPriceFractionPair)))

def decode (bytes : List UInt8) : Option (StrategyInstrumentLeg × List UInt8) := do
  let (legGroupInstrument, bytes) ← Alpha.decode 2 bytes
  let (legInstrument, bytes) ← Alpha.decode 4 bytes
  let (legRatioOrDeltaFractionPair, bytes) ← LegRatioOrDeltaFractionPair.decode bytes
  let (legPriceFractionPair, bytes) ← LegPriceFractionPair.decode bytes
  pure ({ legGroupInstrument, legInstrument, legRatioOrDeltaFractionPair, legPriceFractionPair }, bytes)

@[simp] theorem encode_length (message : StrategyInstrumentLeg) : (encode message).length = 19 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, LegRatioOrDeltaFractionPair.encode_length, LegPriceFractionPair.encode_length]

theorem encode_length_pos (message : StrategyInstrumentLeg) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyInstrumentLeg) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LegRatioOrDeltaFractionPair.decode_encode, some_bind]
  dsimp only
  rw [LegPriceFractionPair.decode_encode, some_bind]
  rfl

end StrategyInstrumentLeg

/-- Strategy Instrument Keys Message -/
structure StrategyInstrumentKeysMessage where
  exchangeId : ExchangeId
  strategySymbol : Alpha 30
  expiryYear : Alpha 2
  expiryMonthStrategy : Alpha 1
  expiryDay : Alpha 2
  maximumNumberOfContractsPerOrder : Alpha 6
  minimumNumberOfContractsPerOrder : Alpha 6
  maximumThresholdPriceFractionPair : MaximumThresholdPriceFractionPair
  minimumThresholdPriceStrategyFractionPair : MinimumThresholdPriceStrategyFractionPair
  tickIncrement : TickIncrement
  marketFlowIndicator : Alpha 2
  groupInstrument : Alpha 2
  instrument : Alpha 4
  instrumentExternalCode : Alpha 30
  strategyAllowImplied : StrategyAllowImplied
  strategyCode : Alpha 2
  strategyType : StrategyType
  lastTradingDatetime : Alpha 14
  variableLegsStrategyCode : Alpha 2
  strategyInstrumentLeg : Digited 2 StrategyInstrumentLeg
  deriving DecidableEq, Repr

namespace StrategyInstrumentKeysMessage

def encode (message : StrategyInstrumentKeysMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.strategySymbol
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryMonthStrategy
    ++ (Alpha.encode message.expiryDay
    ++ (Alpha.encode message.maximumNumberOfContractsPerOrder
    ++ (Alpha.encode message.minimumNumberOfContractsPerOrder
    ++ (MaximumThresholdPriceFractionPair.encode message.maximumThresholdPriceFractionPair
    ++ (MinimumThresholdPriceStrategyFractionPair.encode message.minimumThresholdPriceStrategyFractionPair
    ++ (TickIncrement.encode message.tickIncrement
    ++ (Alpha.encode message.marketFlowIndicator
    ++ (Alpha.encode message.groupInstrument
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.instrumentExternalCode
    ++ (StrategyAllowImplied.encode message.strategyAllowImplied
    ++ (Alpha.encode message.strategyCode
    ++ (StrategyType.encode message.strategyType
    ++ (Alpha.encode message.lastTradingDatetime
    ++ (Alpha.encode message.variableLegsStrategyCode
    ++ (encodeDigits 2 message.strategyInstrumentLeg.val.length
    ++ (encodeMany StrategyInstrumentLeg.encode message.strategyInstrumentLeg.val))))))))))))))))))))

def decode (bytes : List UInt8) : Option (StrategyInstrumentKeysMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (strategySymbol, bytes) ← Alpha.decode 30 bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryMonthStrategy, bytes) ← Alpha.decode 1 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (maximumNumberOfContractsPerOrder, bytes) ← Alpha.decode 6 bytes
  let (minimumNumberOfContractsPerOrder, bytes) ← Alpha.decode 6 bytes
  let (maximumThresholdPriceFractionPair, bytes) ← MaximumThresholdPriceFractionPair.decode bytes
  let (minimumThresholdPriceStrategyFractionPair, bytes) ← MinimumThresholdPriceStrategyFractionPair.decode bytes
  let (tickIncrement, bytes) ← TickIncrement.decode bytes
  let (marketFlowIndicator, bytes) ← Alpha.decode 2 bytes
  let (groupInstrument, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (instrumentExternalCode, bytes) ← Alpha.decode 30 bytes
  let (strategyAllowImplied, bytes) ← StrategyAllowImplied.decode bytes
  let (strategyCode, bytes) ← Alpha.decode 2 bytes
  let (strategyType, bytes) ← StrategyType.decode bytes
  let (lastTradingDatetime, bytes) ← Alpha.decode 14 bytes
  let (variableLegsStrategyCode, bytes) ← Alpha.decode 2 bytes
  let (numberOfLegs, bytes) ← decodeDigits 2 bytes
  let (strategyInstrumentLeg_, bytes) ← decodeMany StrategyInstrumentLeg.decode numberOfLegs bytes
  if fits_strategyInstrumentLeg : strategyInstrumentLeg_.length < 10 ^ 2 then
    pure ({ exchangeId, strategySymbol, expiryYear, expiryMonthStrategy, expiryDay, maximumNumberOfContractsPerOrder, minimumNumberOfContractsPerOrder, maximumThresholdPriceFractionPair, minimumThresholdPriceStrategyFractionPair, tickIncrement, marketFlowIndicator, groupInstrument, instrument, instrumentExternalCode, strategyAllowImplied, strategyCode, strategyType, lastTradingDatetime, variableLegsStrategyCode, strategyInstrumentLeg := ⟨strategyInstrumentLeg_, fits_strategyInstrumentLeg⟩ }, bytes)
  else none

theorem encode_length_pos (message : StrategyInstrumentKeysMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [ExchangeId.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : StrategyInstrumentKeysMessage) : (encode message).length ≤ 2013 := by
  have bound_strategyInstrumentLeg := message.strategyInstrumentLeg.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, ExchangeId.encode_length, Alpha.encode_length, MaximumThresholdPriceFractionPair.encode_length, MinimumThresholdPriceStrategyFractionPair.encode_length, TickIncrement.encode_length, StrategyAllowImplied.encode_length, StrategyType.encode_length, encodeDigits_length, encodeMany_length_const StrategyInstrumentLeg.encode 19 StrategyInstrumentLeg.encode_length]
  omega

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
  rw [List.append_assoc, MaximumThresholdPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MinimumThresholdPriceStrategyFractionPair.decode_encode, some_bind]
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
  rw [List.append_assoc, StrategyAllowImplied.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StrategyType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.strategyInstrumentLeg.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany StrategyInstrumentLeg.encode StrategyInstrumentLeg.decode StrategyInstrumentLeg.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.strategyInstrumentLeg.length_lt]
  rfl

end StrategyInstrumentKeysMessage

/-- Initial Order Price Fraction Pair: 8 bytes -/
structure InitialOrderPriceFractionPair where
  rawInitialOrderPrice : Alpha 7
  initialOrderPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace InitialOrderPriceFractionPair

def encode (message : InitialOrderPriceFractionPair) : List UInt8 :=
  Alpha.encode message.rawInitialOrderPrice
    ++ (encodeUInt 1 message.initialOrderPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (InitialOrderPriceFractionPair × List UInt8) := do
  let (rawInitialOrderPrice, bytes) ← Alpha.decode 7 bytes
  let (initialOrderPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawInitialOrderPrice, initialOrderPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : InitialOrderPriceFractionPair) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : InitialOrderPriceFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InitialOrderPriceFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end InitialOrderPriceFractionPair

/-- Option Auction Beginning Message: 83 bytes -/
structure OptionAuctionBeginningMessage where
  exchangeId : ExchangeId
  optionSymbol : OptionSymbol
  auctionId : Alpha 6
  initialOrderSide : InitialOrderSide
  initialOrderQuantity : Alpha 8
  initialOrderPriceFractionPair : InitialOrderPriceFractionPair
  auctionExpiryTimestamp : Alpha 20
  auctionDuration : Alpha 12
  initialQuantityAssured : Alpha 8
  deriving DecidableEq, Repr

namespace OptionAuctionBeginningMessage

def encode (message : OptionAuctionBeginningMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (OptionSymbol.encode message.optionSymbol
    ++ (Alpha.encode message.auctionId
    ++ (InitialOrderSide.encode message.initialOrderSide
    ++ (Alpha.encode message.initialOrderQuantity
    ++ (InitialOrderPriceFractionPair.encode message.initialOrderPriceFractionPair
    ++ (Alpha.encode message.auctionExpiryTimestamp
    ++ (Alpha.encode message.auctionDuration
    ++ (Alpha.encode message.initialQuantityAssured))))))))

def decode (bytes : List UInt8) : Option (OptionAuctionBeginningMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (optionSymbol, bytes) ← OptionSymbol.decode bytes
  let (auctionId, bytes) ← Alpha.decode 6 bytes
  let (initialOrderSide, bytes) ← InitialOrderSide.decode bytes
  let (initialOrderQuantity, bytes) ← Alpha.decode 8 bytes
  let (initialOrderPriceFractionPair, bytes) ← InitialOrderPriceFractionPair.decode bytes
  let (auctionExpiryTimestamp, bytes) ← Alpha.decode 20 bytes
  let (auctionDuration, bytes) ← Alpha.decode 12 bytes
  let (initialQuantityAssured, bytes) ← Alpha.decode 8 bytes
  pure ({ exchangeId, optionSymbol, auctionId, initialOrderSide, initialOrderQuantity, initialOrderPriceFractionPair, auctionExpiryTimestamp, auctionDuration, initialQuantityAssured }, bytes)

@[simp] theorem encode_length (message : OptionAuctionBeginningMessage) : (encode message).length = 83 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, OptionSymbol.encode_length, Alpha.encode_length, InitialOrderSide.encode_length, InitialOrderPriceFractionPair.encode_length]

theorem encode_length_pos (message : OptionAuctionBeginningMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionAuctionBeginningMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InitialOrderSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InitialOrderPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OptionAuctionBeginningMessage

/-- Strategy Auction Beginning Message: 94 bytes -/
structure StrategyAuctionBeginningMessage where
  exchangeId : ExchangeId
  strategySymbol : Alpha 30
  auctionId : Alpha 6
  initialOrderSide : InitialOrderSide
  initialOrderQuantity : Alpha 8
  initialOrderPriceFractionPair : InitialOrderPriceFractionPair
  auctionExpiryTimestamp : Alpha 20
  auctionDuration : Alpha 12
  initialQuantityAssured : Alpha 8
  deriving DecidableEq, Repr

namespace StrategyAuctionBeginningMessage

def encode (message : StrategyAuctionBeginningMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.strategySymbol
    ++ (Alpha.encode message.auctionId
    ++ (InitialOrderSide.encode message.initialOrderSide
    ++ (Alpha.encode message.initialOrderQuantity
    ++ (InitialOrderPriceFractionPair.encode message.initialOrderPriceFractionPair
    ++ (Alpha.encode message.auctionExpiryTimestamp
    ++ (Alpha.encode message.auctionDuration
    ++ (Alpha.encode message.initialQuantityAssured))))))))

def decode (bytes : List UInt8) : Option (StrategyAuctionBeginningMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (strategySymbol, bytes) ← Alpha.decode 30 bytes
  let (auctionId, bytes) ← Alpha.decode 6 bytes
  let (initialOrderSide, bytes) ← InitialOrderSide.decode bytes
  let (initialOrderQuantity, bytes) ← Alpha.decode 8 bytes
  let (initialOrderPriceFractionPair, bytes) ← InitialOrderPriceFractionPair.decode bytes
  let (auctionExpiryTimestamp, bytes) ← Alpha.decode 20 bytes
  let (auctionDuration, bytes) ← Alpha.decode 12 bytes
  let (initialQuantityAssured, bytes) ← Alpha.decode 8 bytes
  pure ({ exchangeId, strategySymbol, auctionId, initialOrderSide, initialOrderQuantity, initialOrderPriceFractionPair, auctionExpiryTimestamp, auctionDuration, initialQuantityAssured }, bytes)

@[simp] theorem encode_length (message : StrategyAuctionBeginningMessage) : (encode message).length = 94 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length, InitialOrderSide.encode_length, InitialOrderPriceFractionPair.encode_length]

theorem encode_length_pos (message : StrategyAuctionBeginningMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyAuctionBeginningMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InitialOrderSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InitialOrderPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StrategyAuctionBeginningMessage

/-- Bid Price Summary Fraction Pair: 8 bytes -/
structure BidPriceSummaryFractionPair where
  rawBidPriceSummary : Alpha 7
  bidPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace BidPriceSummaryFractionPair

def encode (message : BidPriceSummaryFractionPair) : List UInt8 :=
  Alpha.encode message.rawBidPriceSummary
    ++ (encodeUInt 1 message.bidPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (BidPriceSummaryFractionPair × List UInt8) := do
  let (rawBidPriceSummary, bytes) ← Alpha.decode 7 bytes
  let (bidPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawBidPriceSummary, bidPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : BidPriceSummaryFractionPair) : (encode message).length = 8 := by
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

/-- Ask Price Summary Fraction Pair: 8 bytes -/
structure AskPriceSummaryFractionPair where
  rawAskPriceSummary : Alpha 7
  askPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace AskPriceSummaryFractionPair

def encode (message : AskPriceSummaryFractionPair) : List UInt8 :=
  Alpha.encode message.rawAskPriceSummary
    ++ (encodeUInt 1 message.askPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (AskPriceSummaryFractionPair × List UInt8) := do
  let (rawAskPriceSummary, bytes) ← Alpha.decode 7 bytes
  let (askPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawAskPriceSummary, askPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : AskPriceSummaryFractionPair) : (encode message).length = 8 := by
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

/-- Last Price Fraction Pair: 8 bytes -/
structure LastPriceFractionPair where
  rawLastPrice : Alpha 7
  lastPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace LastPriceFractionPair

def encode (message : LastPriceFractionPair) : List UInt8 :=
  Alpha.encode message.rawLastPrice
    ++ (encodeUInt 1 message.lastPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (LastPriceFractionPair × List UInt8) := do
  let (rawLastPrice, bytes) ← Alpha.decode 7 bytes
  let (lastPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawLastPrice, lastPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : LastPriceFractionPair) : (encode message).length = 8 := by
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

/-- Net Change Option Summary Message Fraction Pair: 8 bytes -/
structure NetChangeOptionSummaryMessageFractionPair where
  rawNetChangeOptionSummaryMessage : Alpha 7
  netChangeFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace NetChangeOptionSummaryMessageFractionPair

def encode (message : NetChangeOptionSummaryMessageFractionPair) : List UInt8 :=
  Alpha.encode message.rawNetChangeOptionSummaryMessage
    ++ (encodeUInt 1 message.netChangeFractionIndicator)

def decode (bytes : List UInt8) : Option (NetChangeOptionSummaryMessageFractionPair × List UInt8) := do
  let (rawNetChangeOptionSummaryMessage, bytes) ← Alpha.decode 7 bytes
  let (netChangeFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawNetChangeOptionSummaryMessage, netChangeFractionIndicator }, bytes)

@[simp] theorem encode_length (message : NetChangeOptionSummaryMessageFractionPair) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : NetChangeOptionSummaryMessageFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NetChangeOptionSummaryMessageFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end NetChangeOptionSummaryMessageFractionPair

/-- Open Price Fraction Pair: 8 bytes -/
structure OpenPriceFractionPair where
  rawOpenPrice : Alpha 7
  openPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace OpenPriceFractionPair

def encode (message : OpenPriceFractionPair) : List UInt8 :=
  Alpha.encode message.rawOpenPrice
    ++ (encodeUInt 1 message.openPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (OpenPriceFractionPair × List UInt8) := do
  let (rawOpenPrice, bytes) ← Alpha.decode 7 bytes
  let (openPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawOpenPrice, openPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : OpenPriceFractionPair) : (encode message).length = 8 := by
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

/-- High Price Fraction Pair: 8 bytes -/
structure HighPriceFractionPair where
  rawHighPrice : Alpha 7
  highPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace HighPriceFractionPair

def encode (message : HighPriceFractionPair) : List UInt8 :=
  Alpha.encode message.rawHighPrice
    ++ (encodeUInt 1 message.highPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (HighPriceFractionPair × List UInt8) := do
  let (rawHighPrice, bytes) ← Alpha.decode 7 bytes
  let (highPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawHighPrice, highPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : HighPriceFractionPair) : (encode message).length = 8 := by
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

/-- Low Price Fraction Pair: 8 bytes -/
structure LowPriceFractionPair where
  rawLowPrice : Alpha 7
  lowPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace LowPriceFractionPair

def encode (message : LowPriceFractionPair) : List UInt8 :=
  Alpha.encode message.rawLowPrice
    ++ (encodeUInt 1 message.lowPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (LowPriceFractionPair × List UInt8) := do
  let (rawLowPrice, bytes) ← Alpha.decode 7 bytes
  let (lowPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawLowPrice, lowPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : LowPriceFractionPair) : (encode message).length = 8 := by
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

/-- Closing Price Fraction Pair: 8 bytes -/
structure ClosingPriceFractionPair where
  rawClosingPrice : Alpha 7
  closingPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace ClosingPriceFractionPair

def encode (message : ClosingPriceFractionPair) : List UInt8 :=
  Alpha.encode message.rawClosingPrice
    ++ (encodeUInt 1 message.closingPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (ClosingPriceFractionPair × List UInt8) := do
  let (rawClosingPrice, bytes) ← Alpha.decode 7 bytes
  let (closingPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawClosingPrice, closingPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : ClosingPriceFractionPair) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ClosingPriceFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ClosingPriceFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ClosingPriceFractionPair

/-- Previous Closing Price Fraction Pair: 8 bytes -/
structure PreviousClosingPriceFractionPair where
  rawPreviousClosingPrice : Alpha 7
  previousClosingPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace PreviousClosingPriceFractionPair

def encode (message : PreviousClosingPriceFractionPair) : List UInt8 :=
  Alpha.encode message.rawPreviousClosingPrice
    ++ (encodeUInt 1 message.previousClosingPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (PreviousClosingPriceFractionPair × List UInt8) := do
  let (rawPreviousClosingPrice, bytes) ← Alpha.decode 7 bytes
  let (previousClosingPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawPreviousClosingPrice, previousClosingPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : PreviousClosingPriceFractionPair) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : PreviousClosingPriceFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PreviousClosingPriceFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end PreviousClosingPriceFractionPair

/-- Option Summary Message: 128 bytes -/
structure OptionSummaryMessage where
  exchangeId : ExchangeId
  optionSymbol : OptionSymbol
  bidPriceSummaryFractionPair : BidPriceSummaryFractionPair
  bidSize : Alpha 5
  askPriceSummaryFractionPair : AskPriceSummaryFractionPair
  askSize : Alpha 5
  lastPriceFractionPair : LastPriceFractionPair
  openInterest : Alpha 7
  openInterestDate : Alpha 6
  tick : Tick
  volume : Alpha 8
  netChangeSign : NetChangeSign
  netChangeOptionSummaryMessageFractionPair : NetChangeOptionSummaryMessageFractionPair
  openPriceFractionPair : OpenPriceFractionPair
  highPriceFractionPair : HighPriceFractionPair
  lowPriceFractionPair : LowPriceFractionPair
  optionMarker : Alpha 2
  closingPriceFractionPair : ClosingPriceFractionPair
  previousClosingPriceFractionPair : PreviousClosingPriceFractionPair
  reason : Reason
  deriving DecidableEq, Repr

namespace OptionSummaryMessage

def encode (message : OptionSummaryMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (OptionSymbol.encode message.optionSymbol
    ++ (BidPriceSummaryFractionPair.encode message.bidPriceSummaryFractionPair
    ++ (Alpha.encode message.bidSize
    ++ (AskPriceSummaryFractionPair.encode message.askPriceSummaryFractionPair
    ++ (Alpha.encode message.askSize
    ++ (LastPriceFractionPair.encode message.lastPriceFractionPair
    ++ (Alpha.encode message.openInterest
    ++ (Alpha.encode message.openInterestDate
    ++ (Tick.encode message.tick
    ++ (Alpha.encode message.volume
    ++ (NetChangeSign.encode message.netChangeSign
    ++ (NetChangeOptionSummaryMessageFractionPair.encode message.netChangeOptionSummaryMessageFractionPair
    ++ (OpenPriceFractionPair.encode message.openPriceFractionPair
    ++ (HighPriceFractionPair.encode message.highPriceFractionPair
    ++ (LowPriceFractionPair.encode message.lowPriceFractionPair
    ++ (Alpha.encode message.optionMarker
    ++ (ClosingPriceFractionPair.encode message.closingPriceFractionPair
    ++ (PreviousClosingPriceFractionPair.encode message.previousClosingPriceFractionPair
    ++ (Reason.encode message.reason)))))))))))))))))))

def decode (bytes : List UInt8) : Option (OptionSummaryMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (optionSymbol, bytes) ← OptionSymbol.decode bytes
  let (bidPriceSummaryFractionPair, bytes) ← BidPriceSummaryFractionPair.decode bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPriceSummaryFractionPair, bytes) ← AskPriceSummaryFractionPair.decode bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (lastPriceFractionPair, bytes) ← LastPriceFractionPair.decode bytes
  let (openInterest, bytes) ← Alpha.decode 7 bytes
  let (openInterestDate, bytes) ← Alpha.decode 6 bytes
  let (tick, bytes) ← Tick.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (netChangeSign, bytes) ← NetChangeSign.decode bytes
  let (netChangeOptionSummaryMessageFractionPair, bytes) ← NetChangeOptionSummaryMessageFractionPair.decode bytes
  let (openPriceFractionPair, bytes) ← OpenPriceFractionPair.decode bytes
  let (highPriceFractionPair, bytes) ← HighPriceFractionPair.decode bytes
  let (lowPriceFractionPair, bytes) ← LowPriceFractionPair.decode bytes
  let (optionMarker, bytes) ← Alpha.decode 2 bytes
  let (closingPriceFractionPair, bytes) ← ClosingPriceFractionPair.decode bytes
  let (previousClosingPriceFractionPair, bytes) ← PreviousClosingPriceFractionPair.decode bytes
  let (reason, bytes) ← Reason.decode bytes
  pure ({ exchangeId, optionSymbol, bidPriceSummaryFractionPair, bidSize, askPriceSummaryFractionPair, askSize, lastPriceFractionPair, openInterest, openInterestDate, tick, volume, netChangeSign, netChangeOptionSummaryMessageFractionPair, openPriceFractionPair, highPriceFractionPair, lowPriceFractionPair, optionMarker, closingPriceFractionPair, previousClosingPriceFractionPair, reason }, bytes)

@[simp] theorem encode_length (message : OptionSummaryMessage) : (encode message).length = 128 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, OptionSymbol.encode_length, BidPriceSummaryFractionPair.encode_length, Alpha.encode_length, AskPriceSummaryFractionPair.encode_length, LastPriceFractionPair.encode_length, Tick.encode_length, NetChangeSign.encode_length, NetChangeOptionSummaryMessageFractionPair.encode_length, OpenPriceFractionPair.encode_length, HighPriceFractionPair.encode_length, LowPriceFractionPair.encode_length, ClosingPriceFractionPair.encode_length, PreviousClosingPriceFractionPair.encode_length, Reason.encode_length]

theorem encode_length_pos (message : OptionSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionSummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OptionSymbol.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Tick.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeOptionSummaryMessageFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpenPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, HighPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LowPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ClosingPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PreviousClosingPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [Reason.decode_encode, some_bind]
  rfl

end OptionSummaryMessage

/-- Net Change Future Options Summary Message Fraction Pair: 8 bytes -/
structure NetChangeFutureOptionsSummaryMessageFractionPair where
  rawNetChangeFutureOptionsSummaryMessage : Alpha 7
  netChangeFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace NetChangeFutureOptionsSummaryMessageFractionPair

def encode (message : NetChangeFutureOptionsSummaryMessageFractionPair) : List UInt8 :=
  Alpha.encode message.rawNetChangeFutureOptionsSummaryMessage
    ++ (encodeUInt 1 message.netChangeFractionIndicator)

def decode (bytes : List UInt8) : Option (NetChangeFutureOptionsSummaryMessageFractionPair × List UInt8) := do
  let (rawNetChangeFutureOptionsSummaryMessage, bytes) ← Alpha.decode 7 bytes
  let (netChangeFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawNetChangeFutureOptionsSummaryMessage, netChangeFractionIndicator }, bytes)

@[simp] theorem encode_length (message : NetChangeFutureOptionsSummaryMessageFractionPair) : (encode message).length = 8 := by
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

/-- Opening Price Fraction Pair: 8 bytes -/
structure OpeningPriceFractionPair where
  rawOpeningPrice : Alpha 7
  openingPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace OpeningPriceFractionPair

def encode (message : OpeningPriceFractionPair) : List UInt8 :=
  Alpha.encode message.rawOpeningPrice
    ++ (encodeUInt 1 message.openingPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (OpeningPriceFractionPair × List UInt8) := do
  let (rawOpeningPrice, bytes) ← Alpha.decode 7 bytes
  let (openingPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawOpeningPrice, openingPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : OpeningPriceFractionPair) : (encode message).length = 8 := by
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

/-- Settlement Price Fraction Pair: 8 bytes -/
structure SettlementPriceFractionPair where
  rawSettlementPrice : Alpha 7
  settlementPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace SettlementPriceFractionPair

def encode (message : SettlementPriceFractionPair) : List UInt8 :=
  Alpha.encode message.rawSettlementPrice
    ++ (encodeUInt 1 message.settlementPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (SettlementPriceFractionPair × List UInt8) := do
  let (rawSettlementPrice, bytes) ← Alpha.decode 7 bytes
  let (settlementPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawSettlementPrice, settlementPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : SettlementPriceFractionPair) : (encode message).length = 8 := by
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

/-- Previous Settlement Price Fraction Pair: 8 bytes -/
structure PreviousSettlementPriceFractionPair where
  rawPreviousSettlementPrice : Alpha 7
  previousSettlementPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace PreviousSettlementPriceFractionPair

def encode (message : PreviousSettlementPriceFractionPair) : List UInt8 :=
  Alpha.encode message.rawPreviousSettlementPrice
    ++ (encodeUInt 1 message.previousSettlementPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (PreviousSettlementPriceFractionPair × List UInt8) := do
  let (rawPreviousSettlementPrice, bytes) ← Alpha.decode 7 bytes
  let (previousSettlementPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawPreviousSettlementPrice, previousSettlementPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : PreviousSettlementPriceFractionPair) : (encode message).length = 8 := by
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

/-- Future Options Summary Message: 127 bytes -/
structure FutureOptionsSummaryMessage where
  exchangeId : ExchangeId
  futureOptionSymbol : FutureOptionSymbol
  bidPriceSummaryFractionPair : BidPriceSummaryFractionPair
  bidSize : Alpha 5
  askPriceSummaryFractionPair : AskPriceSummaryFractionPair
  askSize : Alpha 5
  lastPriceFractionPair : LastPriceFractionPair
  openInterest : Alpha 7
  openInterestDate : Alpha 6
  tick : Tick
  volume : Alpha 8
  netChangeSign : NetChangeSign
  netChangeFutureOptionsSummaryMessageFractionPair : NetChangeFutureOptionsSummaryMessageFractionPair
  openingPriceFractionPair : OpeningPriceFractionPair
  highPriceFractionPair : HighPriceFractionPair
  lowPriceFractionPair : LowPriceFractionPair
  settlementPriceFractionPair : SettlementPriceFractionPair
  previousSettlementPriceFractionPair : PreviousSettlementPriceFractionPair
  reason : Reason
  deriving DecidableEq, Repr

namespace FutureOptionsSummaryMessage

def encode (message : FutureOptionsSummaryMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (FutureOptionSymbol.encode message.futureOptionSymbol
    ++ (BidPriceSummaryFractionPair.encode message.bidPriceSummaryFractionPair
    ++ (Alpha.encode message.bidSize
    ++ (AskPriceSummaryFractionPair.encode message.askPriceSummaryFractionPair
    ++ (Alpha.encode message.askSize
    ++ (LastPriceFractionPair.encode message.lastPriceFractionPair
    ++ (Alpha.encode message.openInterest
    ++ (Alpha.encode message.openInterestDate
    ++ (Tick.encode message.tick
    ++ (Alpha.encode message.volume
    ++ (NetChangeSign.encode message.netChangeSign
    ++ (NetChangeFutureOptionsSummaryMessageFractionPair.encode message.netChangeFutureOptionsSummaryMessageFractionPair
    ++ (OpeningPriceFractionPair.encode message.openingPriceFractionPair
    ++ (HighPriceFractionPair.encode message.highPriceFractionPair
    ++ (LowPriceFractionPair.encode message.lowPriceFractionPair
    ++ (SettlementPriceFractionPair.encode message.settlementPriceFractionPair
    ++ (PreviousSettlementPriceFractionPair.encode message.previousSettlementPriceFractionPair
    ++ (Reason.encode message.reason))))))))))))))))))

def decode (bytes : List UInt8) : Option (FutureOptionsSummaryMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (futureOptionSymbol, bytes) ← FutureOptionSymbol.decode bytes
  let (bidPriceSummaryFractionPair, bytes) ← BidPriceSummaryFractionPair.decode bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPriceSummaryFractionPair, bytes) ← AskPriceSummaryFractionPair.decode bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (lastPriceFractionPair, bytes) ← LastPriceFractionPair.decode bytes
  let (openInterest, bytes) ← Alpha.decode 7 bytes
  let (openInterestDate, bytes) ← Alpha.decode 6 bytes
  let (tick, bytes) ← Tick.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (netChangeSign, bytes) ← NetChangeSign.decode bytes
  let (netChangeFutureOptionsSummaryMessageFractionPair, bytes) ← NetChangeFutureOptionsSummaryMessageFractionPair.decode bytes
  let (openingPriceFractionPair, bytes) ← OpeningPriceFractionPair.decode bytes
  let (highPriceFractionPair, bytes) ← HighPriceFractionPair.decode bytes
  let (lowPriceFractionPair, bytes) ← LowPriceFractionPair.decode bytes
  let (settlementPriceFractionPair, bytes) ← SettlementPriceFractionPair.decode bytes
  let (previousSettlementPriceFractionPair, bytes) ← PreviousSettlementPriceFractionPair.decode bytes
  let (reason, bytes) ← Reason.decode bytes
  pure ({ exchangeId, futureOptionSymbol, bidPriceSummaryFractionPair, bidSize, askPriceSummaryFractionPair, askSize, lastPriceFractionPair, openInterest, openInterestDate, tick, volume, netChangeSign, netChangeFutureOptionsSummaryMessageFractionPair, openingPriceFractionPair, highPriceFractionPair, lowPriceFractionPair, settlementPriceFractionPair, previousSettlementPriceFractionPair, reason }, bytes)

@[simp] theorem encode_length (message : FutureOptionsSummaryMessage) : (encode message).length = 127 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, FutureOptionSymbol.encode_length, BidPriceSummaryFractionPair.encode_length, Alpha.encode_length, AskPriceSummaryFractionPair.encode_length, LastPriceFractionPair.encode_length, Tick.encode_length, NetChangeSign.encode_length, NetChangeFutureOptionsSummaryMessageFractionPair.encode_length, OpeningPriceFractionPair.encode_length, HighPriceFractionPair.encode_length, LowPriceFractionPair.encode_length, SettlementPriceFractionPair.encode_length, PreviousSettlementPriceFractionPair.encode_length, Reason.encode_length]

theorem encode_length_pos (message : FutureOptionsSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FutureOptionsSummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureOptionSymbol.decode_encode, some_bind]
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
  rw [List.append_assoc, SettlementPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PreviousSettlementPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [Reason.decode_encode, some_bind]
  rfl

end FutureOptionsSummaryMessage

/-- Net Change Futures Summary Message Fraction Pair: 8 bytes -/
structure NetChangeFuturesSummaryMessageFractionPair where
  rawNetChangeFuturesSummaryMessage : Alpha 7
  netChangeFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace NetChangeFuturesSummaryMessageFractionPair

def encode (message : NetChangeFuturesSummaryMessageFractionPair) : List UInt8 :=
  Alpha.encode message.rawNetChangeFuturesSummaryMessage
    ++ (encodeUInt 1 message.netChangeFractionIndicator)

def decode (bytes : List UInt8) : Option (NetChangeFuturesSummaryMessageFractionPair × List UInt8) := do
  let (rawNetChangeFuturesSummaryMessage, bytes) ← Alpha.decode 7 bytes
  let (netChangeFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawNetChangeFuturesSummaryMessage, netChangeFractionIndicator }, bytes)

@[simp] theorem encode_length (message : NetChangeFuturesSummaryMessageFractionPair) : (encode message).length = 8 := by
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

/-- Previous Settlement Fraction Pair: 8 bytes -/
structure PreviousSettlementFractionPair where
  rawPreviousSettlement : Alpha 7
  previousSettlementFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace PreviousSettlementFractionPair

def encode (message : PreviousSettlementFractionPair) : List UInt8 :=
  Alpha.encode message.rawPreviousSettlement
    ++ (encodeUInt 1 message.previousSettlementFractionIndicator)

def decode (bytes : List UInt8) : Option (PreviousSettlementFractionPair × List UInt8) := do
  let (rawPreviousSettlement, bytes) ← Alpha.decode 7 bytes
  let (previousSettlementFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawPreviousSettlement, previousSettlementFractionIndicator }, bytes)

@[simp] theorem encode_length (message : PreviousSettlementFractionPair) : (encode message).length = 8 := by
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

/-- External Price At Source Fraction Pair: 8 bytes -/
structure ExternalPriceAtSourceFractionPair where
  rawExternalPriceAtSource : Alpha 7
  externalPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace ExternalPriceAtSourceFractionPair

def encode (message : ExternalPriceAtSourceFractionPair) : List UInt8 :=
  Alpha.encode message.rawExternalPriceAtSource
    ++ (encodeUInt 1 message.externalPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (ExternalPriceAtSourceFractionPair × List UInt8) := do
  let (rawExternalPriceAtSource, bytes) ← Alpha.decode 7 bytes
  let (externalPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawExternalPriceAtSource, externalPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : ExternalPriceAtSourceFractionPair) : (encode message).length = 8 := by
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

/-- Futures Summary Message: 125 bytes -/
structure FuturesSummaryMessage where
  exchangeId : ExchangeId
  futureProduct : FutureProduct
  bidPriceSummaryFractionPair : BidPriceSummaryFractionPair
  bidSize : Alpha 5
  askPriceSummaryFractionPair : AskPriceSummaryFractionPair
  askSize : Alpha 5
  lastPriceFractionPair : LastPriceFractionPair
  openPriceFractionPair : OpenPriceFractionPair
  highPriceFractionPair : HighPriceFractionPair
  lowPriceFractionPair : LowPriceFractionPair
  settlementPriceFractionPair : SettlementPriceFractionPair
  netChangeSign : NetChangeSign
  netChangeFuturesSummaryMessageFractionPair : NetChangeFuturesSummaryMessageFractionPair
  volume : Alpha 8
  previousSettlementFractionPair : PreviousSettlementFractionPair
  openInterest : Alpha 7
  openInterestDate : Alpha 6
  reason : Reason
  externalPriceAtSourceFractionPair : ExternalPriceAtSourceFractionPair
  deriving DecidableEq, Repr

namespace FuturesSummaryMessage

def encode (message : FuturesSummaryMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (FutureProduct.encode message.futureProduct
    ++ (BidPriceSummaryFractionPair.encode message.bidPriceSummaryFractionPair
    ++ (Alpha.encode message.bidSize
    ++ (AskPriceSummaryFractionPair.encode message.askPriceSummaryFractionPair
    ++ (Alpha.encode message.askSize
    ++ (LastPriceFractionPair.encode message.lastPriceFractionPair
    ++ (OpenPriceFractionPair.encode message.openPriceFractionPair
    ++ (HighPriceFractionPair.encode message.highPriceFractionPair
    ++ (LowPriceFractionPair.encode message.lowPriceFractionPair
    ++ (SettlementPriceFractionPair.encode message.settlementPriceFractionPair
    ++ (NetChangeSign.encode message.netChangeSign
    ++ (NetChangeFuturesSummaryMessageFractionPair.encode message.netChangeFuturesSummaryMessageFractionPair
    ++ (Alpha.encode message.volume
    ++ (PreviousSettlementFractionPair.encode message.previousSettlementFractionPair
    ++ (Alpha.encode message.openInterest
    ++ (Alpha.encode message.openInterestDate
    ++ (Reason.encode message.reason
    ++ (ExternalPriceAtSourceFractionPair.encode message.externalPriceAtSourceFractionPair))))))))))))))))))

def decode (bytes : List UInt8) : Option (FuturesSummaryMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (futureProduct, bytes) ← FutureProduct.decode bytes
  let (bidPriceSummaryFractionPair, bytes) ← BidPriceSummaryFractionPair.decode bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPriceSummaryFractionPair, bytes) ← AskPriceSummaryFractionPair.decode bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (lastPriceFractionPair, bytes) ← LastPriceFractionPair.decode bytes
  let (openPriceFractionPair, bytes) ← OpenPriceFractionPair.decode bytes
  let (highPriceFractionPair, bytes) ← HighPriceFractionPair.decode bytes
  let (lowPriceFractionPair, bytes) ← LowPriceFractionPair.decode bytes
  let (settlementPriceFractionPair, bytes) ← SettlementPriceFractionPair.decode bytes
  let (netChangeSign, bytes) ← NetChangeSign.decode bytes
  let (netChangeFuturesSummaryMessageFractionPair, bytes) ← NetChangeFuturesSummaryMessageFractionPair.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (previousSettlementFractionPair, bytes) ← PreviousSettlementFractionPair.decode bytes
  let (openInterest, bytes) ← Alpha.decode 7 bytes
  let (openInterestDate, bytes) ← Alpha.decode 6 bytes
  let (reason, bytes) ← Reason.decode bytes
  let (externalPriceAtSourceFractionPair, bytes) ← ExternalPriceAtSourceFractionPair.decode bytes
  pure ({ exchangeId, futureProduct, bidPriceSummaryFractionPair, bidSize, askPriceSummaryFractionPair, askSize, lastPriceFractionPair, openPriceFractionPair, highPriceFractionPair, lowPriceFractionPair, settlementPriceFractionPair, netChangeSign, netChangeFuturesSummaryMessageFractionPair, volume, previousSettlementFractionPair, openInterest, openInterestDate, reason, externalPriceAtSourceFractionPair }, bytes)

@[simp] theorem encode_length (message : FuturesSummaryMessage) : (encode message).length = 125 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, FutureProduct.encode_length, BidPriceSummaryFractionPair.encode_length, Alpha.encode_length, AskPriceSummaryFractionPair.encode_length, LastPriceFractionPair.encode_length, OpenPriceFractionPair.encode_length, HighPriceFractionPair.encode_length, LowPriceFractionPair.encode_length, SettlementPriceFractionPair.encode_length, NetChangeSign.encode_length, NetChangeFuturesSummaryMessageFractionPair.encode_length, PreviousSettlementFractionPair.encode_length, Reason.encode_length, ExternalPriceAtSourceFractionPair.encode_length]

theorem encode_length_pos (message : FuturesSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FuturesSummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureProduct.decode_encode, some_bind]
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
  rw [List.append_assoc, SettlementPriceFractionPair.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Reason.decode_encode, some_bind]
  dsimp only
  rw [ExternalPriceAtSourceFractionPair.decode_encode, some_bind]
  rfl

end FuturesSummaryMessage

/-- Net Change Strategy Summary Message Fraction Pair: 8 bytes -/
structure NetChangeStrategySummaryMessageFractionPair where
  rawNetChangeStrategySummaryMessage : Alpha 7
  netChangeFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace NetChangeStrategySummaryMessageFractionPair

def encode (message : NetChangeStrategySummaryMessageFractionPair) : List UInt8 :=
  Alpha.encode message.rawNetChangeStrategySummaryMessage
    ++ (encodeUInt 1 message.netChangeFractionIndicator)

def decode (bytes : List UInt8) : Option (NetChangeStrategySummaryMessageFractionPair × List UInt8) := do
  let (rawNetChangeStrategySummaryMessage, bytes) ← Alpha.decode 7 bytes
  let (netChangeFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawNetChangeStrategySummaryMessage, netChangeFractionIndicator }, bytes)

@[simp] theorem encode_length (message : NetChangeStrategySummaryMessageFractionPair) : (encode message).length = 8 := by
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

/-- Strategy Summary Message: 113 bytes -/
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
    ++ (Reason.encode message.reason)))))))))))))))))))

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
  pure ({ exchangeId, strategySymbol, bidPriceSign, bidPriceSummaryFractionPair, bidSize, askPriceSign, askPriceSummaryFractionPair, askSize, lastPriceSign, lastPriceFractionPair, openPriceSign, openPriceFractionPair, highPriceSign, highPriceFractionPair, lowPriceSign, lowPriceFractionPair, netChangeSign, netChangeStrategySummaryMessageFractionPair, volume, reason }, bytes)

@[simp] theorem encode_length (message : StrategySummaryMessage) : (encode message).length = 113 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length, BidPriceSign.encode_length, BidPriceSummaryFractionPair.encode_length, AskPriceSign.encode_length, AskPriceSummaryFractionPair.encode_length, LastPriceSign.encode_length, LastPriceFractionPair.encode_length, OpenPriceSign.encode_length, OpenPriceFractionPair.encode_length, HighPriceSign.encode_length, HighPriceFractionPair.encode_length, LowPriceSign.encode_length, LowPriceFractionPair.encode_length, NetChangeSign.encode_length, NetChangeStrategySummaryMessageFractionPair.encode_length, Reason.encode_length]

theorem encode_length_pos (message : StrategySummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

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
  rw [Reason.decode_encode, some_bind]
  rfl

end StrategySummaryMessage

/-- Order Price Fraction Pair: 8 bytes -/
structure OrderPriceFractionPair where
  rawOrderPrice : Alpha 7
  orderPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace OrderPriceFractionPair

def encode (message : OrderPriceFractionPair) : List UInt8 :=
  Alpha.encode message.rawOrderPrice
    ++ (encodeUInt 1 message.orderPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (OrderPriceFractionPair × List UInt8) := do
  let (rawOrderPrice, bytes) ← Alpha.decode 7 bytes
  let (orderPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawOrderPrice, orderPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : OrderPriceFractionPair) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : OrderPriceFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderPriceFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderPriceFractionPair

/-- Option Initial And Improvement Order Message: 60 bytes -/
structure OptionInitialAndImprovementOrderMessage where
  exchangeId : ExchangeId
  optionSymbol : OptionSymbol
  auctionId : Alpha 6
  orderSide : OrderSide
  orderQuantity : Alpha 8
  orderPriceFractionPair : OrderPriceFractionPair
  orderType : OrderType
  orderId : Alpha 8
  previousOrderId : Alpha 8
  deriving DecidableEq, Repr

namespace OptionInitialAndImprovementOrderMessage

def encode (message : OptionInitialAndImprovementOrderMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (OptionSymbol.encode message.optionSymbol
    ++ (Alpha.encode message.auctionId
    ++ (OrderSide.encode message.orderSide
    ++ (Alpha.encode message.orderQuantity
    ++ (OrderPriceFractionPair.encode message.orderPriceFractionPair
    ++ (OrderType.encode message.orderType
    ++ (Alpha.encode message.orderId
    ++ (Alpha.encode message.previousOrderId))))))))

def decode (bytes : List UInt8) : Option (OptionInitialAndImprovementOrderMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (optionSymbol, bytes) ← OptionSymbol.decode bytes
  let (auctionId, bytes) ← Alpha.decode 6 bytes
  let (orderSide, bytes) ← OrderSide.decode bytes
  let (orderQuantity, bytes) ← Alpha.decode 8 bytes
  let (orderPriceFractionPair, bytes) ← OrderPriceFractionPair.decode bytes
  let (orderType, bytes) ← OrderType.decode bytes
  let (orderId, bytes) ← Alpha.decode 8 bytes
  let (previousOrderId, bytes) ← Alpha.decode 8 bytes
  pure ({ exchangeId, optionSymbol, auctionId, orderSide, orderQuantity, orderPriceFractionPair, orderType, orderId, previousOrderId }, bytes)

@[simp] theorem encode_length (message : OptionInitialAndImprovementOrderMessage) : (encode message).length = 60 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, OptionSymbol.encode_length, Alpha.encode_length, OrderSide.encode_length, OrderPriceFractionPair.encode_length, OrderType.encode_length]

theorem encode_length_pos (message : OptionInitialAndImprovementOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionInitialAndImprovementOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OptionInitialAndImprovementOrderMessage

/-- Strategy Initial And Improvement Order Message: 71 bytes -/
structure StrategyInitialAndImprovementOrderMessage where
  exchangeId : ExchangeId
  strategySymbol : Alpha 30
  auctionId : Alpha 6
  orderSide : OrderSide
  orderQuantity : Alpha 8
  orderPriceFractionPair : OrderPriceFractionPair
  orderType : OrderType
  orderId : Alpha 8
  previousOrderId : Alpha 8
  deriving DecidableEq, Repr

namespace StrategyInitialAndImprovementOrderMessage

def encode (message : StrategyInitialAndImprovementOrderMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.strategySymbol
    ++ (Alpha.encode message.auctionId
    ++ (OrderSide.encode message.orderSide
    ++ (Alpha.encode message.orderQuantity
    ++ (OrderPriceFractionPair.encode message.orderPriceFractionPair
    ++ (OrderType.encode message.orderType
    ++ (Alpha.encode message.orderId
    ++ (Alpha.encode message.previousOrderId))))))))

def decode (bytes : List UInt8) : Option (StrategyInitialAndImprovementOrderMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (strategySymbol, bytes) ← Alpha.decode 30 bytes
  let (auctionId, bytes) ← Alpha.decode 6 bytes
  let (orderSide, bytes) ← OrderSide.decode bytes
  let (orderQuantity, bytes) ← Alpha.decode 8 bytes
  let (orderPriceFractionPair, bytes) ← OrderPriceFractionPair.decode bytes
  let (orderType, bytes) ← OrderType.decode bytes
  let (orderId, bytes) ← Alpha.decode 8 bytes
  let (previousOrderId, bytes) ← Alpha.decode 8 bytes
  pure ({ exchangeId, strategySymbol, auctionId, orderSide, orderQuantity, orderPriceFractionPair, orderType, orderId, previousOrderId }, bytes)

@[simp] theorem encode_length (message : StrategyInitialAndImprovementOrderMessage) : (encode message).length = 71 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length, OrderSide.encode_length, OrderPriceFractionPair.encode_length, OrderType.encode_length]

theorem encode_length_pos (message : StrategyInitialAndImprovementOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyInitialAndImprovementOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StrategyInitialAndImprovementOrderMessage

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

/-- Option Auction Ending Message: 26 bytes -/
structure OptionAuctionEndingMessage where
  exchangeId : ExchangeId
  optionSymbol : OptionSymbol
  auctionId : Alpha 6
  deriving DecidableEq, Repr

namespace OptionAuctionEndingMessage

def encode (message : OptionAuctionEndingMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (OptionSymbol.encode message.optionSymbol
    ++ (Alpha.encode message.auctionId))

def decode (bytes : List UInt8) : Option (OptionAuctionEndingMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (optionSymbol, bytes) ← OptionSymbol.decode bytes
  let (auctionId, bytes) ← Alpha.decode 6 bytes
  pure ({ exchangeId, optionSymbol, auctionId }, bytes)

@[simp] theorem encode_length (message : OptionAuctionEndingMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, OptionSymbol.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : OptionAuctionEndingMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionAuctionEndingMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OptionAuctionEndingMessage

/-- Strategy Auction Ending Message: 37 bytes -/
structure StrategyAuctionEndingMessage where
  exchangeId : ExchangeId
  strategySymbol : Alpha 30
  auctionId : Alpha 6
  deriving DecidableEq, Repr

namespace StrategyAuctionEndingMessage

def encode (message : StrategyAuctionEndingMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.strategySymbol
    ++ (Alpha.encode message.auctionId))

def decode (bytes : List UInt8) : Option (StrategyAuctionEndingMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (strategySymbol, bytes) ← Alpha.decode 30 bytes
  let (auctionId, bytes) ← Alpha.decode 6 bytes
  pure ({ exchangeId, strategySymbol, auctionId }, bytes)

@[simp] theorem encode_length (message : StrategyAuctionEndingMessage) : (encode message).length = 37 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : StrategyAuctionEndingMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyAuctionEndingMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StrategyAuctionEndingMessage

/-- Net Change Futures Trade Correction Message Fraction Pair: 8 bytes -/
structure NetChangeFuturesTradeCorrectionMessageFractionPair where
  rawNetChangeFuturesTradeCorrectionMessage : Alpha 7
  netChangeFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace NetChangeFuturesTradeCorrectionMessageFractionPair

def encode (message : NetChangeFuturesTradeCorrectionMessageFractionPair) : List UInt8 :=
  Alpha.encode message.rawNetChangeFuturesTradeCorrectionMessage
    ++ (encodeUInt 1 message.netChangeFractionIndicator)

def decode (bytes : List UInt8) : Option (NetChangeFuturesTradeCorrectionMessageFractionPair × List UInt8) := do
  let (rawNetChangeFuturesTradeCorrectionMessage, bytes) ← Alpha.decode 7 bytes
  let (netChangeFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawNetChangeFuturesTradeCorrectionMessage, netChangeFractionIndicator }, bytes)

@[simp] theorem encode_length (message : NetChangeFuturesTradeCorrectionMessageFractionPair) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : NetChangeFuturesTradeCorrectionMessageFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NetChangeFuturesTradeCorrectionMessageFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end NetChangeFuturesTradeCorrectionMessageFractionPair

/-- Futures Trade Correction Message: 46 bytes -/
structure FuturesTradeCorrectionMessage where
  exchangeId : ExchangeId
  futureProduct : FutureProduct
  volume : Alpha 8
  tradePriceFractionPair : TradePriceFractionPair
  netChangeSign : NetChangeSign
  netChangeFuturesTradeCorrectionMessageFractionPair : NetChangeFuturesTradeCorrectionMessageFractionPair
  priceIndicatorMarker : FuturesTradeMessagePriceIndicatorMarker
  tradeNumber : Alpha 8
  deriving DecidableEq, Repr

namespace FuturesTradeCorrectionMessage

def encode (message : FuturesTradeCorrectionMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (FutureProduct.encode message.futureProduct
    ++ (Alpha.encode message.volume
    ++ (TradePriceFractionPair.encode message.tradePriceFractionPair
    ++ (NetChangeSign.encode message.netChangeSign
    ++ (NetChangeFuturesTradeCorrectionMessageFractionPair.encode message.netChangeFuturesTradeCorrectionMessageFractionPair
    ++ (FuturesTradeMessagePriceIndicatorMarker.encode message.priceIndicatorMarker
    ++ (Alpha.encode message.tradeNumber)))))))

def decode (bytes : List UInt8) : Option (FuturesTradeCorrectionMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (futureProduct, bytes) ← FutureProduct.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePriceFractionPair, bytes) ← TradePriceFractionPair.decode bytes
  let (netChangeSign, bytes) ← NetChangeSign.decode bytes
  let (netChangeFuturesTradeCorrectionMessageFractionPair, bytes) ← NetChangeFuturesTradeCorrectionMessageFractionPair.decode bytes
  let (priceIndicatorMarker, bytes) ← FuturesTradeMessagePriceIndicatorMarker.decode bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ exchangeId, futureProduct, volume, tradePriceFractionPair, netChangeSign, netChangeFuturesTradeCorrectionMessageFractionPair, priceIndicatorMarker, tradeNumber }, bytes)

@[simp] theorem encode_length (message : FuturesTradeCorrectionMessage) : (encode message).length = 46 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, FutureProduct.encode_length, Alpha.encode_length, TradePriceFractionPair.encode_length, NetChangeSign.encode_length, NetChangeFuturesTradeCorrectionMessageFractionPair.encode_length, FuturesTradeMessagePriceIndicatorMarker.encode_length]

theorem encode_length_pos (message : FuturesTradeCorrectionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FuturesTradeCorrectionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureProduct.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradePriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeFuturesTradeCorrectionMessageFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FuturesTradeMessagePriceIndicatorMarker.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FuturesTradeCorrectionMessage

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

/-- Coupon Fraction Pair: 8 bytes -/
structure CouponFractionPair where
  rawCoupon : Alpha 7
  couponFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace CouponFractionPair

def encode (message : CouponFractionPair) : List UInt8 :=
  Alpha.encode message.rawCoupon
    ++ (encodeUInt 1 message.couponFractionIndicator)

def decode (bytes : List UInt8) : Option (CouponFractionPair × List UInt8) := do
  let (rawCoupon, bytes) ← Alpha.decode 7 bytes
  let (couponFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawCoupon, couponFractionIndicator }, bytes)

@[simp] theorem encode_length (message : CouponFractionPair) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CouponFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CouponFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CouponFractionPair

/-- Conversion Factor Fraction Pair: 8 bytes -/
structure ConversionFactorFractionPair where
  rawConversionFactor : Alpha 7
  conversionFactorFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace ConversionFactorFractionPair

def encode (message : ConversionFactorFractionPair) : List UInt8 :=
  Alpha.encode message.rawConversionFactor
    ++ (encodeUInt 1 message.conversionFactorFractionIndicator)

def decode (bytes : List UInt8) : Option (ConversionFactorFractionPair × List UInt8) := do
  let (rawConversionFactor, bytes) ← Alpha.decode 7 bytes
  let (conversionFactorFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawConversionFactor, conversionFactorFractionIndicator }, bytes)

@[simp] theorem encode_length (message : ConversionFactorFractionPair) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ConversionFactorFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ConversionFactorFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ConversionFactorFractionPair

/-- Bond Definition: 32 bytes -/
structure BondDefinition where
  maturityDate : Alpha 8
  couponFractionPair : CouponFractionPair
  outstandingBondValue : Alpha 8
  conversionFactorFractionPair : ConversionFactorFractionPair
  deriving DecidableEq, Repr

namespace BondDefinition

def encode (message : BondDefinition) : List UInt8 :=
  Alpha.encode message.maturityDate
    ++ (CouponFractionPair.encode message.couponFractionPair
    ++ (Alpha.encode message.outstandingBondValue
    ++ (ConversionFactorFractionPair.encode message.conversionFactorFractionPair)))

def decode (bytes : List UInt8) : Option (BondDefinition × List UInt8) := do
  let (maturityDate, bytes) ← Alpha.decode 8 bytes
  let (couponFractionPair, bytes) ← CouponFractionPair.decode bytes
  let (outstandingBondValue, bytes) ← Alpha.decode 8 bytes
  let (conversionFactorFractionPair, bytes) ← ConversionFactorFractionPair.decode bytes
  pure ({ maturityDate, couponFractionPair, outstandingBondValue, conversionFactorFractionPair }, bytes)

@[simp] theorem encode_length (message : BondDefinition) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, CouponFractionPair.encode_length, ConversionFactorFractionPair.encode_length]

theorem encode_length_pos (message : BondDefinition) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BondDefinition) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CouponFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [ConversionFactorFractionPair.decode_encode, some_bind]
  rfl

end BondDefinition

/-- Future Deliverables Message -/
structure FutureDeliverablesMessage where
  exchangeId : ExchangeId
  futureProduct : FutureProduct
  bondDefinition : Digited 2 BondDefinition
  deriving DecidableEq, Repr

namespace FutureDeliverablesMessage

def encode (message : FutureDeliverablesMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (FutureProduct.encode message.futureProduct
    ++ (encodeDigits 2 message.bondDefinition.val.length
    ++ (encodeMany BondDefinition.encode message.bondDefinition.val)))

def decode (bytes : List UInt8) : Option (FutureDeliverablesMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (futureProduct, bytes) ← FutureProduct.decode bytes
  let (numberOfBonds, bytes) ← decodeDigits 2 bytes
  let (bondDefinition_, bytes) ← decodeMany BondDefinition.decode numberOfBonds bytes
  if fits_bondDefinition : bondDefinition_.length < 10 ^ 2 then
    pure ({ exchangeId, futureProduct, bondDefinition := ⟨bondDefinition_, fits_bondDefinition⟩ }, bytes)
  else none

theorem encode_length_pos (message : FutureDeliverablesMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [ExchangeId.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : FutureDeliverablesMessage) : (encode message).length ≤ 3182 := by
  have bound_bondDefinition := message.bondDefinition.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, ExchangeId.encode_length, FutureProduct.encode_length, encodeDigits_length, encodeMany_length_const BondDefinition.encode 32 BondDefinition.encode_length]
  omega

@[simp] theorem decode_encode (message : FutureDeliverablesMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureProduct.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.bondDefinition.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany BondDefinition.encode BondDefinition.decode BondDefinition.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.bondDefinition.length_lt]
  rfl

end FutureDeliverablesMessage

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

/-- Min Price Fraction Pair: 8 bytes -/
structure MinPriceFractionPair where
  rawMinPrice : Alpha 7
  minPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace MinPriceFractionPair

def encode (message : MinPriceFractionPair) : List UInt8 :=
  Alpha.encode message.rawMinPrice
    ++ (encodeUInt 1 message.minPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (MinPriceFractionPair × List UInt8) := do
  let (rawMinPrice, bytes) ← Alpha.decode 7 bytes
  let (minPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawMinPrice, minPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : MinPriceFractionPair) : (encode message).length = 8 := by
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

/-- Tick Price Fraction Pair: 8 bytes -/
structure TickPriceFractionPair where
  rawTickPrice : Alpha 7
  tickPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace TickPriceFractionPair

def encode (message : TickPriceFractionPair) : List UInt8 :=
  Alpha.encode message.rawTickPrice
    ++ (encodeUInt 1 message.tickPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (TickPriceFractionPair × List UInt8) := do
  let (rawTickPrice, bytes) ← Alpha.decode 7 bytes
  let (tickPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawTickPrice, tickPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : TickPriceFractionPair) : (encode message).length = 8 := by
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

/-- Tick Entry: 16 bytes -/
structure TickEntry where
  minPriceFractionPair : MinPriceFractionPair
  tickPriceFractionPair : TickPriceFractionPair
  deriving DecidableEq, Repr

namespace TickEntry

def encode (message : TickEntry) : List UInt8 :=
  MinPriceFractionPair.encode message.minPriceFractionPair
    ++ (TickPriceFractionPair.encode message.tickPriceFractionPair)

def decode (bytes : List UInt8) : Option (TickEntry × List UInt8) := do
  let (minPriceFractionPair, bytes) ← MinPriceFractionPair.decode bytes
  let (tickPriceFractionPair, bytes) ← TickPriceFractionPair.decode bytes
  pure ({ minPriceFractionPair, tickPriceFractionPair }, bytes)

@[simp] theorem encode_length (message : TickEntry) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, MinPriceFractionPair.encode_length, TickPriceFractionPair.encode_length]

theorem encode_length_pos (message : TickEntry) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TickEntry) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, MinPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [TickPriceFractionPair.decode_encode, some_bind]
  rfl

end TickEntry

/-- Tick Table Message -/
structure TickTableMessage where
  exchangeId : ExchangeId
  tickTableName : Alpha 50
  tickTableShortName : Alpha 2
  tickEntry : Digited 2 TickEntry
  deriving DecidableEq, Repr

namespace TickTableMessage

def encode (message : TickTableMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.tickTableName
    ++ (Alpha.encode message.tickTableShortName
    ++ (encodeDigits 2 message.tickEntry.val.length
    ++ (encodeMany TickEntry.encode message.tickEntry.val))))

def decode (bytes : List UInt8) : Option (TickTableMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (tickTableName, bytes) ← Alpha.decode 50 bytes
  let (tickTableShortName, bytes) ← Alpha.decode 2 bytes
  let (numberOfEntries, bytes) ← decodeDigits 2 bytes
  let (tickEntry_, bytes) ← decodeMany TickEntry.decode numberOfEntries bytes
  if fits_tickEntry : tickEntry_.length < 10 ^ 2 then
    pure ({ exchangeId, tickTableName, tickTableShortName, tickEntry := ⟨tickEntry_, fits_tickEntry⟩ }, bytes)
  else none

theorem encode_length_pos (message : TickTableMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [ExchangeId.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TickTableMessage) : (encode message).length ≤ 1639 := by
  have bound_tickEntry := message.tickEntry.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, ExchangeId.encode_length, Alpha.encode_length, encodeDigits_length, encodeMany_length_const TickEntry.encode 16 TickEntry.encode_length]
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
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.tickEntry.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany TickEntry.encode TickEntry.decode TickEntry.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.tickEntry.length_lt]
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

/-- Start Of Day Message: 9 bytes -/
structure StartOfDayMessage where
  exchangeId : ExchangeId
  businessDate : Alpha 8
  deriving DecidableEq, Repr

namespace StartOfDayMessage

def encode (message : StartOfDayMessage) : List UInt8 :=
  ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.businessDate)

def decode (bytes : List UInt8) : Option (StartOfDayMessage × List UInt8) := do
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (businessDate, bytes) ← Alpha.decode 8 bytes
  pure ({ exchangeId, businessDate }, bytes)

@[simp] theorem encode_length (message : StartOfDayMessage) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, ExchangeId.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : StartOfDayMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StartOfDayMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StartOfDayMessage

/-- Any Message Body, selected by Message Type -/
inductive MessageBody where
  | optionTradeMessage (message : OptionTradeMessage) -- "C " 0x4320
  | futureOptionsTradeMessage (message : FutureOptionsTradeMessage) -- "CB" 0x4342
  | futuresTradeMessage (message : FuturesTradeMessage) -- "CF" 0x4346
  | strategyTradeMessage (message : StrategyTradeMessage) -- "CS" 0x4353
  | optionRequestForQuoteMessage (message : OptionRequestForQuoteMessage) -- "D " 0x4420
  | futureOptionsRequestForQuoteMessage (message : FutureOptionsRequestForQuoteMessage) -- "DB" 0x4442
  | futureRequestForQuoteMessage (message : FutureRequestForQuoteMessage) -- "DF" 0x4446
  | strategyRequestForQuoteMessage (message : StrategyRequestForQuoteMessage) -- "DS" 0x4453
  | instrumentScheduleNoticeOptionMessage (message : InstrumentScheduleNoticeOptionMessage) -- "E " 0x4520
  | instrumentScheduleNoticeFuturesOptionMessage (message : InstrumentScheduleNoticeFuturesOptionMessage) -- "EB" 0x4542
  | instrumentScheduleNoticeFutureMessage (message : InstrumentScheduleNoticeFutureMessage) -- "EF" 0x4546
  | instrumentScheduleNoticeStrategyMessage (message : InstrumentScheduleNoticeStrategyMessage) -- "ES" 0x4553
  | optionQuoteMessage (message : OptionQuoteMessage) -- "F " 0x4620
  | futureOptionsQuoteMessage (message : FutureOptionsQuoteMessage) -- "FB" 0x4642
  | futuresQuoteMessage (message : FuturesQuoteMessage) -- "FF" 0x4646
  | strategyQuoteMessage (message : StrategyQuoteMessage) -- "FS" 0x4653
  | optionMarketDepthMessage (message : OptionMarketDepthMessage) -- "H " 0x4820
  | futureOptionsMarketDepthMessage (message : FutureOptionsMarketDepthMessage) -- "HB" 0x4842
  | futuresMarketDepthMessage (message : FuturesMarketDepthMessage) -- "HF" 0x4846
  | strategyMarketDepthMessage (message : StrategyMarketDepthMessage) -- "HS" 0x4853
  | optionTradeCancellationMessage (message : OptionTradeCancellationMessage) -- "I " 0x4920
  | futureOptionsTradeCancellationMessage (message : FutureOptionsTradeCancellationMessage) -- "IB" 0x4942
  | futureTradeCancellationMessage (message : FutureTradeCancellationMessage) -- "IF" 0x4946
  | strategyTradeCancellationMessage (message : StrategyTradeCancellationMessage) -- "IS" 0x4953
  | optionInstrumentKeysMessage (message : OptionInstrumentKeysMessage) -- "J " 0x4A20
  | futureOptionsInstrumentKeysMessage (message : FutureOptionsInstrumentKeysMessage) -- "JB" 0x4A42
  | underlyingInstrumentKeysMessage (message : UnderlyingInstrumentKeysMessage) -- "JE" 0x4A45
  | futuresInstrumentKeysMessage (message : FuturesInstrumentKeysMessage) -- "JF" 0x4A46
  | strategyInstrumentKeysMessage (message : StrategyInstrumentKeysMessage) -- "JS" 0x4A53
  | optionAuctionBeginningMessage (message : OptionAuctionBeginningMessage) -- "M " 0x4D20
  | strategyAuctionBeginningMessage (message : StrategyAuctionBeginningMessage) -- "MS" 0x4D53
  | optionSummaryMessage (message : OptionSummaryMessage) -- "N " 0x4E20
  | futureOptionsSummaryMessage (message : FutureOptionsSummaryMessage) -- "NB" 0x4E42
  | futuresSummaryMessage (message : FuturesSummaryMessage) -- "NF" 0x4E46
  | strategySummaryMessage (message : StrategySummaryMessage) -- "NS" 0x4E53
  | optionInitialAndImprovementOrderMessage (message : OptionInitialAndImprovementOrderMessage) -- "O " 0x4F20
  | strategyInitialAndImprovementOrderMessage (message : StrategyInitialAndImprovementOrderMessage) -- "OS" 0x4F53
  | beginningOfOptionsSummaryMessage (message : BeginningOfOptionsSummaryMessage) -- "Q " 0x5120
  | beginningOfFutureOptionsSummaryMessage (message : BeginningOfFutureOptionsSummaryMessage) -- "QB" 0x5142
  | beginningOfFuturesSummaryMessage (message : BeginningOfFuturesSummaryMessage) -- "QF" 0x5146
  | beginningOfStrategySummaryMessage (message : BeginningOfStrategySummaryMessage) -- "QS" 0x5153
  | optionAuctionEndingMessage (message : OptionAuctionEndingMessage) -- "T " 0x5420
  | strategyAuctionEndingMessage (message : StrategyAuctionEndingMessage) -- "TS" 0x5453
  | futuresTradeCorrectionMessage (message : FuturesTradeCorrectionMessage) -- "XF" 0x5846
  | groupStatusMessage (message : GroupStatusMessage) -- "GR" 0x4752
  | groupStatusStrategiesMessage (message : GroupStatusStrategiesMessage) -- "GS" 0x4753
  | futureDeliverablesMessage (message : FutureDeliverablesMessage) -- "KF" 0x4B46
  | bulletinsMessage (message : BulletinsMessage) -- "L " 0x4C20
  | endOfSalesMessage (message : EndOfSalesMessage) -- "S " 0x5320
  | tickTableMessage (message : TickTableMessage) -- "TT" 0x5454
  | endOfTransmissionMessage (message : EndOfTransmissionMessage) -- "U " 0x5520
  | circuitAssuranceMessage (message : CircuitAssuranceMessage) -- "V " 0x5620
  | startOfDayMessage (message : StartOfDayMessage) -- "SD" 0x5344
  deriving DecidableEq, Repr

namespace MessageBody

/-- The Message Type each message is sent under -/
def tag : MessageBody → BitVec 16
  | .optionTradeMessage _ => 17184
  | .futureOptionsTradeMessage _ => 17218
  | .futuresTradeMessage _ => 17222
  | .strategyTradeMessage _ => 17235
  | .optionRequestForQuoteMessage _ => 17440
  | .futureOptionsRequestForQuoteMessage _ => 17474
  | .futureRequestForQuoteMessage _ => 17478
  | .strategyRequestForQuoteMessage _ => 17491
  | .instrumentScheduleNoticeOptionMessage _ => 17696
  | .instrumentScheduleNoticeFuturesOptionMessage _ => 17730
  | .instrumentScheduleNoticeFutureMessage _ => 17734
  | .instrumentScheduleNoticeStrategyMessage _ => 17747
  | .optionQuoteMessage _ => 17952
  | .futureOptionsQuoteMessage _ => 17986
  | .futuresQuoteMessage _ => 17990
  | .strategyQuoteMessage _ => 18003
  | .optionMarketDepthMessage _ => 18464
  | .futureOptionsMarketDepthMessage _ => 18498
  | .futuresMarketDepthMessage _ => 18502
  | .strategyMarketDepthMessage _ => 18515
  | .optionTradeCancellationMessage _ => 18720
  | .futureOptionsTradeCancellationMessage _ => 18754
  | .futureTradeCancellationMessage _ => 18758
  | .strategyTradeCancellationMessage _ => 18771
  | .optionInstrumentKeysMessage _ => 18976
  | .futureOptionsInstrumentKeysMessage _ => 19010
  | .underlyingInstrumentKeysMessage _ => 19013
  | .futuresInstrumentKeysMessage _ => 19014
  | .strategyInstrumentKeysMessage _ => 19027
  | .optionAuctionBeginningMessage _ => 19744
  | .strategyAuctionBeginningMessage _ => 19795
  | .optionSummaryMessage _ => 20000
  | .futureOptionsSummaryMessage _ => 20034
  | .futuresSummaryMessage _ => 20038
  | .strategySummaryMessage _ => 20051
  | .optionInitialAndImprovementOrderMessage _ => 20256
  | .strategyInitialAndImprovementOrderMessage _ => 20307
  | .beginningOfOptionsSummaryMessage _ => 20768
  | .beginningOfFutureOptionsSummaryMessage _ => 20802
  | .beginningOfFuturesSummaryMessage _ => 20806
  | .beginningOfStrategySummaryMessage _ => 20819
  | .optionAuctionEndingMessage _ => 21536
  | .strategyAuctionEndingMessage _ => 21587
  | .futuresTradeCorrectionMessage _ => 22598
  | .groupStatusMessage _ => 18258
  | .groupStatusStrategiesMessage _ => 18259
  | .futureDeliverablesMessage _ => 19270
  | .bulletinsMessage _ => 19488
  | .endOfSalesMessage _ => 21280
  | .tickTableMessage _ => 21588
  | .endOfTransmissionMessage _ => 21792
  | .circuitAssuranceMessage _ => 22048
  | .startOfDayMessage _ => 21316

def encode : MessageBody → List UInt8
  | .optionTradeMessage message => OptionTradeMessage.encode message
  | .futureOptionsTradeMessage message => FutureOptionsTradeMessage.encode message
  | .futuresTradeMessage message => FuturesTradeMessage.encode message
  | .strategyTradeMessage message => StrategyTradeMessage.encode message
  | .optionRequestForQuoteMessage message => OptionRequestForQuoteMessage.encode message
  | .futureOptionsRequestForQuoteMessage message => FutureOptionsRequestForQuoteMessage.encode message
  | .futureRequestForQuoteMessage message => FutureRequestForQuoteMessage.encode message
  | .strategyRequestForQuoteMessage message => StrategyRequestForQuoteMessage.encode message
  | .instrumentScheduleNoticeOptionMessage message => InstrumentScheduleNoticeOptionMessage.encode message
  | .instrumentScheduleNoticeFuturesOptionMessage message => InstrumentScheduleNoticeFuturesOptionMessage.encode message
  | .instrumentScheduleNoticeFutureMessage message => InstrumentScheduleNoticeFutureMessage.encode message
  | .instrumentScheduleNoticeStrategyMessage message => InstrumentScheduleNoticeStrategyMessage.encode message
  | .optionQuoteMessage message => OptionQuoteMessage.encode message
  | .futureOptionsQuoteMessage message => FutureOptionsQuoteMessage.encode message
  | .futuresQuoteMessage message => FuturesQuoteMessage.encode message
  | .strategyQuoteMessage message => StrategyQuoteMessage.encode message
  | .optionMarketDepthMessage message => OptionMarketDepthMessage.encode message
  | .futureOptionsMarketDepthMessage message => FutureOptionsMarketDepthMessage.encode message
  | .futuresMarketDepthMessage message => FuturesMarketDepthMessage.encode message
  | .strategyMarketDepthMessage message => StrategyMarketDepthMessage.encode message
  | .optionTradeCancellationMessage message => OptionTradeCancellationMessage.encode message
  | .futureOptionsTradeCancellationMessage message => FutureOptionsTradeCancellationMessage.encode message
  | .futureTradeCancellationMessage message => FutureTradeCancellationMessage.encode message
  | .strategyTradeCancellationMessage message => StrategyTradeCancellationMessage.encode message
  | .optionInstrumentKeysMessage message => OptionInstrumentKeysMessage.encode message
  | .futureOptionsInstrumentKeysMessage message => FutureOptionsInstrumentKeysMessage.encode message
  | .underlyingInstrumentKeysMessage message => UnderlyingInstrumentKeysMessage.encode message
  | .futuresInstrumentKeysMessage message => FuturesInstrumentKeysMessage.encode message
  | .strategyInstrumentKeysMessage message => StrategyInstrumentKeysMessage.encode message
  | .optionAuctionBeginningMessage message => OptionAuctionBeginningMessage.encode message
  | .strategyAuctionBeginningMessage message => StrategyAuctionBeginningMessage.encode message
  | .optionSummaryMessage message => OptionSummaryMessage.encode message
  | .futureOptionsSummaryMessage message => FutureOptionsSummaryMessage.encode message
  | .futuresSummaryMessage message => FuturesSummaryMessage.encode message
  | .strategySummaryMessage message => StrategySummaryMessage.encode message
  | .optionInitialAndImprovementOrderMessage message => OptionInitialAndImprovementOrderMessage.encode message
  | .strategyInitialAndImprovementOrderMessage message => StrategyInitialAndImprovementOrderMessage.encode message
  | .beginningOfOptionsSummaryMessage message => BeginningOfOptionsSummaryMessage.encode message
  | .beginningOfFutureOptionsSummaryMessage message => BeginningOfFutureOptionsSummaryMessage.encode message
  | .beginningOfFuturesSummaryMessage message => BeginningOfFuturesSummaryMessage.encode message
  | .beginningOfStrategySummaryMessage message => BeginningOfStrategySummaryMessage.encode message
  | .optionAuctionEndingMessage message => OptionAuctionEndingMessage.encode message
  | .strategyAuctionEndingMessage message => StrategyAuctionEndingMessage.encode message
  | .futuresTradeCorrectionMessage message => FuturesTradeCorrectionMessage.encode message
  | .groupStatusMessage message => GroupStatusMessage.encode message
  | .groupStatusStrategiesMessage message => GroupStatusStrategiesMessage.encode message
  | .futureDeliverablesMessage message => FutureDeliverablesMessage.encode message
  | .bulletinsMessage message => BulletinsMessage.encode message
  | .endOfSalesMessage message => EndOfSalesMessage.encode message
  | .tickTableMessage message => TickTableMessage.encode message
  | .endOfTransmissionMessage message => EndOfTransmissionMessage.encode message
  | .circuitAssuranceMessage message => CircuitAssuranceMessage.encode message
  | .startOfDayMessage message => StartOfDayMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : MessageBody) : (encode message).length ≤ 3182 := by
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
  | optionRequestForQuoteMessage inner =>
    simp only [encode, OptionRequestForQuoteMessage.encode_length]
    omega
  | futureOptionsRequestForQuoteMessage inner =>
    simp only [encode, FutureOptionsRequestForQuoteMessage.encode_length]
    omega
  | futureRequestForQuoteMessage inner =>
    simp only [encode, FutureRequestForQuoteMessage.encode_length]
    omega
  | strategyRequestForQuoteMessage inner =>
    simp only [encode, StrategyRequestForQuoteMessage.encode_length]
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
  | optionTradeCancellationMessage inner =>
    simp only [encode, OptionTradeCancellationMessage.encode_length]
    omega
  | futureOptionsTradeCancellationMessage inner =>
    simp only [encode, FutureOptionsTradeCancellationMessage.encode_length]
    omega
  | futureTradeCancellationMessage inner =>
    simp only [encode, FutureTradeCancellationMessage.encode_length]
    omega
  | strategyTradeCancellationMessage inner =>
    simp only [encode, StrategyTradeCancellationMessage.encode_length]
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
    have bound_inner := StrategyInstrumentKeysMessage.encode_length_le inner
    simp only [encode]
    omega
  | optionAuctionBeginningMessage inner =>
    simp only [encode, OptionAuctionBeginningMessage.encode_length]
    omega
  | strategyAuctionBeginningMessage inner =>
    simp only [encode, StrategyAuctionBeginningMessage.encode_length]
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
    simp only [encode, StrategySummaryMessage.encode_length]
    omega
  | optionInitialAndImprovementOrderMessage inner =>
    simp only [encode, OptionInitialAndImprovementOrderMessage.encode_length]
    omega
  | strategyInitialAndImprovementOrderMessage inner =>
    simp only [encode, StrategyInitialAndImprovementOrderMessage.encode_length]
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
  | optionAuctionEndingMessage inner =>
    simp only [encode, OptionAuctionEndingMessage.encode_length]
    omega
  | strategyAuctionEndingMessage inner =>
    simp only [encode, StrategyAuctionEndingMessage.encode_length]
    omega
  | futuresTradeCorrectionMessage inner =>
    simp only [encode, FuturesTradeCorrectionMessage.encode_length]
    omega
  | groupStatusMessage inner =>
    simp only [encode, GroupStatusMessage.encode_length]
    omega
  | groupStatusStrategiesMessage inner =>
    simp only [encode, GroupStatusStrategiesMessage.encode_length]
    omega
  | futureDeliverablesMessage inner =>
    have bound_inner := FutureDeliverablesMessage.encode_length_le inner
    simp only [encode]
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
  | startOfDayMessage inner =>
    simp only [encode, StartOfDayMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (MessageBody × List UInt8) :=
  if tag = 17184 then (OptionTradeMessage.decode bytes).map fun (message, rest) => (.optionTradeMessage message, rest)
  else if tag = 17218 then (FutureOptionsTradeMessage.decode bytes).map fun (message, rest) => (.futureOptionsTradeMessage message, rest)
  else if tag = 17222 then (FuturesTradeMessage.decode bytes).map fun (message, rest) => (.futuresTradeMessage message, rest)
  else if tag = 17235 then (StrategyTradeMessage.decode bytes).map fun (message, rest) => (.strategyTradeMessage message, rest)
  else if tag = 17440 then (OptionRequestForQuoteMessage.decode bytes).map fun (message, rest) => (.optionRequestForQuoteMessage message, rest)
  else if tag = 17474 then (FutureOptionsRequestForQuoteMessage.decode bytes).map fun (message, rest) => (.futureOptionsRequestForQuoteMessage message, rest)
  else if tag = 17478 then (FutureRequestForQuoteMessage.decode bytes).map fun (message, rest) => (.futureRequestForQuoteMessage message, rest)
  else if tag = 17491 then (StrategyRequestForQuoteMessage.decode bytes).map fun (message, rest) => (.strategyRequestForQuoteMessage message, rest)
  else if tag = 17696 then (InstrumentScheduleNoticeOptionMessage.decode bytes).map fun (message, rest) => (.instrumentScheduleNoticeOptionMessage message, rest)
  else if tag = 17730 then (InstrumentScheduleNoticeFuturesOptionMessage.decode bytes).map fun (message, rest) => (.instrumentScheduleNoticeFuturesOptionMessage message, rest)
  else if tag = 17734 then (InstrumentScheduleNoticeFutureMessage.decode bytes).map fun (message, rest) => (.instrumentScheduleNoticeFutureMessage message, rest)
  else if tag = 17747 then (InstrumentScheduleNoticeStrategyMessage.decode bytes).map fun (message, rest) => (.instrumentScheduleNoticeStrategyMessage message, rest)
  else if tag = 17952 then (OptionQuoteMessage.decode bytes).map fun (message, rest) => (.optionQuoteMessage message, rest)
  else if tag = 17986 then (FutureOptionsQuoteMessage.decode bytes).map fun (message, rest) => (.futureOptionsQuoteMessage message, rest)
  else if tag = 17990 then (FuturesQuoteMessage.decode bytes).map fun (message, rest) => (.futuresQuoteMessage message, rest)
  else if tag = 18003 then (StrategyQuoteMessage.decode bytes).map fun (message, rest) => (.strategyQuoteMessage message, rest)
  else if tag = 18464 then (OptionMarketDepthMessage.decode bytes).map fun (message, rest) => (.optionMarketDepthMessage message, rest)
  else if tag = 18498 then (FutureOptionsMarketDepthMessage.decode bytes).map fun (message, rest) => (.futureOptionsMarketDepthMessage message, rest)
  else if tag = 18502 then (FuturesMarketDepthMessage.decode bytes).map fun (message, rest) => (.futuresMarketDepthMessage message, rest)
  else if tag = 18515 then (StrategyMarketDepthMessage.decode bytes).map fun (message, rest) => (.strategyMarketDepthMessage message, rest)
  else if tag = 18720 then (OptionTradeCancellationMessage.decode bytes).map fun (message, rest) => (.optionTradeCancellationMessage message, rest)
  else if tag = 18754 then (FutureOptionsTradeCancellationMessage.decode bytes).map fun (message, rest) => (.futureOptionsTradeCancellationMessage message, rest)
  else if tag = 18758 then (FutureTradeCancellationMessage.decode bytes).map fun (message, rest) => (.futureTradeCancellationMessage message, rest)
  else if tag = 18771 then (StrategyTradeCancellationMessage.decode bytes).map fun (message, rest) => (.strategyTradeCancellationMessage message, rest)
  else if tag = 18976 then (OptionInstrumentKeysMessage.decode bytes).map fun (message, rest) => (.optionInstrumentKeysMessage message, rest)
  else if tag = 19010 then (FutureOptionsInstrumentKeysMessage.decode bytes).map fun (message, rest) => (.futureOptionsInstrumentKeysMessage message, rest)
  else if tag = 19013 then (UnderlyingInstrumentKeysMessage.decode bytes).map fun (message, rest) => (.underlyingInstrumentKeysMessage message, rest)
  else if tag = 19014 then (FuturesInstrumentKeysMessage.decode bytes).map fun (message, rest) => (.futuresInstrumentKeysMessage message, rest)
  else if tag = 19027 then (StrategyInstrumentKeysMessage.decode bytes).map fun (message, rest) => (.strategyInstrumentKeysMessage message, rest)
  else if tag = 19744 then (OptionAuctionBeginningMessage.decode bytes).map fun (message, rest) => (.optionAuctionBeginningMessage message, rest)
  else if tag = 19795 then (StrategyAuctionBeginningMessage.decode bytes).map fun (message, rest) => (.strategyAuctionBeginningMessage message, rest)
  else if tag = 20000 then (OptionSummaryMessage.decode bytes).map fun (message, rest) => (.optionSummaryMessage message, rest)
  else if tag = 20034 then (FutureOptionsSummaryMessage.decode bytes).map fun (message, rest) => (.futureOptionsSummaryMessage message, rest)
  else if tag = 20038 then (FuturesSummaryMessage.decode bytes).map fun (message, rest) => (.futuresSummaryMessage message, rest)
  else if tag = 20051 then (StrategySummaryMessage.decode bytes).map fun (message, rest) => (.strategySummaryMessage message, rest)
  else if tag = 20256 then (OptionInitialAndImprovementOrderMessage.decode bytes).map fun (message, rest) => (.optionInitialAndImprovementOrderMessage message, rest)
  else if tag = 20307 then (StrategyInitialAndImprovementOrderMessage.decode bytes).map fun (message, rest) => (.strategyInitialAndImprovementOrderMessage message, rest)
  else if tag = 20768 then (BeginningOfOptionsSummaryMessage.decode bytes).map fun (message, rest) => (.beginningOfOptionsSummaryMessage message, rest)
  else if tag = 20802 then (BeginningOfFutureOptionsSummaryMessage.decode bytes).map fun (message, rest) => (.beginningOfFutureOptionsSummaryMessage message, rest)
  else if tag = 20806 then (BeginningOfFuturesSummaryMessage.decode bytes).map fun (message, rest) => (.beginningOfFuturesSummaryMessage message, rest)
  else if tag = 20819 then (BeginningOfStrategySummaryMessage.decode bytes).map fun (message, rest) => (.beginningOfStrategySummaryMessage message, rest)
  else if tag = 21536 then (OptionAuctionEndingMessage.decode bytes).map fun (message, rest) => (.optionAuctionEndingMessage message, rest)
  else if tag = 21587 then (StrategyAuctionEndingMessage.decode bytes).map fun (message, rest) => (.strategyAuctionEndingMessage message, rest)
  else if tag = 22598 then (FuturesTradeCorrectionMessage.decode bytes).map fun (message, rest) => (.futuresTradeCorrectionMessage message, rest)
  else if tag = 18258 then (GroupStatusMessage.decode bytes).map fun (message, rest) => (.groupStatusMessage message, rest)
  else if tag = 18259 then (GroupStatusStrategiesMessage.decode bytes).map fun (message, rest) => (.groupStatusStrategiesMessage message, rest)
  else if tag = 19270 then (FutureDeliverablesMessage.decode bytes).map fun (message, rest) => (.futureDeliverablesMessage message, rest)
  else if tag = 19488 then (BulletinsMessage.decode bytes).map fun (message, rest) => (.bulletinsMessage message, rest)
  else if tag = 21280 then (EndOfSalesMessage.decode bytes).map fun (message, rest) => (.endOfSalesMessage message, rest)
  else if tag = 21588 then (TickTableMessage.decode bytes).map fun (message, rest) => (.tickTableMessage message, rest)
  else if tag = 21792 then (EndOfTransmissionMessage.decode bytes).map fun (message, rest) => (.endOfTransmissionMessage message, rest)
  else if tag = 22048 then (CircuitAssuranceMessage.decode bytes).map fun (message, rest) => (.circuitAssuranceMessage message, rest)
  else if tag = 21316 then (StartOfDayMessage.decode bytes).map fun (message, rest) => (.startOfDayMessage message, rest)
  else none

@[simp] theorem decode_encode (message : MessageBody) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end MessageBody

/-- Sola Frame -/
structure SolaFrame where
  solaMessageStart : BitVec 8
  sequenceNumber : Alpha 10
  messageTimestamp : Alpha 20
  messageBody : MessageBody
  solaMessageEnd : BitVec 8
  deriving DecidableEq, Repr

namespace SolaFrame

def encode (message : SolaFrame) : List UInt8 :=
  encodeUInt 1 message.solaMessageStart
    ++ (Alpha.encode message.sequenceNumber
    ++ (encodeUInt 2 (MessageBody.tag message.messageBody)
    ++ (Alpha.encode message.messageTimestamp
    ++ (MessageBody.encode message.messageBody
    ++ (encodeUInt 1 message.solaMessageEnd)))))

def decode (bytes : List UInt8) : Option (SolaFrame × List UInt8) := do
  let (solaMessageStart, bytes) ← decodeUInt 1 bytes
  let (sequenceNumber, bytes) ← Alpha.decode 10 bytes
  let (messageType, bytes) ← decodeUInt 2 bytes
  let (messageTimestamp, bytes) ← Alpha.decode 20 bytes
  let (messageBody, bytes) ← MessageBody.decode messageType bytes
  let (solaMessageEnd, bytes) ← decodeUInt 1 bytes
  pure ({ solaMessageStart, sequenceNumber, messageTimestamp, messageBody, solaMessageEnd }, bytes)

theorem encode_length_pos (message : SolaFrame) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SolaFrame) : (encode message).length ≤ 3216 := by
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
  | optionRequestForQuoteMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OptionRequestForQuoteMessage.encode_length]
    omega
  | futureOptionsRequestForQuoteMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FutureOptionsRequestForQuoteMessage.encode_length]
    omega
  | futureRequestForQuoteMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FutureRequestForQuoteMessage.encode_length]
    omega
  | strategyRequestForQuoteMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, StrategyRequestForQuoteMessage.encode_length]
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
  | optionTradeCancellationMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OptionTradeCancellationMessage.encode_length]
    omega
  | futureOptionsTradeCancellationMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FutureOptionsTradeCancellationMessage.encode_length]
    omega
  | futureTradeCancellationMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FutureTradeCancellationMessage.encode_length]
    omega
  | strategyTradeCancellationMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, StrategyTradeCancellationMessage.encode_length]
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
    have bound_inner := StrategyInstrumentKeysMessage.encode_length_le inner
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
    omega
  | optionAuctionBeginningMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OptionAuctionBeginningMessage.encode_length]
    omega
  | strategyAuctionBeginningMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, StrategyAuctionBeginningMessage.encode_length]
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
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, StrategySummaryMessage.encode_length]
    omega
  | optionInitialAndImprovementOrderMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OptionInitialAndImprovementOrderMessage.encode_length]
    omega
  | strategyInitialAndImprovementOrderMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, StrategyInitialAndImprovementOrderMessage.encode_length]
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
  | optionAuctionEndingMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OptionAuctionEndingMessage.encode_length]
    omega
  | strategyAuctionEndingMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, StrategyAuctionEndingMessage.encode_length]
    omega
  | futuresTradeCorrectionMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FuturesTradeCorrectionMessage.encode_length]
    omega
  | groupStatusMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, GroupStatusMessage.encode_length]
    omega
  | groupStatusStrategiesMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, GroupStatusStrategiesMessage.encode_length]
    omega
  | futureDeliverablesMessage inner =>
    have bound_inner := FutureDeliverablesMessage.encode_length_le inner
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
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
  | startOfDayMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, StartOfDayMessage.encode_length]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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

end Omi.TmxMxSolamulticastHsvfV1141
