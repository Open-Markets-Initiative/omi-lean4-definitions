import nyse.nationalequities.integratedfeedstocksummary.NationalEquities_IntegratedFeedStockSummary_v2_5_g

/-!
# New York Stock Exchange Integrated Feed Stock Summary tests

Payloads captured in omi-data-packets, decoded by the generated definition: udp datagrams as they
are, tcp segments reassembled into the stream each side sent. Each must decode and leave nothing
behind, which `decide` checks at build time.
-/

namespace Omi.NyseNationalequitiesIntegratedfeedstocksummaryPillarV25G.Tests

/-- Nyse/NationalEquities.IntegratedFeedStockSummary.Pillar.v2.5.g/StockSummaryMessage.pcap: 52 bytes -/
def captureStocksummarymessage : List UInt8 :=
  [0x34, 0x00, 0x0b, 0x01, 0x3b, 0x4c, 0x03, 0x00, 0x88, 0x84, 0x16, 0x62, 0x00, 0xca, 0x83, 0x11, 0x24, 0x00, 0xdf, 0x00, 0xf5, 0x6b, 0x16, 0x62, 0x00, 0xf5, 0xa5, 0x0d, 0xbf, 0xe7, 0x00, 0x00, 0xa0, 0xe4, 0x98, 0x00, 0x80, 0x96, 0x98, 0x00, 0xa0, 0xe4, 0x98, 0x00, 0x00, 0x00, 0x00, 0x00, 0x84, 0x03, 0x00, 0x00]

example : (decodeAll Omi.NyseNationalequitiesIntegratedfeedstocksummaryPillarV25G.Packet.decode captureStocksummarymessage.length captureStocksummarymessage).isSome = true := by
  decide +kernel

end Omi.NyseNationalequitiesIntegratedfeedstocksummaryPillarV25G.Tests
