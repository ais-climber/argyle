<TeXmacs|2.1.1>

<style|<tuple|poster|a1-poster|reduced-margins|rough-paper|topless-poster-title>>

<\body>
  <\hide-preamble>
    \;

    <assign|par-width|auto>

    <assign|poster-title|<\macro|body|ldeco|rdeco>
      <\no-margins>
        <\with|par-columns|1|deco-hook|<macro|body|<with|ornament-border|0em|ornament-hpadding|<value|title-hpadding>|ornament-vpadding|<value|title-vpadding>|<arg|body>>>>
          <\surround||<vspace|<value|title-vsep>>>
            <\title-block>
              <\surround|<resize|<arg|ldeco>|||1l|><htab|5mm>|<htab|5mm><resize|<arg|rdeco>|1r|||>>
                <arg|body>
              </surround>
            </title-block>
          </surround>
        </with>
      </no-margins>
    </macro>>

    <assign|title-ver-padding|4spc>

    <assign|infix-iff|<macro|<math-imply|<text|
    <localize|<space|1em>iff<space|1em>> >>>>

    \;

    <assign|garnet|<macro|body|<with|color|#990002|<arg|body>>>>

    <assign|myblue|<macro|body|<with|color|#0749ac|<arg|body>>>>

    <assign|key|<macro|body|<myblue|<strong|<arg|body>>>>>

    <assign|Model|<with|font|cal|M>>

    <assign|Net|<with|font|cal|N>>

    <assign|Set|<with|font-family|ss|Set>>

    <assign|Primes|<with|font-family|ss|P>>

    <assign|semantics|<macro|body|<around*|\<llbracket\>|<arg|body>|\<rrbracket\>>>>

    <assign|Lang|<with|font|cal|L>>

    <assign|Logic|<with|font-series|bold|<text|L>>>

    <assign|vocab|<with|font|cal|V>>

    <assign|wocab|<with|font|cal|W>>

    <assign|proves|\<vdash\>>

    <assign|orr|\<vee\>>

    <assign|land|\<wedge\>>

    <assign|NP|<with|font-shape|small-caps|NP>>

    <assign|axiom|<macro|body|<with|font-shape|small-caps|<arg|body>>>>

    <assign|bigchi|<larger|\<chi\>>>

    <assign|powerset|<with|font|cal|P>>

    \;

    <assign|hash|<with|font-family|ss|hash>>

    <assign|unique|<with|font-family|ss|unique>>

    <assign|Know|<with|font-series|bold|<text|K>>>

    <assign|Knownby|<with|font-series|bold|<text|K><rsup|\<downarrow\>>>>

    <assign|diaKnow|\<langle\><value|Know>\<rangle\>>

    <assign|diaKnownby|\<langle\><value|Knownby>\<rangle\>>

    <assign|Typ|<with|font-series|bold|<text|T>>>

    <assign|diaTyp|\<langle\><value|Typ>\<rangle\>>

    <assign|Reach|<with|font-family|ss|Reach>>

    <assign|Reachedby|<with|font-family|ss|Reach><rsup|\<downarrow\>>>

    <assign|Prop|<with|font-family|ss|Prop>>

    <assign|Hebb|<with|font-family|ss|Update>>

    <assign|Activ|<with|font-family|ss|Act>>

    <assign|Inc|<with|font-family|ss|Inc>>

    <assign|AllNets|<with|font-family|ss|Net>>

    <assign|AllModels|<with|font-family|ss|Model>>

    <assign|axiom|<macro|x|<text|<name|(<arg|x>)>>>>

    <assign|precede|<with|font-family|ss|prec>>
  </hide-preamble>

  <center|<tabular|<tformat|<cwith|1|3|2|2|cell-halign|c>|<cwith|1|1|1|1|cell-row-span|3>|<cwith|1|1|1|1|cell-col-span|1>|<cwith|1|1|1|1|cell-valign|c>|<twith|table-width|1par>|<twith|table-hmode|exact>|<cwith|1|1|1|1|cell-rsep|0em>|<cwith|1|1|1|1|cell-bsep|0em>|<cwith|1|1|1|1|cell-tsep|0em>|<cwith|1|1|1|1|cell-halign|l>|<cwith|1|1|1|1|cell-hpart|0em>|<cwith|1|1|1|1|cell-width|0em>|<cwith|1|1|1|1|cell-hmode|exact>|<cwith|1|1|1|1|cell-lsep|0.5em>|<cwith|1|1|3|3|cell-row-span|3>|<cwith|1|1|3|3|cell-col-span|1>|<twith|table-lsep|0.75em>|<twith|table-rsep|0.75em>|<twith|table-bsep|0.75em>|<twith|table-tsep|1em>|<table|<row|<cell|<image|<tuple|<#FFD8FFE000104A46494600010101006000600000FFE1004045786966000049492A0008000000010069870400010000001A00000000000000020002A0090001000000ED00000003A00900010000001301000000000000FFDB0043000302020302020303030304030304050805050404050A070706080C0A0C0C0B0A0B0B0D0E12100D0E110E0B0B1016101113141515150C0F171816141812141514FFDB00430103040405040509050509140D0B0D1414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414FFC0001108011300ED03012200021101031101FFC4001F0000010501010101010100000000000000000102030405060708090A0BFFC400B5100002010303020403050504040000017D01020300041105122131410613516107227114328191A1082342B1C11552D1F02433627282090A161718191A25262728292A3435363738393A434445464748494A535455565758595A636465666768696A737475767778797A838485868788898A92939495969798999AA2A3A4A5A6A7A8A9AAB2B3B4B5B6B7B8B9BAC2C3C4C5C6C7C8C9CAD2D3D4D5D6D7D8D9DAE1E2E3E4E5E6E7E8E9EAF1F2F3F4F5F6F7F8F9FAFFC4001F0100030101010101010101010000000000000102030405060708090A0BFFC400B51100020102040403040705040400010277000102031104052131061241510761711322328108144291A1B1C109233352F0156272D10A162434E125F11718191A262728292A35363738393A434445464748494A535455565758595A636465666768696A737475767778797A82838485868788898A92939495969798999AA2A3A4A5A6A7A8A9AAB2B3B4B5B6B7B8B9BAC2C3C4C5C6C7C8C9CAD2D3D4D5D6D7D8D9DAE2E3E4E5E6E7E8E9EAF2F3F4F5F6F7F8F9FAFFDA000C03010002110311003F00F8928A28AFCE8FECD0A28A2800A28A2800A28A2800A28A2800A28A2800A28A2800A28A2800A28A2800A28A2800A28A2800A28A2800A28A2800A28A2800A28A2800A28A2800A28A2800A28A2800A28A2800A28A2800A28A2800A28A2800A28A2800A28A2800A28A2800A28A2800A28A2800A28A2800A28A2800A28A2800A28A2800A28A2800A28A2800A28A2800A28A2800A28AFD49FF008254E93637FF0002BC5125CD9DBDC38F11CAA1A5895881F65B7E32457561A87D62A7B3BD8F073BCD564D8378B70E6B34AD7B6FE7667E5B515FD0E7FC237A47FD02ECBFF01D3FC28FF846F48FFA05D97FE03A7F857AFF00D90FF9FF000FF827E73FF11163FF0040AFFF0003FF00ED4FE78E8AFE873FE11BD23FE81765FF0080E9FE147FC237A47FD02ECBFF0001D3FC28FEC87FCFF87FC11FFC4458FF00D02BFF00C0FF00FB53F9E3A2BFA1CFF846F48FFA05D97FE03A7F851FF08DE91FF40BB2FF00C074FF000A3FB21FF3FE1FF045FF0011163FF40AFF00F03FFED4FE78E8AF48FDA522483F688F89D1C68B1C69E26D49551460002E64C002BCDEBC0947964E3D8FD76855F6D4A156D6E649FDEAE14514549B851451400514514005145140051451400514514005145140051451400514514005145140057E94FF00C132FE2C7823C05F05BC4763E26F19787FC397B2F88249A3B6D5B5482D6478CDB5B80E164604AE5586471907D2BF35A8AE9C3D7787A9ED12B9E267395C338C23C254938A6D3BAF23F7CF47F8F1F0D3C43AA5B69BA57C44F0A6A7A8DD388A0B3B3D6EDA59A673D15115C963EC057755F865FB207FC9CF7C34FF00B0D41FCEBF73ABEB3058978A839356B33F9F389723A7916221469CDC9495F5F5B0514515E81F2065789BC57A2782F4A7D53C41AC69FA16991B2A3DE6A77496F0AB138505DC80093C0E79AE37FE1A47E127FD152F05FF00E14369FF00C72BC83FE0A57FF26A7ADFFD842CBFF470AFC77AF1B198F961AA7228DF43F4AE1CE14A39DE0DE26A55716A4D5925D12FF33D07F686D4ECF5AF8F5F11F50D3EEE0BFB0BBF116A13DBDD5AC8248A68DAE1CABA3292194820820E0835E7D4515F2B297349CBB9FBED1A4A8D28D25F6525F7051451526C14514500145145001451450014514500145145001451450015FB0DE1EFF8277FC0ABFD034CBA9FC2972D34F6D148EC356BB196280938F33D4D7E3CD7F431E12FF915746FFAF287FF00458AF772BA50A8E7CF14F6DFE67E55C778EC560A187786AB285DCAFCADABFC3D8F9F3FE1DC9F017FE852BAFF00C1BDDFFF001CA3FE1DC9F017FE852BAFFC1BDDFF00F1CAFA62815EF7D5687F22FB91F91FF6EE6BFF0041553FF0397F99F33FFC3B93E02FFD0A575FF837BBFF00E3947FC3B93E02FF00D0A575FF00837BBFFE395F4CD2138A3EAB43F917DC83FB7735FF00A0AA9FF81CBFCCF99FFE1DC9F017FE852BAFFC1BDDFF00F1CAF817FE0A01F04FC21F023E2EE89A178334E934CD32E7428AF658A4B99272D2B5C4E85B748C48F963518E9C57EC957E547FC1583FE4E03C35FF0062C41FFA57755E6E614294283942293BAE87DB707E698EC566B1A788AF2947965A3936BEE6CF09FD8FFF00E4E7BE1A7FD86A0FE75FB9D5F863FB207FC9CF7C34FF00B0D41FCEBF73A9653FC297A95E217FBF51FF0007EAC28A28AF74FCACF967FE0A57FF0026A7ADFF00D842CBFF00470AFC77AFD88FF8295FFC9A9EB7FF00610B2FFD1C2BF1DEBE4B35FE3AF4FF0033FA1380BFE4552FF1BFCA27EB37C1CFD817E0A78BBE11781F5DD53C31713EA7A9E87637B752AEA97481E592DD1DD82890019662703815D7FF00C3B93E02FF00D0A575FF00837BBFFE395EAFFB3B7FC9BFFC32FF00B1634CFF00D248EBD0735F414F0D41C13705B7647E438BCEF348E22A463899A4A4FED4BBFA9F33FF00C3B93E02FF00D0A575FF00837BBFFE3947FC3B93E02FFD0A575FF837BBFF00E395F4C52D5FD5687F22FB91CBFDBB9AFF00D054FF00F0397F99F337FC3B93E02FFD0A575FF837BBFF00E3947FC3B93E02FF00D0A575FF00837BBFFE395F4C1A051F55A1FC8BEE41FDBB9AFF00D0554FFC0E5FE67E46FF00C1437F67DF03FC02D7FC176BE09D2A4D2E1D4ADAE64B9592EE59F7B23C614E64638E18F4AF912BF407FE0AE5FF002357C37FFAF2BDFF00D19157E7F57C9636318622518AB2FF00807F4470BD7AB89CA2855AD272934EEDBBBF89F50A28A2B84FA90A28A2800A28A2800A28A2800AF4387F68BF8AF6F124517C4FF194712285444F105D85503A003CCE0579E5154A528FC2EC6352852AD6F69152B77499FA93FF0004BAF889E2BF883A0FC4293C53E26D67C4925ADCD92C0DABDFCB74620CB36E086463B73819C75C0AFB96BF3E7FE0917FF22EFC4BFF00AFAB0FFD027AFD06AFB4C036F0D06FFAD4FE65E2C8469E755E30565EEE8BFC310A43DA9693D2BBCF923F12BE33FED05F14B4AF8C3E3AB2B2F895E2FB3B3B6D7AFE182DE0D76E9238916E1C2A2A8930AA000001C002BC8BC59E37F11F8F7508AFFC4DAFEA9E22BE8A2104773AB5EC9752A46096081A46242E598E3A649F5ADEF8EDFF0025BFE21FFD8C5A8FFE94C95C357C0559C9C9A6FA9FD7581C351A7469CE1049F2AD5257D8F60FD903FE4E7BE1A7FD86A0FE75FB9D5F863FB207FC9CF7C34FFB0D41FCEBF73ABE8B29FE14BD4FC6BC42FF007EA3FE0FD58514515EE9F951F2CFFC14AFFE4D4F5BFF00B08597FE8E15F8EF5FB11FF052BFF9353D6FFEC2165FFA3857E3BD7C966BFC75E9FE67F42700FF00C8AA5FE37F944EFB4EFDA03E2868FA7DAD8587C48F175958DAC4B05BDB5B6BB751C50C6A02AA22890055000000E0015FA63FF04CBF1C788FC7BF057C497DE27F106A9E23BD8BC412431DCEAD7B25D48918B6B7210348C485CB31C74C93EB5F9215FAA9FF00049EFF00920DE29FFB1965FF00D25B6A32D9C9E2126FA32F8D70D429E5139C2093E68EA92BEE7DB5451457D69FCF015F845AC7ED1BF1662D5AF513E2878CD116770AABE20BB000DC781FBCAFDDDAFE77B5BFF90D5FFF00D7C49FFA11AF9FCDA528A872BB6FFA1FAF787D42956962BDAC54ADC9BA4FF98D4F177C43F157C4096DA5F14789B58F124B6CACB03EAF7F2DD1881C160A6463B41C0CE3AE0573D4515F36DB6EECFDB2108D38A8C1597905145148B0A28A2800A28A2800A28A2800A28A2803F4A3FE0917FF0022EFC4BFFAFAB0FF00D027AFD06AFCF9FF008245FF00C8BBF12FFEBEAC3FF409EBF41ABED72FFF007687CFF367F31717FF00C8F311FF006EFF00E9310A4F4A5A4F4AF40F8F3F02FE3B7FC96FF887FF006316A3FF00A532570D5DCFC76FF92DFF0010FF00EC62D47FF4A64AE1ABF3DA9F1BF53FB0F09FEEF4FF00C2BF23D83F640FF939EF869FF61A83F9D7EE757E18FEC81FF273DF0D3FEC3507F3AFDCEAFA5CA7F852F53F11F10BFDFA8FF83F561451457BA7E547CB3FF052BFF9353D6FFEC2165FFA3857E3BD7EC47FC14AFF00E4D4F5BFFB08597FE8E15F8EF5F259AFF1D7A7F99FD09C03FF0022A97F8DFE510AFD54FF00824F7FC906F14FFD8CB2FF00E92DB57E55D7EAA7FC127BFE48378A7FEC6597FF00496DAA32CFF785E8CEBE38FF009134FF00C51FCCFB6A8A28AFB03F9C02BF9DED6FFE4357FF00F5F127FE846BFA21AFE77B5BFF0090D5FF00FD7C49FF00A11AF9DCDF687CFF0043F64F0EBE2C57FDB9FF00B714A8A28AF9C3F690A28A2800A28A2800A28A2800A28A2800A28A2803F4A3FE0917FF0022EFC4BFFAFAB0FF00D027AFD06AFCF9FF008245FF00C8BBF12FFEBEAC3FF409EBF41ABED72FFF007687CFF367F31717FF00C8F311FF006EFF00E9310A4F4A5A4F4AF40F8F3F02FE3B7FC96FF887FF006316A3FF00A532570D5DCFC76FF92DFF0010FF00EC62D47FF4A64AE1ABF3DA9F1BF53FB0F09FEEF4FF00C2BF23D83F640FF939EF869FF61A83F9D7EE757E18FEC81FF273DF0D3FEC3507F3AFDCEAFA5CA7F852F53F11F10BFDFA8FF83F561451457BA7E547CB3FF052BFF9353D6FFEC2165FFA3857E3BD7EC47FC14AFF00E4D4F5BFFB08597FE8E15F8EF5F259AFF1D7A7F99FD09C03FF0022A97F8DFE510AFD54FF00824F7FC906F14FFD8CB2FF00E92DB57E55D7EAA7FC127BFE48378A7FEC6597FF00496DAA32CFF785E8CEBE38FF009134FF00C51FCCFB6A8A28AFB03F9C02BF9DED6FFE4357FF00F5F127FE846BFA21AFE77B5BFF0090D5FF00FD7C49FF00A11AF9DCDF687CFF0043F64F0EBE2C57FDB9FF00B714A8A28AF9C3F690A28A2800A28A2800A28A2800A28A2800A28A2803F4A3FE0917FF0022EFC4BFFAFAB0FF00D027AFD06AFCF9FF008245FF00C8BBF12FFEBEAC3FF409EBF41ABED72FFF007687CFF367F31717FF00C8F311FF006EFF00E9310A4F4A5A4F4AF40F8F3F02FE3B7FC96FF887FF006316A3FF00A532570D5DCFC76FF92DFF0010FF00EC62D47FF4A64AE1ABF3DA9F1BF53FB0F09FEEF4FF00C2BF23D83F640FF939EF869FF61A83F9D7EE757E18FEC81FF273DF0D3FEC3507F3AFDCEAFA5CA7F852F53F11F10BFDFA8FF83F561451457BA7E547CB3FF052BFF9353D6FFEC2165FFA3857E3BD7EC47FC14AFF00E4D4F5BFFB08597FE8E15F8EF5F259AFF1D7A7F99FD09C03FF0022A97F8DFE510AFD54FF00824F7FC906F14FFD8CB2FF00E92DB57E55D7EAA7FC127BFE48378A7FEC6597FF00496DAA32CFF785E8CEBE38FF009134FF00C51FCCFB6A8A28AFB03F9C02BF9DED6FFE4357FF00F5F127FE846BFA21AFE77B5BFF0090D5FF00FD7C49FF00A11AF9DCDF687CFF0043F64F0EBE2C57FDB9FF00B714A8A28AF9C3F690A28A2800A28A2800A28A2800A28A2800A28A2803F4A3FE0917FF0022EFC4BFFAFAB0FF00D027AFD06AFCF9FF008245FF00C8BBF12FFEBEAC3FF409EBF41ABED72FFF007687CFF367F31717FF00C8F311FF006EFF00E9310A4F4A5A4F4AF40F8F3F02FE3B7FC96FF887FF006316A3FF00A532570D5DCFC76FF92DFF0010FF00EC62D47FF4A64AE1ABF3DA9F1BF53FB0F09FEEF4FF00C2BF23D83F640FF939EF869FF61A83F9D7EE757E18FEC81FF273DF0D3FEC3507F3AFDCEAFA5CA7F852F53F11F10BFDFA8FF83F561451457BA7E547CB3FF052BFF9353D6FFEC2165FFA3857E3BD7EC47FC14AFF00E4D4F5BFFB08597FE8E15F8EF5F259AFF1D7A7F99FD09C03FF0022A97F8DFE510AFD54FF00824F7FC906F14FFD8CB2FF00E92DB57E55D7EAA7FC127BFE48378A7FEC6597FF00496DAA32CFF785E8CEBE38FF009134FF00C51FCCFB6A8A28AFB03F9C02BF9DED6FFE4357FF00F5F127FE846BFA21AFE77B5BFF0090D5FF00FD7C49FF00A11AF9DCDF687CFF0043F64F0EBE2C57FDB9FF00B714A8A28AF9C3F690A28A2800A28A2800A28A2800A28A2800A28A2803F4A3FE0917FF0022EFC4BFFAFAB0FF00D027AFD06AFCF9FF0082461FF8A7BE258FFA7AB0FF00D027AFD051CD7DAE5FFEED0F9FE67F31717FFC8F311FF6EFFE9311690D2D15E81F1E7CA5E28FF826C7C25F17F89B57D76FAE7C46B7BAA5E4D7B3886FE3541248E5DB68311C0CB1C0CD667FC3AD7E0DFF00CFD789FF00F06117FF0019AFB028AE4784A0F57047D0C78873682518E26565E67CC1F0FBFE09DFF0B3E19F8DB45F14E9171E216D4F49B95BAB71737D1BC65D7A6E022048FC457D3C2968ADA9D28525682B1E662F1D8AC7C94F1551CDAD15FB0514515A9C270BF19FE0F683F1D7C0973E12F123DE2695712C7339B194472EE46DCB862AC3191E95F3CFFC3ADBE0D9FF0097AF13FF00E0C23FFE335F60515CF530F4AABE69C5367AF84CDF1F81A7ECB0D5A508DEF64FA9F1FF00FC3AD7E0DFFCFD789FFF0006117FF19AF75F80DFB3F7863F674F0B5F787FC2B25FC961797AD7D21D466595FCC28887055570311AF18F5AF4BA28861E9537CD08A4CAC5673986369FB1C45694A3D9B0A28A2BA0F182BF9DED6FFE4357FF00F5F127FE846BFA20AFE77F5BFF0090CDFF00FD7C49FF00A11AF9DCDF687CFF0043F64F0EBE2C57FDB9FF00B714A8A28AF9C3F690A28A2800A28A2800A28A2800A28A2800A28A2803D1BE03FC77F137ECF7E3BB7F12F86E707A477BA7CA4F917B0E726371FA86EAA791DC1FDA4F817F1CFC33FB407812D7C4DE1AB9CAB623BBB1908F3ECA6C65A2907AFA1E8C30457E0AD7A5FC01F8FBE26FD9DFC770788FC3B379913622BFD3656220BD873928E3B1EEAC3953ED907D4C1635E1DF2CBE17F81F09C4DC354F39A7EDA8E95A3B3FE65D9FE8FA7A1FBC4296BCFF00E08FC6DF0CFC7BF025A789FC3375E6432612E6D2423CEB39B00B4520EC46783D08C11906BBF15F5F1929A528BD0FE73AD46A61EA4A9558DA4B469F4168A28AA310A28A2800A28A2800A28A2800A28A2800A4A2BF3CFF006F1FDBABEC0351F86BF0E75022EFE6B7D6B5EB67FF0055D9ADE061FC5D9DC74FBA39C91CF5EBC30F0E799EC6559562337C4AC3E1D7ABE89777FD6A56FDBCBF6EADBFDA3F0D3E1CEA07765ADF5AD7AD5FA766B68187E4EE3DD47735F9CF4515F155EBCF113E799FD3794E5387C9F0CB0F875EAFAB7DDFF9740A28A2B9CF6828A28A0028A28A0028A28A0028A28A0028A28A0028A28A00F43F827F1EBC65FB3FF89A5D6BC1FA82DACD711186E6D6E13CCB7B84EDBD33C953C83C11CF38241F74FF00879FFC69FEF787BFF05A7FF8BAF9228AE88622AD35CB09348F231593E5F8CA9ED71142329776B53EB7FF00879FFC69FEF787BFF05A7FF8BA3FE1E7FF001A7FBDE1EFFC169FFE2EBE48A2AFEB788FE76727FABB94FF00D0343EE47DEFFB3FFF00C1427E2BFC49F8D5E0DF0BEB0DA27F65EABA8C56B71E4581493631E76B6F3835FA6C2BF0CBF640FF00939EF869FF0061A83F9D7EE757D1659567569C9CDDF53F1BE37C0E1B018CA50C2D3504E377656D6EC28A28AF60FCE0F0FF00DB27E2FEBFF037E066A5E2CF0C9B51AADBDD5B429F6C8BCD8F6BC815B2B91DBDEBF3E3FE1E7FF1A7FBDE1EFF00C169FF00E2EBED1FF8295FFC9A9EB7FF00610B2FFD1C2BF1DEBE6731AF5695651849A563F6EE0CCA7018ECB6557134633973B576AFA591F5BFFC3CFF00E34FF7BC3DFF0082D3FF00C5D1FF000F3FF8D3FDEF0F7FE0B4FF00F175F24515E5FD6F11FCECFBDFF57729FF00A0687DC8FA7BC63FF0518F8CDE33F0CEA1A24BA969BA5C37D11864BAD32CCC370A87EF047DC7692323239E4E083CD7CC47AF3D6928AC6A559D5779BB9E9E130185C045C70B4D413DECAD70A28A2B23BC28A28A0028A28A0028A28A0028A28A0028A28A0028A28A0028A28A0028A28A0028A2BF4F7FE095FE19D1F5BF82DE2A9B51D26C6FE55F103A2C9756C92305FB340700B03C726BAB0D43EB153D9A763C2CEF3559360DE2DC39ACD2B5EDBFDE7C45FB207FC9CF7C34FF00B0D41FCEBF734563DA782FC3D61731DC5B685A65BCF19DC92C5671AB29F5040C835B35F5983C2BC2C5C5BBDCFE7BE23CF239ED78568D3E4E556DEFD6FD90514515DE7C99F2CFFC14AFFE4D4F5BFF00AFFB2FFD1C2BF1DEBFA25D434CB3D5ED8DB5F5A417B6EC4130DC462442474E08C564FF00C201E17FFA16F48FFC018BFF0089AF1F1780789A9CEA56D3B1FA370FF164324C23C2CA8B9DE4DDEF6DD25D9F63F9F0A2BD1BF690B68ACFF684F8990411241045E25D451238D42AA28B9900000E001E95E735F2928F2C9C7B1FD0342AFB6A50AB6B7324FEF570A28A2A4D828A28A0028A28A0028A28A0028A28A0028A28A0028A28A0028A28A0028A28A0028A28A002BF543FE0939FF2443C59FF006313FF00E93415F95F5F487ECCDFB6D6BFFB32F83F53F0FE93E1CD375982FAFCDFB4D792C8ACAC6344DA369C63080FE35DF82AD0A1594E7B1F27C5197E2333CB6586C32BC9B4F7B6CFCCFD9EA2BF307FE1ED7E33FF00A11742FF00C089BFC68FF87B5F8CFF00E845D0BFF0226FF1AFA2FED2C377FC19F8C7FA959D7FCFB5FF008147FCCFD3EA2BF307FE1ED7E33FFA11742FFC089BFC68FF0087B5F8CFFE845D0BFF000226FF001A3FB4B0DDFF00061FEA5675FF003ED7FE051FF33F4FA8AFCC1FF87B5F8CFF00E845D0BFF0226FF1A3FE1ED7E33FFA11742FFC089BFC68FED2C377FC187FA959D7FCFB5FF8147FCCF967F699FF00938CF8A3FF00633EA5FF00A552579AD741F10BC613FC42F1E788FC51736F1DADCEB5A8DC6A32411125236964672AA4F3805B1CD73F5F2336A536D773FA270B4E54B0F4E9CB75149FC90514515075051451400514514005145140051451400514514005145140051451400514514005145140051451400514514005145140051451400514514005145140051451400514514005145140051451400514514005145140051451400514514005145140051451400514514005145140051451400514514005145140051451400514514005145140051451400514514121451450014514500145145001451450014514500145145001451450014514500145145001451450014514500145145001451450014B451401FFD9>|IU-trident.jpg>||1.25in||>>|<cell|<with-title-font|Neural
  Network Semantics>>|<cell|>>|<row|<cell|>|<cell|<with|font-series|bold|Caleb
  Schultz Kisby>, <with|font-series|bold|Sa�l Blanco>, and
  <with|font-series|bold|Lawrence Moss>>|<cell|>>|<row|<cell|>|<cell|Luddy
  School of Informatics, Computing, and Engineering>|<cell|>>>>>>

  <\center>
    <tabular|<tformat|<twith|table-width|1par>|<twith|table-hmode|exact>|<cwith|1|-1|1|-1|cell-width|0.3par>|<cwith|1|-1|1|-1|cell-hmode|exact>|<cwith|1|-1|1|-1|cell-hyphen|t>|<twith|table-height|0.4par>|<twith|table-vmode|exact>|<twith|table-hyphen|n>|<cwith|1|-1|1|-1|cell-block|auto>|<cwith|1|-1|1|-1|cell-valign|t>|<cwith|1|-1|1|-1|cell-halign|c>|<cwith|1|1|2|2|cell-row-span|2>|<cwith|1|1|2|2|cell-col-span|1>|<cwith|1|-1|1|-1|cell-bsep|0.5em>|<cwith|1|-1|1|-1|cell-tsep|0.5em>|<cwith|1|1|1|1|cell-row-span|2>|<cwith|1|1|1|1|cell-col-span|1>|<cwith|1|1|3|3|cell-row-span|2>|<cwith|1|1|3|3|cell-col-span|1>|<twith|table-lsep|0em>|<twith|table-rsep|0em>|<twith|table-bsep|0em>|<twith|table-tsep|0em>|<table|<row|<\cell>
      <\framed-titled-block|The Logic>
        <\equation*>
          <tabular|<tformat|<cwith|2|-1|1|1|cell-halign|c>|<cwith|1|1|1|-1|cell-halign|c>|<cwith|1|1|1|-1|cell-tborder|0ln>|<cwith|1|1|1|-1|cell-bborder|1ln>|<cwith|2|2|1|-1|cell-tborder|1ln>|<cwith|1|1|1|1|cell-lborder|0ln>|<cwith|1|1|2|2|cell-rborder|0ln>|<cwith|2|2|1|-1|cell-tsep|0.25em>|<twith|table-width|1par>|<twith|table-hmode|exact>|<cwith|1|1|2|2|cell-halign|l>|<cwith|1|-1|2|2|cell-lsep|0.5em>|<cwith|5|5|2|2|cell-hyphen|t>|<cwith|6|6|2|2|cell-hyphen|t>|<cwith|7|7|2|2|cell-hyphen|t>|<table|<row|<cell|<text|<with|font-series|bold|Syntax>>>|<cell|<with|font-series|bold|<text|Neural
          Net Semantics>>>>|<row|<cell|p>|<cell|<text|a (fuzzy) set of
          neurons>>>|<row|<cell|A\<wedge\>B>|<cell|A\<cup\>B>>|<row|<cell|A\<rightarrow\>B>|<cell|A\<supseteq\>B>>|<row|<cell|<value|Know>A>|<\cell>
            the set of <text|neurons graph-reachable from >A
          </cell>>|<row|<cell|<value|Typ>A>|<\cell>
            <text|the set of neurons activated by >A
          </cell>>|<row|<cell|<around*|[|A|]>B>|<\cell>
            <text|after repeated Hebbian update, >B
          </cell>>>>>
        </equation*>

        <\small>
          <\note*>
            You might expect <math|\<wedge\>> to be <math|\<cap\>>,
            <math|\<rightarrow\>> to be <math|\<subseteq\>>. If we \Pflip\Q
            the semantics this way, <math|<value|Know>>,<value|Typ> get
            replaced by their duals <math|<value|diaKnow>>,<math|<value|diaTyp>>.
            Otherwise, exactly the same axioms hold.
          </note*>
        </small>
      </framed-titled-block>

      \;

      <\framed-titled-block|Static Net Axioms>
        <\equation*>
          <tabular|<tformat|<cwith|1|1|1|1|cell-row-span|1>|<cwith|1|1|1|1|cell-col-span|2>|<twith|table-width|1par>|<twith|table-hmode|exact>|<cwith|1|1|1|-1|cell-tborder|0ln>|<cwith|1|1|1|-1|cell-bborder|1ln>|<cwith|2|2|1|1|cell-tborder|1ln>|<cwith|1|1|1|-1|cell-rborder|0ln>|<cwith|1|1|1|-1|cell-lborder|0ln>|<cwith|6|6|1|1|cell-row-span|1>|<cwith|6|6|1|1|cell-col-span|2>|<cwith|6|6|1|-1|cell-tborder|0ln>|<cwith|5|5|1|1|cell-bborder|0ln>|<cwith|6|6|1|-1|cell-bborder|1ln>|<cwith|7|7|1|1|cell-tborder|1ln>|<cwith|6|6|1|-1|cell-rborder|0ln>|<cwith|6|6|1|-1|cell-lborder|0ln>|<cwith|2|2|1|-1|cell-tsep|0.5em>|<cwith|7|7|1|-1|cell-tsep|0.5em>|<cwith|6|6|1|1|cell-tsep|0.75em>|<cwith|10|10|2|2|cell-hyphen|t>|<cwith|10|10|1|1|cell-valign|t>|<table|<row|<cell|<text|<with|font-series|bold|Properties
          of ><value|Know>>>|<cell|<text|<with|font-series|bold|Basic Modal
          Axioms>>>>|<row|<cell|<text|Refl>>|<cell|<value|Know>A\<rightarrow\>A>>|<row|<cell|<text|Trans>>|<cell|<value|Know>A\<rightarrow\><value|Know><value|Know>A>>|<row|<cell|<text|Acyclic>>|<cell|<value|Know><around*|(|<value|Know><around*|(|A\<rightarrow\><value|Know>A|)>\<rightarrow\>A|)>\<rightarrow\>A>>|<row|<cell|<text|Monotone>>|<cell|<value|Know><around*|(|A\<rightarrow\>B|)>\<rightarrow\><around*|(|<value|Know>A\<rightarrow\><value|Know>B|)>>>|<row|<cell|<text|<with|font-series|bold|Properties
          of ><value|Typ>>>|<cell|>>|<row|<cell|<text|Refl>>|<cell|<value|Typ>A\<rightarrow\>A>>|<row|<cell|<text|Trans>>|<cell|<value|Typ>A\<rightarrow\><value|Typ><value|Typ>A>>|<row|<cell|<text|Interact>>|<cell|<value|Know>A\<rightarrow\><value|Typ>A>>|<row|<cell|<text|Loop>>|<\cell>
            <tabular|<tformat|<table|<row|<cell|<around*|(|<value|Typ>A<rsub|1>\<rightarrow\>A<rsub|2>|)>\<ldots\><around*|(|<value|Typ>A<rsub|n>\<rightarrow\>A<rsub|1>|)>>>|<row|<cell|<space|1em>\<rightarrow\><around*|(|<value|Typ>A<rsub|i>\<leftrightarrow\>A<rsub|j>|)>>>>>>
          </cell>>>>>
        </equation*>

        \;
      </framed-titled-block>
    </cell>|<\cell>
      <\framed-titled-block|Neural Net Model Building>
        \;

        \;

        \;

        \;

        \;

        \;

        \;

        \;

        \;

        \;

        \;

        \;

        \;

        \;

        \;

        \;

        \;

        \;

        \;

        \;

        \;

        \;
      </framed-titled-block>
    </cell>|<\cell>
      <\framed-titled-block|Hebbian Learning Axioms>
        blah blah blah more text more text here's some more text blah blah
        blah more text more text here's some more text blah blah blah more
        text more text here's some more text blah blah blah more text more
        text here's some more text blah

        \;

        \;

        \ 

        \;
      </framed-titled-block>

      \;

      <\framed-titled-block|Work In Progress>
        blah blah blah more text more text here's some more text blah blah
        blah more text more text here's

        \;
      </framed-titled-block>

      \;

      <\framed-titled-block|Future Work>
        blah blah blah more text more text here's some more text blah blah
        blah more text more text

        \;

        \;

        <\small>
          <\acknowledgments*>
            This work was funded by the US Department of Defense (Contract
            W52P1J2093009).<nbsp> Thank you for your support!
          </acknowledgments*>
        </small>
      </framed-titled-block>
    </cell>>|<row|<\cell>
      \;
    </cell>|<\cell>
      \;
    </cell>|<\cell>
      <tabular|<tformat|<twith|table-width|1par>|<twith|table-hmode|exact>|<cwith|1|-1|1|1|cell-halign|c>|<cwith|1|-1|1|1|cell-valign|t>|<cwith|1|-1|1|1|cell-hyphen|t>|<cwith|1|1|1|1|cell-row-span|2>|<cwith|1|1|1|1|cell-col-span|1>|<table|<row|<\cell>
        <framed-titled-block|Title 6|blah blah blah more text more text
        here's some more text blah blah blah more text more text here's some
        more text blah blah blah more text more text here's some more text >
      </cell>>|<row|<\cell>
        <\framed-titled-block|Acknowledgements>
          blah blah blah more text more text here's some more text blah blah
          blah more text more text here's some more text\ 
        </framed-titled-block>
      </cell>>>>>
    </cell>>>>>
  </center>
</body>

<\initial>
  <\collection>
    <associate|bg-color|white>
    <associate|enunciation-sep|<macro|. >>
    <associate|font|frak=TeX Gyre Pagella,cal=TeX Gyre Termes,roman>
    <associate|font-base-size|24>
    <associate|font-family|ss>
    <associate|font-shape|right>
    <associate|item-hsep|<macro|1fn>>
    <associate|item-vsep|<macro|0.1fn>>
    <associate|large-padding-above|0.1fn>
    <associate|large-padding-below|0fn>
    <associate|math-font|math-termes>
    <associate|page-height|36in>
    <associate|page-medium|paper>
    <associate|page-type|user>
    <associate|page-width|48in>
    <associate|paper-rough-dark-scene-bg-color|#800000>
    <associate|paper-rough-light-scene-bg-color|white>
    <associate|paper-rough-ornament-color|#800000>
    <associate|par-columns|1>
    <associate|par-par-sep|0.3333fn>
    <associate|par-sep|0.1fn>
    <associate|title-vpadding|1em>
    <associate|title-vsep|0spc>
  </collection>
</initial>