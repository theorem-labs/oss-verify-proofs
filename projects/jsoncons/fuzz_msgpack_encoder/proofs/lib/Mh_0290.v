(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith List Lia Bool. From stdpp.bitvector Require definitions. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Asan. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0080. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0124. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0242. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0253. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0260. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0270. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0189. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0238. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0239. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0206. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0249. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0246. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0181. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0234. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0262. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0268. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0230. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0202. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0228. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PnASinkPush. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0236. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PnACVal. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0243. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0200. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PnAEncEndA. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PnAEncEndO. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0284. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PnATsDivE. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0269. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0265. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PnAEncStrT. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PnAAdEa. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PnAAdEo. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0278. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0259. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PnATsWs. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PnATsWs2d PnACValR. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0288. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PnARiT8 PnARiT12. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0287.
Module NTopAsmA.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0080. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0124. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0242. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0253. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0260. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0270. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0189. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0238. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0239. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0206. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0249. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0246. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0181. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0234. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0262. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0268. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0230. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0202. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0228. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PnASinkPush. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0236. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PnACVal. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0243. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0200. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PnAEncEndA PnAEncEndO. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0284. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PnATsDivE. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0269. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0265. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PnAEncStrT PnAAdEa PnAAdEo. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0278. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0259. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PnATsWs PnATsWs2d PnACValR. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0288. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PnARiT8 PnARiT12. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0287. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0080.HeapIfaceAMxI OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMr OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PmLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PmStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PgV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgSrcA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgV8A OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunBA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0080.PnSpecsAmc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutQA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnQStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnVisA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunHA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.PnAImgGap OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAdStrA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAXq OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAXl OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.VaSpec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.NemLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.NemLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSink OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemSinkA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnVisN OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnVisNA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0124.PnRunN OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnRunNA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0242.PnAOpnewN OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0253.PnATsSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0253.PnATs12Specs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0253.PnATs12SpecsW2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0260.PnATs12Pot OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0253.PnATsTsw OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0260.PnATsVPot OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnRunAr OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnCValSpecA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0270.PnAAdVs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0242.PnAOpnew OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0189.PnAOpdel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0238.PnASrcXsgetn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0239.Na0PgSrcFill OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0239.Na0PgSrcFillTb OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0206.Na0PgSrcRead OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0249.PnALoc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0239.PnAStr OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0246.PnAIss OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0181.PnASys OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0242.PnAIosDtor OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0234.PnASrcDtor OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0234.PnAMakeEc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0246.Na0PgV8Close OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0262.PnAEmbC OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAXe OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0262.PnAEPushC OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0270.PnARst OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0249.PnAPCtor OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0262.PnALvPush OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0181.PnAAdCtor OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0268.PnARdCtor OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0270.PnARdDtor OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAdStrCA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0230.PnAAdPbC OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAKStrC3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAdStrCA2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0202.PnAAdGbC OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0228.PnAAdScC OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0249.PnAAdSdC OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0270.PnAAdInC OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0270.PnAAdJnC OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0270.PnAAdFuC OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0249.PnAAdFiC OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAdStrCB OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0270.PnAAdB6C OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PnASinkPush OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0268.PnAEncNtbN OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAEncNtbFSpec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0268.PnAEncNtbF OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0236.PnAEncWts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0236.PnAEncWsv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PnACVal OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0268.PnAEncNull OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0268.PnAEncBool OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0234.PnAEncU64 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0243.PnAEncI64 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0249.PnAEncDbl OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0236.PnAEncKey OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0200.PnAEncBst OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0200.PnAEncBsr OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0200.PnAEncBeg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0200.PnAEncBegO OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PnAEncEndA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0236.PnAEstkAnn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PnAEncEndO OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0249.PnAEncFlush OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0260.NemSpecsTsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0284.PnATsTsnz OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PnATsDivE OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0269.PnATsMuC OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0269.PnATsAdC OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0265.PnATsRzD3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0269.PnATsMuD OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0269.PnATsAdD OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0284.PnATsMuG OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0284.PnATsAdG OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0284.PnAEncTob OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PnAEncStrT OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0260.PnAEncTobK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0270.PnAAdBa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0270.PnAAdBo OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PnAAdEa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0228.PnAAnnLv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PnAAdEo OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0230.PnAAdU64 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0270.PnAAdI64 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0278.PnAAdDbl OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0278.VaSOpC OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0278.WaSnBridge OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0259.WaStBridge OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0249.VaLedgerN OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0270.PnAAdNl OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0270.PnAAdBl OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0270.PnAAdBt OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0230.PnAAdBr OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0268.PnAAdFl OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0270.PnAGetSize OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0270.PnABegArr OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0249.PnABegObj OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0269.PnATsMul OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0269.PnATsAdd OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PnATsWs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0269.PnATsLt0 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0269.PnATsAdd1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0284.PnATsAdd2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0269.PnATsSub1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0284.PnATsSub2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0284.PnATsWs2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PnATsWs2d OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PnACValR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0288.PnAReadItem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PnARiT8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PnARiT12 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0287.PnALp2.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module NTASMA.
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation AD := PMA.AD.
Abbreviation AAD := PMA.AAD.
Abbreviation AQ := PnLayoutQA.QADDR_A.
Abbreviation AE := NemLayoutA.NEADDR_A.
Section SCFG_1.
Context {SCFG_P : ScfgP}.

(* [comment removed for export] *)
Record harness_depsS (Lx : asan_layout) (arx : asan_run) (HI : asan_iface) (RES : credit) : Prop := HDEPSS {
  hds_str_ctor : PMA.str_ctor_spec Lx arx HI;
  hds_iss_ctor : PMA.iss_ctor_spec Lx arx HI;
  hds_reader_ctor : PQRAa.reader_ctor_spec Lx arx HI;
  hds_syscat : PMA.syscat_spec Lx arx HI;
  hds_reset : PQRAa.reset_spec Lx arx HI;
  hds_parse : PNRNA.parse_specF RSEGS AD AQ AAD AE Lx arx (fun _ : list (list Z) => HI) RES;
  hds_reader_dtor : PQRAa.reader_dtor_spec Lx arx HI;
  hds_opdel : PMA.opdel_spec Lx arx HI;
  hds_locale_dtor : PMA.locale_dtor_spec Lx arx HI;
  hds_ios_dtor : PMA.ios_dtor_spec Lx arx HI
}.

Section Asm.
Variables (L : asan_layout) (C : asan_statics_cells) (IL : icpt_layout) (LR : HAR.layoutR).
Hypothesis LY : PMA.layout L C.
Hypothesis ILY : as0_icpt_layout IL.
Hypothesis MCC : PMAMC.mcmp_cells C.
Hypothesis SNPC : VA.snp_cells C.
Variable ar : asan_run.
Variable HIk : list (list Z) -> asan_iface.
(* [comment removed for export] *)
Variable TSRESA : credit.
(* [comment removed for export] *)
Definition tspE : Z -> Z -> list (list Z) -> list Z -> credit := NETSA.TSPE LR.
Definition TSPVMAX : credit := NETSA.TSPEMAX.
(* [comment removed for export] *)
Definition tspv_laws (f : Z -> list (list Z) -> list Z -> credit) (MX : credit) : Prop :=
  forall t D RC, PMSP.credit_le PMSP.cr0 (f t D RC) /\ PMSP.credit_le (f t D RC) MX /\ (t <> NEM.TAG_ENANO -> f t D RC = PMSP.cr0)
                 /\ (forall D', incl D D' -> PMSP.credit_le (f t D' RC) (f t D RC)) /\ (forall RC', f t D RC' = f t D RC).
Definition tspe_laws (f : Z -> Z -> list (list Z) -> list Z -> credit) (MX : credit) : Prop :=
  forall t r D RC, PMSP.credit_le PMSP.cr0 (f t r D RC) /\ PMSP.credit_le (f t r D RC) MX /\ (t <> NEM.TAG_ENANO -> f t r D RC = PMSP.cr0)
                   /\ (forall D', incl D D' -> PMSP.credit_le (f t r D' RC) (f t r D RC)).
Lemma TSPE_OK : tspe_laws tspE TSPVMAX.
Proof. exact (PNAETBK.TSPE_laws LR). Qed.
(* [comment removed for export] *)
Definition tspV : Z -> list (list Z) -> list Z -> credit := PQAAVS.tspV tspE.
Lemma TSPV_OK : tspv_laws tspV TSPVMAX.
Proof. intros t D RC. pose proof (TSPE_OK t PQAAVS.VSRA D []) as (A & B & C' & E). unfold tspV, PQAAVS.tspV. split; [exact A|]. split; [exact B|]. split; [exact C'|]. split; [intros D' I; exact (E D' I)| intros RC'; reflexivity]. Qed.
Local Lemma TSNN t q Dx RCx : 0 <= fst (tspE t q Dx RCx) /\ 0 <= snd (tspE t q Dx RCx).
Proof. pose proof (TSPE_OK t q Dx RCx) as (A & _). revert A. unfold PMSP.credit_le, PMSP.cr0. cbn [fst snd]. intros A; exact A. Qed.
Local Lemma TSANTI t q Dx Dy RCx : incl Dx Dy -> PMSP.credit_le (tspE t q Dy RCx) (tspE t q Dx RCx).
Proof. intros I. pose proof (TSPE_OK t q Dx RCx) as (_ & _ & _ & E). exact (E Dy I). Qed.
(* [comment removed for export] *)
Definition tswe : list (list Z) -> Z -> list Z -> credit := PQATSTW.TSW LR.
Lemma TSWE : PQATSP.tswe_laws tswe PQATSTW.TSWMAX.
Proof. pose proof (PQATSTW.tsw_laws_ok LR) as (A & B). split; [intros D r RC; exact (A D 0 r RC)| intros D D' r RC; exact (B D D' 0 r RC)]. Qed.
(* [comment removed for export] *)
Hypothesis RESGE : PMSP.credit_le (PQATSPV.T12VMAX L PQATSTW.TSWMAX TSPVMAX) TSRESA.
Definition tsp : list (list Z) -> list Z -> credit := PQATSPV.T12V L LR tswe tspV.
Lemma TSP_LE : forall D RC, PMSP.credit_le PMSP.cr0 (tsp D RC) /\ PMSP.credit_le (tsp D RC) TSRESA.
Proof. exact (PQATSPV.T12V_bounds L C LR tswe PQATSTW.TSWMAX tspV TSPVMAX TSRESA LY TSWE TSPV_OK RESGE). Qed.
Lemma TSP_V : forall t D RC RCv, PMSP.credit_le (tspV t D RCv) (tsp D RC)
                               /\ (forall D', incl D D' -> PMSP.credit_le (PM.credit_add (tsp D' RC) (tspV t D RCv)) (PM.credit_add (tsp D RC) (tspV t D' RCv))).
Proof. exact (PQATSPV.T12V_vlaw L C LR tswe PQATSTW.TSWMAX tspV TSPVMAX LY TSWE TSPV_OK). Qed.

(* [comment removed for export] *)
Definition inst_ok (HI : asan_iface) : Prop :=
  HAJ.asan_iface_okR L ar C SCFG HI /\ aicpt_ok L ar IL SCFG HI /\ HAJ.asan_ext_ok L ar SCFG HI PMA.EXT /\ PMAGAP.rt_img_gap HI.
Definition fam_ok : Prop := HAR.asan_famR_ok L ar C SCFG LR HIk /\ (forall D, inst_ok (HIk D)) /\ (forall D, PQASA.memmove_libc_n_spec L ar (HIk D) IL).
Hypothesis FAM : fam_ok.
Let IOKD (D : list (list Z)) : inst_ok (HIk D) := proj1 (proj2 FAM) D.
Let MMLN (D : list (list Z)) : PQASA.memmove_libc_n_spec L ar (HIk D) IL := proj2 (proj2 FAM) D.
(* [comment removed for export] *)
Let MALLOCN (D : list (list Z)) : HAR.amallocN_spec L ar SCFG (fun _ => HIk D) := fun _ => HAR.fr_mallocN L ar C SCFG LR HIk (proj1 FAM) D.
Let MEMCPYN (D : list (list Z)) : HAR.amemcpyN_spec_at L ar SCFG (fun _ => HIk D) (hl_asan_memcpy L) := fun _ => HAR.fr_memcpyN L ar C SCFG LR HIk (proj1 FAM) D.
Let MEMMOVEN (D : list (list Z)) : PQASA.memmove_n_spec L ar (HIk D) := fun _ => HAR.fr_memmoveN L ar C SCFG LR HIk (proj1 FAM) D.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Lemma opnew_n_wide D : NESKA.opnew_n_spec RSEGS AD L ar (HIk D) (NESKA.spa_nmax (NESKA.PMEA L)).
Proof.
  pose proof (PMAOPNW.opnew_n_ok L ar C (HIk D) LY (proj1 (IOKD D)) (MALLOCN D)) as W.
  intros fx R M model K LB FF LK Aw cr n sp r RI AM HK G10 Hn. apply (W fx R M model K LB FF LK Aw cr n sp r RI AM HK G10). revert Hn. clear. cbn. unfold HAR.NREQ, NESK.ZMAX. lia.
Qed.
Local Lemma NMAXI : NESKA.spa_nmax (NESKA.PMEA L) <= 2 ^ 31. Proof. cbn. unfold NESK.ZMAX. lia. Qed.
Let opnew_n_free (D : list (list Z)) : PQRAa.opnew_n_spec L ar (HIk D) := PMAOPNW.opnew_n_ok L ar C (HIk D) LY (proj1 (IOKD D)) (MALLOCN D).   (* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record open_A : Prop := OPENA {
  oa_pin : L = L /\ C = C /\ IL = IL /\ LR = LR /\ ar = ar /\ HIk = HIk /\ TSRESA = TSRESA;

}.
Hypothesis OPEN : open_A.

(* [comment removed for export] *)
Lemma opnew_c HI (IOK : inst_ok HI) : PMA.opnew_spec L ar HI.
Proof. exact (PMAOPN.opnew_ok L ar C HI LY (proj1 IOK)). Qed.   (* [comment removed for export] *)
Lemma opdel_c HI (IOK : inst_ok HI) : PMA.opdel_spec L ar HI.
Proof. exact (PMAOPD.opdel_ok L ar C HI LY (proj1 IOK)). Qed.   (* [comment removed for export] *)
Lemma xsgetn_c HI (IOK : inst_ok HI) : PMA.xsgetn_spec L ar HI.
Proof. exact (PMAXG.xsgetn_ok L ar C IL HI LY (proj1 IOK) (proj1 (proj2 IOK)) ILY). Qed.   (* [comment removed for export] *)
Lemma fill_buffer_c HI (IOK : inst_ok HI) : PQRAa.fill_buffer_spec L ar HI.
Proof. exact (PGSFBA.fill_buffer_okG L ar C HI LY (proj1 IOK) IL (proj1 (proj2 IOK)) ILY (xsgetn_c HI IOK)). Qed.   (* [comment removed for export] *)
Lemma fill_buffer_tb_c HI (IOK : inst_ok HI) : PQRAa.fill_buffer_tb_spec L ar HI.
Proof. exact (PGSFBTA.fill_buffer_tb_okG L ar C HI LY (proj1 IOK) IL (proj1 (proj2 IOK)) ILY (xsgetn_c HI IOK)). Qed.   (* [comment removed for export] *)
Lemma src_read_c HI (IOK : inst_ok HI) : PQRAa.src_read_spec L ar HI.
Proof. exact (PGSRDA.src_read_okG L ar C HI LY (proj1 IOK) IL (proj1 (proj2 IOK)) ILY (fill_buffer_c HI IOK) (xsgetn_c HI IOK)). Qed.   (* [comment removed for export] *)
(* [comment removed for export] *)
Lemma locale_ctor_c HI (IOK : inst_ok HI) : PMA.locale_ctor_spec L ar HI.
Proof. exact (PMALOC.locale_ctor_ok L ar C IL HI LY (proj1 IOK) (proj1 (proj2 IOK)) ILY MCC). Qed.   (* [comment removed for export] *)
Lemma locale_dtor_c HI (IOK : inst_ok HI) : PMA.locale_dtor_spec L ar HI.
Proof. exact (PMALOC.locale_dtor_ok L ar C HI LY (proj1 IOK)). Qed.   (* [comment removed for export] *)
Lemma str_ctor_c HI (IOK : inst_ok HI) : PMA.str_ctor_spec L ar HI.
Proof. exact (PMASTR.str_ctor_ok L ar C HI LY (proj1 IOK) (opnew_c HI IOK)). Qed.   (* [comment removed for export] *)
Lemma iss_ctor_c HI (IOK : inst_ok HI) : PMA.iss_ctor_spec L ar HI.
Proof. exact (PMAISS.iss_ctor_ok L ar C IL HI LY (proj1 IOK) (proj1 (proj2 IOK)) ILY (locale_ctor_c HI IOK) (opnew_c HI IOK)). Qed.   (* [comment removed for export] *)
Lemma syscat_c HI (IOK : inst_ok HI) : PMA.syscat_spec L ar HI.
Proof. exact (PMASY.syscat_ok L ar C HI LY (proj1 IOK)). Qed.   (* [comment removed for export] *)
Lemma ios_dtor_c HI (IOK : inst_ok HI) : PMA.ios_dtor_spec L ar HI.
Proof. exact (PMAID.ios_dtor_ok L ar C HI LY (proj1 IOK) (proj1 (proj2 (proj2 IOK))) (locale_dtor_c HI IOK)). Qed.   (* [comment removed for export] *)
Lemma src_dtor_c HI (IOK : inst_ok HI) : PMA.src_dtor_spec L ar HI.
Proof. exact (PMASD.src_dtor_ok L ar C HI LY (proj1 IOK) (opdel_c HI IOK) (locale_dtor_c HI IOK) (ios_dtor_c HI IOK)). Qed.   (* [comment removed for export] *)
Lemma make_ec_c HI (IOK : inst_ok HI) : PQRAa.make_ec_spec L ar HI.
Proof. exact (PQAMEC.make_ec_ok L ar C HI LY (proj1 IOK) (proj1 (proj2 (proj2 IOK)))). Qed.   (* [comment removed for export] *)
Lemma read_span_v_c HI (IOK : inst_ok HI) : PQRAa.read_span_v_spec L ar HI.
Proof. exact (PGVCLA.read_span_v_closed L ar C HI LY (proj1 IOK) (proj1 (proj2 (proj2 IOK))) IL (proj1 (proj2 IOK)) ILY (opnew_c HI IOK) (opdel_c HI IOK) (xsgetn_c HI IOK)). Qed.   (* [comment removed for export] *)
Lemma push_cont_c HI (IOK : inst_ok HI) : PQSAXQ.push_cont_spec RSEGS PMA.AD L ar HI 0xd4dc8.
Proof. exact (PQAEC.push_cont_ok L ar C HI LY (proj1 IOK) (proj1 (proj2 (proj2 IOK))) (opnew_c HI IOK) (opdel_c HI IOK)). Qed.   (* [comment removed for export] *)
Lemma epush_cont_f D : PQSAXE.epush_spec RSEGS PMA.AD L ar (HIk D) 0xc5fb4.
Proof. exact (NEAEP.epush_ok L ar C (HIk D) LY (proj1 (IOKD D)) (proj1 (proj2 (proj2 (IOKD D)))) (opnew_c (HIk D) (IOKD D)) (opdel_c (HIk D) (IOKD D))). Qed.   (* [comment removed for export] *)
Lemma reset_c HI (IOK : inst_ok HI) : PQRAa.reset_spec L ar HI.
Proof. exact (PQARS.reset_ok L ar C HI LY (proj1 IOK) (proj1 (proj2 (proj2 IOK))) (opnew_c HI IOK)). Qed.   (* [comment removed for export] *)
Lemma parser_ctor_c HI (IOK : inst_ok HI) : PQRAa.parser_ctor_spec L ar HI.
Proof. exact (PQAPC.parser_ctor_ok L ar C IL HI LY (proj1 IOK) (proj1 (proj2 IOK)) ILY (proj1 (proj2 (proj2 IOK))) (locale_ctor_c HI IOK) (opnew_c HI IOK)). Qed.   (* [comment removed for export] *)
Lemma lvpush_any_c HI (IOK : inst_ok HI) : PQSAXL.lvpush_any_spec RSEGS PMA.AD L ar HI 0xb84e8.
Proof. exact (PQALVP.lvpush_ok L ar C HI LY (proj1 IOK) (proj1 (proj2 (proj2 IOK))) (opnew_c HI IOK) (opdel_c HI IOK)). Qed.   (* [comment removed for export] *)
Lemma adaptor_ctor_c HI (IOK : inst_ok HI) : PQRAa.adaptor_ctor_spec L ar HI.
Proof. exact (PQAADC.adaptor_ctor_ok L ar C HI LY (proj1 IOK) (PQSAXL.lvpush_any_empty _ _ _ _ _ _ (lvpush_any_c HI IOK))). Qed.   (* [comment removed for export] *)
Lemma reader_ctor_c HI (IOK : inst_ok HI) : PQRAa.reader_ctor_spec L ar HI.
Proof. exact (PQARDC.reader_ctor_ok L ar C HI LY (proj1 IOK) eq_refl (parser_ctor_c HI IOK) (adaptor_ctor_c HI IOK)). Qed.   (* [comment removed for export] *)
Lemma reader_dtor_c HI (IOK : inst_ok HI) : PQRAa.reader_dtor_spec L ar HI.
Proof. exact (PQARDD.reader_dtor_ok L ar C HI LY (proj1 IOK) (proj1 (proj2 (proj2 IOK))) (opdel_c HI IOK) (src_dtor_c HI IOK)). Qed.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma spbC_A_f D : PQASCA.pb_specCA RSEGS AD L ar (HIk D) 0xf4640.
Proof. exact (PQAAPBC.pb_ok L ar C IL (HIk D) LY (proj1 (IOKD D)) (proj1 (proj2 (IOKD D))) ILY (opnew_n_free D) (opdel_c (HIk D) (IOKD D)) (MMLN D)). Qed.   (* [comment removed for export] *)
(* [comment removed for export] *)
Lemma gbC_A_f D : PQAKZC3.gb_specCA L ar (HIk D) 0xf44f4.
Proof. exact (PQAAGBC.gb_ok L ar C IL (HIk D) LY (proj1 (IOKD D)) (proj1 (proj2 (IOKD D))) ILY (opnew_n_free D) (opdel_c (HIk D) (IOKD D)) (MMLN D)). Qed.   (* [comment removed for export] *)
Lemma scC_A_f D : PQAKZC3.sc_specCA L ar (HIk D) 0xb9a6c.
Proof. exact (PQAASCC.sc_ok L ar C IL (HIk D) LY (proj1 (IOKD D)) (proj1 (proj2 (IOKD D))) ILY (gbC_A_f D) (MEMMOVEN D)). Qed.   (* [comment removed for export] *)
Lemma sdC_A_f D : PQAKZC3.sc_specCA L ar (HIk D) 0xbe70c.
Proof. exact (PQAASDC.sc_ok L ar C IL (HIk D) LY (proj1 (IOKD D)) (proj1 (proj2 (IOKD D))) ILY (gbC_A_f D) (MEMMOVEN D)). Qed.   (* [comment removed for export] *)
Lemma sinsC_A_f D : PQASCA.ins_specCA RSEGS AD L ar (HIk D) 0xb95f0.
Proof. exact (PQAAINC.ins_ok L ar C IL (HIk D) LY (proj1 (IOKD D)) (proj1 (proj2 (IOKD D))) ILY (scC_A_f D)). Qed.   (* [comment removed for export] *)
Lemma sjnsC_A_f D : PQASCA.ins_specCA RSEGS AD L ar (HIk D) 0xbe330.
Proof. exact (PQAAJNC.ins_ok L ar C IL (HIk D) LY (proj1 (IOKD D)) (proj1 (proj2 (IOKD D))) ILY (sdC_A_f D)). Qed.   (* [comment removed for export] *)
Lemma fromuC_A_f D : PQASCA2.fromu_specCA RSEGS AD L ar (HIk D) 0xb8fb0.
Proof. exact (PQAAFUC.fromu_ok L ar C IL (HIk D) LY (proj1 (IOKD D)) (proj1 (proj2 (IOKD D))) ILY (spbC_A_f D)). Qed.   (* [comment removed for export] *)
Lemma fromiC_A_f D : PQASCA2.fromi_specCA RSEGS AD L ar (HIk D) 0xba148.
Proof. exact (PQAAFIC.fromi_ok L ar C IL (HIk D) LY (proj1 (IOKD D)) (proj1 (proj2 (IOKD D))) ILY (spbC_A_f D)). Qed.   (* [comment removed for export] *)
Lemma b64C_A_f D : PQASCB.b64_specCA RSEGS AD L ar (HIk D) 0xbebe4 0x26613.
Proof. exact (PQAAB6C.b64_ok L ar C IL (HIk D) LY (proj1 (IOKD D)) (proj1 (proj2 (IOKD D))) ILY (proj2 (proj2 (proj2 (IOKD D)))) (spbC_A_f D)). Qed.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Lemma PO : NESKA.sink_policyA_ok L (NESKA.PMEA L).   (* [comment removed for export] *)
Proof. pose proof (PMA.ly_cost L C LY) as (LCK & LCL & LCO). apply NESKA.PMEA_ok; [rewrite LCK| rewrite LCL| rewrite LCO]; cbn; lia. Qed.
Local Lemma HBS : NESKA.spa_hb (NESKA.PMEA L) NESK.SMZ.   (* [comment removed for export] *)
Proof. cbn. apply Z.le_refl. Qed.
Lemma push_back_f D : NESKA.push_back_specA RSEGS AD AE L ar (HIk D) (NESKA.PMEA L).
Proof. exact (PEASKP.push_back_ok L ar C (HIk D) (NESKA.PMEA L) LY (proj1 (IOKD D)) (proj1 (proj2 (proj2 (IOKD D)))) PO (opnew_n_wide D) (opdel_c (HIk D) (IOKD D)) (MEMCPYN D) NMAXI). Qed.   (* [comment removed for export] *)
Lemma ntb_u16_f D : NECSA.ntb_specA RSEGS AD L ar (HIk D) (NESKA.PMEA L) 2 (ne_ntb_u16 AE).
Proof. exact (PNAENTB.ntb_u16A_ok L ar C (HIk D) (NESKA.PMEA L) LY (proj1 (IOKD D)) PO HBS (push_back_f D)). Qed.   (* [comment removed for export] *)
Lemma ntb_u32_f D : NECSA.ntb_specA RSEGS AD L ar (HIk D) (NESKA.PMEA L) 4 (ne_ntb_u32 AE).
Proof. exact (PNAENTB.ntb_u32A_ok L ar C (HIk D) (NESKA.PMEA L) LY (proj1 (IOKD D)) PO HBS (push_back_f D)). Qed.   (* [comment removed for export] *)
Lemma ntb_u64_f D : NECSA.ntb_specA RSEGS AD L ar (HIk D) (NESKA.PMEA L) 8 (ne_ntb_u64 AE).
Proof. exact (PNAENTB.ntb_u64A_ok L ar C (HIk D) (NESKA.PMEA L) LY (proj1 (IOKD D)) PO HBS (push_back_f D)). Qed.   (* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ntb_i16_f D : NECSA.ntb_specA RSEGS AD L ar (HIk D) (NESKA.PMEA L) 2 (ne_ntb_i16 AE).
Proof. exact (PNAENTB.ntb_i16A_ok L ar C (HIk D) (NESKA.PMEA L) LY (proj1 (IOKD D)) PO HBS (push_back_f D)). Qed.   (* [comment removed for export] *)
Lemma ntb_i32_f D : NECSA.ntb_specA RSEGS AD L ar (HIk D) (NESKA.PMEA L) 4 (ne_ntb_i32 AE).
Proof. exact (PNAENTB.ntb_i32A_ok L ar C (HIk D) (NESKA.PMEA L) LY (proj1 (IOKD D)) PO HBS (push_back_f D)). Qed.   (* [comment removed for export] *)
Lemma ntb_i64_f D : NECSA.ntb_specA RSEGS AD L ar (HIk D) (NESKA.PMEA L) 8 (ne_ntb_i64 AE).
Proof. exact (PNAENTB.ntb_i64A_ok L ar C (HIk D) (NESKA.PMEA L) LY (proj1 (IOKD D)) PO HBS (push_back_f D)). Qed.   (* [comment removed for export] *)
Lemma ntb_f32_f D : PENTBAF.ntbf_specA RSEGS AD L ar (HIk D) (ne_ntb_f32 AE) 4 (NESKA.PMEA L).
Proof. exact (PEAENTBF.ntb_f32_ok L ar C (HIk D) (NESKA.PMEA L) LY (proj1 (IOKD D)) PO (push_back_f D)). Qed.   (* [comment removed for export] *)
Lemma ntb_f64_f D : PENTBAF.ntbf_specA RSEGS AD L ar (HIk D) (ne_ntb_f64 AE) 8 (NESKA.PMEA L).
Proof. exact (PEAENTBF.ntb_f64_ok L ar C (HIk D) (NESKA.PMEA L) LY (proj1 (IOKD D)) PO (push_back_f D)). Qed.   (* [comment removed for export] *)
Lemma write_timestamp_f D : NECSA.write_timestamp_specA RSEGS AD AE L ar (HIk D) (NESKA.PMEA L).
Proof. exact (PNAEWTS.write_timestamp_ok AQ L ar C (HIk D) (NESKA.PMEA L) LY (proj1 (IOKD D)) PO HBS (push_back_f D) (ntb_u32_f D) (ntb_u64_f D)). Qed.   (* [comment removed for export] *)
Lemma wsv_f D : NECSA.wsv_specA RSEGS AD AE L ar (HIk D) (NESKA.PMEA L).
Proof. exact (PNAEWSV.wsv_ok AQ L ar C (HIk D) (NESKA.PMEA L) LY (proj1 (IOKD D)) PO HBS (push_back_f D) (ntb_u16_f D) (ntb_u32_f D) (PECVALA.validate_fun_ok L ar C (HIk D) LY (proj1 (IOKD D)) (proj2 (proj2 (proj2 (IOKD D)))))). Qed.   (* [comment removed for export] *)
Lemma eo_null_f D : NECSA.v_null_spec RSEGS AD AQ AAD AE L ar (HIk D) (NESKA.PMEA L).
Proof. exact (PNAENCN.v_null_ok AQ L ar C (HIk D) (NESKA.PMEA L) LY (proj1 (IOKD D)) PO HBS (push_back_f D)). Qed.   (* [comment removed for export] *)
Lemma eo_bool_f D : NECSA.v_bool_spec RSEGS AD AQ AAD AE L ar (HIk D) (NESKA.PMEA L).
Proof. exact (PNAENCT.v_bool_ok AQ L ar C (HIk D) (NESKA.PMEA L) LY (proj1 (IOKD D)) PO HBS (push_back_f D)). Qed.   (* [comment removed for export] *)
Lemma eo_uint64_f D : NECSA.v_uint64_spec RSEGS AD AQ AAD AE L ar (HIk D) (NESKA.PMEA L).
Proof. exact (PNAENU64.v_uint64_ok AQ L ar C (HIk D) (NESKA.PMEA L) LY (proj1 (IOKD D)) PO HBS (push_back_f D) (ntb_u16_f D) (ntb_u32_f D) (ntb_u64_f D) (write_timestamp_f D)). Qed.   (* [comment removed for export] *)
Lemma eo_int64_f D : NECSA.v_int64_spec RSEGS AD AQ AAD AE L ar (HIk D) (NESKA.PMEA L).
Proof. exact (PNAENI64.v_int64_ok AQ L ar C (HIk D) (NESKA.PMEA L) LY (proj1 (IOKD D)) PO HBS (push_back_f D) (ntb_u16_f D) (ntb_u32_f D) (ntb_u64_f D) (ntb_i16_f D) (ntb_i32_f D) (ntb_i64_f D)). Qed.   (* [comment removed for export] *)
Lemma eo_double_f D : NECSA.v_double_spec RSEGS AD AQ AAD AE L ar (HIk D) (NESKA.PMEA L).
Proof. exact (PNAENCD.v_double_ok AQ L ar C (HIk D) (NESKA.PMEA L) LY (proj1 (IOKD D)) PO HBS (push_back_f D) (ntb_f32_f D) (ntb_f64_f D)). Qed.   (* [comment removed for export] *)
Lemma eo_key_f D : NECSA.v_key_spec RSEGS AD AQ AAD AE L ar (HIk D) (NESKA.PMEA L).
Proof. exact (PNAENK.v_key_ok AQ L ar C (HIk D) (NESKA.PMEA L) LY (proj1 (IOKD D)) PO HBS (wsv_f D)). Qed.   (* [comment removed for export] *)
Lemma eo_bstr_tag_f D : NECSA.v_bstr_tag_spec RSEGS AD AQ AAD AE L ar (HIk D) (NESKA.PMEA L).
Proof. exact (PNAENBT.v_bstr_tag_ok AQ L ar C (HIk D) (NESKA.PMEA L) LY (proj1 (IOKD D)) PO HBS (push_back_f D) (ntb_u16_f D) (ntb_u32_f D)). Qed.   (* [comment removed for export] *)
Lemma eo_bstr_raw_f D : NECSA.v_bstr_raw_spec RSEGS AD AQ AAD AE L ar (HIk D) (NESKA.PMEA L).
Proof. exact (PNAENBR.v_bstr_raw_ok AQ L ar C (HIk D) (NESKA.PMEA L) LY (proj1 (IOKD D)) PO HBS (push_back_f D) (ntb_u16_f D) (ntb_u32_f D)). Qed.   (* [comment removed for export] *)
Lemma eo_begin_arr_f D : NECSA.v_begin_arr_spec RSEGS AD AQ AAD AE L ar (HIk D) (NESKA.PMEA L).
Proof. exact (PNAENBGA.v_begin_arr_ok AQ L ar C (HIk D) (NESKA.PMEA L) LY (proj1 (IOKD D)) PO HBS (push_back_f D) (ntb_u16_f D) (ntb_u32_f D) (epush_cont_f D)). Qed.   (* [comment removed for export] *)
Lemma eo_begin_obj_f D : NECSA.v_begin_obj_spec RSEGS AD AQ AAD AE L ar (HIk D) (NESKA.PMEA L).
Proof. exact (PNAENBGO.v_begin_obj_ok AQ L ar C (HIk D) (NESKA.PMEA L) LY (proj1 (IOKD D)) PO HBS (push_back_f D) (ntb_u16_f D) (ntb_u32_f D) (epush_cont_f D)). Qed.   (* [comment removed for export] *)
Lemma eo_end_arr_f D : NECSA.v_end_arr_spec RSEGS AD AQ AAD AE L ar (HIk D) (NESKA.PMEA L).
Proof. exact (PNAENDGA.v_end_arr_ok AQ L ar C (HIk D) (NESKA.PMEA L) LY (proj1 (IOKD D)) PO (make_ec_c (HIk D) (IOKD D)) (PEAEKAN.ann_shrink_e_ok L ar C (HIk D) LY (proj1 (IOKD D)) (proj1 (proj2 (proj2 (IOKD D)))))). Qed.   (* [comment removed for export] *)
Lemma eo_end_obj_f D : NECSA.v_end_obj_spec RSEGS AD AQ AAD AE L ar (HIk D) (NESKA.PMEA L).
Proof. exact (PNAENDGO.v_end_obj_ok AQ L ar C (HIk D) (NESKA.PMEA L) LY (proj1 (IOKD D)) PO (make_ec_c (HIk D) (IOKD D)) (PEAEKAN.ann_shrink_e_ok L ar C (HIk D) LY (proj1 (IOKD D)) (proj1 (proj2 (proj2 (IOKD D)))))). Qed.   (* [comment removed for export] *)
Lemma eo_flush_f D : NECSA.v_flush_spec RSEGS AD AQ AAD AE L ar (HIk D) (NESKA.PMEA L).
Proof. exact (PNAENCF.v_flush_ok AQ L ar C (HIk D) (NESKA.PMEA L) LY (proj1 (IOKD D))). Qed.   (* [comment removed for export] *)
(* [comment removed for export] *)
Lemma tsnz_f D : NETSAa.tsnz_spec L ar (HIk D).
Proof. exact (PQATNZ.tsnz_ok L ar C (HIk D) LY (proj1 (IOKD D))). Qed.   (* [comment removed for export] *)
Lemma divE_f D : NETSAa.divE_spec L ar (HIk D).
Proof. exact (PQATDVE.divE_ok L ar C (HIk D) LY (proj1 (IOKD D))). Qed.   (* [comment removed for export] *)
Lemma mul10i_f D : NETSAa.mul10i_spec L ar (HIk D).
Proof. exact (PQATMUC.mul10i_ok L ar C (HIk D) LY (proj1 (IOKD D))). Qed.   (* [comment removed for export] *)
Lemma add64c_f D : NETSAa.add64c_spec L ar (HIk D).
Proof. exact (PQATADC.add64c_ok L ar C (HIk D) LY (proj1 (IOKD D))). Qed.   (* [comment removed for export] *)
Lemma resizeD3_f D : NETSAa.resizeD3_spec L ar (HIk D).
Proof. exact (PQATRZD3.resizeD3_ok L ar C (HIk D) LY (proj1 (IOKD D))). Qed.   (* [comment removed for export] *)
Lemma mul10d_f D : NETSAa.mul10d_spec L ar (HIk D).
Proof. exact (PQATMUD.mul10d_ok L ar C (HIk D) LY (proj1 (IOKD D))). Qed.   (* [comment removed for export] *)
Lemma add64d_f D : NETSAa.add64d_spec L ar (HIk D).
Proof. exact (PQATADD.add64d_ok L ar C (HIk D) LY (proj1 (IOKD D))). Qed.   (* [comment removed for export] *)
Lemma mul10g_f : NETSAa.mul10g_spec L ar HIk LR.
Proof. exact (PQATMUG.mul10g_ok L ar C LR HIk LY (proj1 FAM)). Qed.   (* [comment removed for export] *)
Lemma add64g_f : NETSAa.add64g_spec L ar HIk LR.
Proof. exact (PQATADG.add64g_ok L ar C LR HIk LY (proj1 FAM)). Qed.   (* [comment removed for export] *)
Lemma tobE_f : NETSAa.tob_spec L ar HIk LR.
Proof. exact (PNAETOB.tob_ok L ar C LR HIk LY (proj1 FAM) mul10i_f add64c_f mul10g_f add64g_f mul10d_f add64d_f). Qed.   (* [comment removed for export] *)
Lemma eo_string_f : NECSA.v_string_specF RSEGS AD AQ AAD AE L ar HIk (NESKA.PMEA L) tspE.
Proof. exact (PNAENST.v_string_okF AQ L ar C LR HIk (NESKA.PMEA L) LY (proj1 FAM) PO HBS wsv_f write_timestamp_f (fun D => make_ec_c _ (IOKD D)) tsnz_f divE_f tobE_f). Qed.   (* [comment removed for export] *)
(* [comment removed for export] *)
Lemma v_begin_array_f D : PNVA.v_begin_array_spec RSEGS AD AQ AAD AE L ar (HIk D).
Proof. exact (PQAABA.begin_array_ok L ar C IL (HIk D) LY (proj1 (IOKD D)) (proj1 (proj2 (IOKD D))) ILY (spbC_A_f D) (PQSAXL.lvpush_any_live _ _ _ _ _ _ (lvpush_any_c (HIk D) (IOKD D))) (eo_begin_arr_f D)). Qed.   (* [comment removed for export] *)
Lemma v_begin_object_f D : PNVA.v_begin_object_spec RSEGS AD AQ AAD AE L ar (HIk D).
Proof. exact (PQAABO.begin_object_ok L ar C IL (HIk D) LY (proj1 (IOKD D)) (proj1 (proj2 (IOKD D))) ILY (spbC_A_f D) (PQSAXL.lvpush_any_live _ _ _ _ _ _ (lvpush_any_c (HIk D) (IOKD D))) (eo_begin_obj_f D)). Qed.   (* [comment removed for export] *)
Lemma v_end_array_f D : PNVA.v_end_array_spec RSEGS AD AQ AAD AE L ar (HIk D).
Proof. exact (PQAAEA.end_array_ok L ar C IL (HIk D) LY (proj1 (IOKD D)) (proj1 (proj2 (IOKD D))) ILY (spbC_A_f D) (PQAALN.ann_shrink_lv_ok L ar C (HIk D) LY (proj1 (IOKD D)) (proj1 (proj2 (proj2 (IOKD D))))) (eo_key_f D) (eo_end_arr_f D)). Qed.   (* [comment removed for export] *)
Lemma v_end_object_f D : PNVA.v_end_object_spec RSEGS AD AQ AAD AE L ar (HIk D).
Proof. exact (PQAAEO.end_object_ok L ar C IL (HIk D) LY (proj1 (IOKD D)) (proj1 (proj2 (IOKD D))) ILY (spbC_A_f D) (PQAALN.ann_shrink_lv_ok L ar C (HIk D) LY (proj1 (IOKD D)) (proj1 (proj2 (proj2 (IOKD D))))) (eo_key_f D) (eo_end_obj_f D)). Qed.   (* [comment removed for export] *)
Lemma v_uint64_f D : PNVA.v_uint64_spec RSEGS AD AQ AAD AE L ar (HIk D).
Proof. exact (PQAAU6.uint64_ok L ar C IL (HIk D) LY (proj1 (IOKD D)) (proj1 (proj2 (IOKD D))) ILY (spbC_A_f D) (fromuC_A_f D) (sinsC_A_f D) (eo_uint64_f D) (eo_key_f D)). Qed.   (* [comment removed for export] *)
Lemma v_int64_f D : PNVA.v_int64_spec RSEGS AD AQ AAD AE L ar (HIk D).
Proof. exact (PQAAI6.int64_ok L ar C IL (HIk D) LY (proj1 (IOKD D)) (proj1 (proj2 (IOKD D))) ILY (spbC_A_f D) (fromiC_A_f D) (sinsC_A_f D) (eo_int64_f D) (eo_key_f D)). Qed.   (* [comment removed for export] *)
Lemma v_double_f D : PNVA.v_double_spec RSEGS AD AQ AAD AE L ar (HIk D).
Proof. exact (PQAADB.double_ok L ar C IL (HIk D) LY (proj1 (IOKD D)) (proj1 (proj2 (IOKD D))) ILY (spbC_A_f D) (VASOPC.wd_ok L ar C (HIk D) LY (proj1 (IOKD D)) IL (proj1 (proj2 (IOKD D))) ILY (spbC_A_f D) (WASB.snprintf_okA L) WATB.strtod_okA (VALEDN.ERRNO_CW L C LY) (VALEDN.snp_rt_of L ar C IL (HIk D) LY (proj1 (IOKD D)) (proj1 (proj2 (IOKD D))) ILY SNPC)) (sinsC_A_f D) (eo_double_f D) (eo_key_f D)). Qed.   (* [comment removed for export] *)
Lemma v_null_f D : PNVA.v_null_spec RSEGS AD AQ AAD AE L ar (HIk D).
Proof. exact (PQAANL.null_ok L ar C IL (HIk D) LY (proj1 (IOKD D)) (proj1 (proj2 (IOKD D))) ILY (spbC_A_f D) (sjnsC_A_f D) (sinsC_A_f D) (eo_null_f D) (eo_key_f D)). Qed.   (* [comment removed for export] *)
Lemma v_bool_f D : PNVA.v_bool_spec RSEGS AD AQ AAD AE L ar (HIk D).
Proof. exact (PQAABL.bool_ok L ar C IL (HIk D) LY (proj1 (IOKD D)) (proj1 (proj2 (IOKD D))) ILY (spbC_A_f D) (sjnsC_A_f D) (sinsC_A_f D) (eo_bool_f D) (eo_key_f D)). Qed.   (* [comment removed for export] *)
Lemma v_bstr_tag_f D : PNVA.v_bstr_tag_spec RSEGS AD AQ AAD AE L ar (HIk D).
Proof. exact (PQAABT.bstr_tag_ok L ar C IL (HIk D) LY (proj1 (IOKD D)) (proj1 (proj2 (IOKD D))) ILY (spbC_A_f D) (b64C_A_f D) (sinsC_A_f D) (eo_bstr_tag_f D) (eo_key_f D)). Qed.   (* [comment removed for export] *)
Lemma v_bstr_raw_f D : PNVA.v_bstr_raw_spec RSEGS AD AQ AAD AE L ar (HIk D).
Proof. exact (PQAABR.bstr_raw_ok L ar C IL (HIk D) LY (proj1 (IOKD D)) (proj1 (proj2 (IOKD D))) ILY (spbC_A_f D) (b64C_A_f D) (sinsC_A_f D) (eo_bstr_raw_f D) (eo_key_f D)). Qed.   (* [comment removed for export] *)
Lemma v_flush_f D : PNVA.v_flush_spec RSEGS AD AQ AAD AE L ar (HIk D).
Proof. exact (PQAAFL.flush_ok L ar C IL (HIk D) LY (proj1 (IOKD D)) (proj1 (proj2 (IOKD D))) ILY (eo_flush_f D)). Qed.   (* [comment removed for export] *)
Lemma v_string_f : PNVA.v_string_specF RSEGS AD AQ AAD AE L ar HIk tspV.
Proof. exact (PQAAVS.string_ok L ar C IL LR HIk tspE LY ILY (proj1 FAM) (fun D => proj1 (proj2 (IOKD D))) TSNN TSANTI (fun D => spbC_A_f D) (fun D => sjnsC_A_f D) (fun D => eo_key_f D) eo_string_f). Qed.   (* [comment removed for export] *)
(* [comment removed for export] *)
Lemma get_size_c HI (IOK : inst_ok HI) : PNRNA.get_size_spec RSEGS AD AQ AAD AE L ar HI.
Proof. exact (PQAGS.get_size_ok L ar C HI LY (proj1 IOK) (src_read_c HI IOK) (make_ec_c HI IOK)). Qed.   (* [comment removed for export] *)
Lemma begin_array_f D : PNRNA.begin_array_spec RSEGS AD AQ AAD AE L ar (HIk D).
Proof. exact (PQABA.begin_array_ok L ar C (HIk D) IL LY (proj1 (IOKD D)) (proj1 (proj2 (IOKD D))) ILY (get_size_c (HIk D) (IOKD D)) (make_ec_c (HIk D) (IOKD D)) (push_cont_c (HIk D) (IOKD D)) (v_begin_array_f D)). Qed.   (* [comment removed for export] *)
Lemma begin_object_f D : PNRNA.begin_object_spec RSEGS AD AQ AAD AE L ar (HIk D).
Proof. exact (PQABO.begin_object_ok L ar C (HIk D) IL LY (proj1 (IOKD D)) (proj1 (proj2 (IOKD D))) ILY (get_size_c (HIk D) (IOKD D)) (make_ec_c (HIk D) (IOKD D)) (push_cont_c (HIk D) (IOKD D)) (v_begin_object_f D)). Qed.   (* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mulu_f D : PQATSSa.mulu_spec L ar (HIk D).
Proof. exact (PQATML.mulu_ok L ar C (HIk D) LY (proj1 (IOKD D))). Qed.   (* [comment removed for export] *)
Lemma add64_f D : PQATSSa.add64_spec L ar (HIk D).
Proof. exact (PQATAD.add64_ok L ar C (HIk D) LY (proj1 (IOKD D))). Qed.   (* [comment removed for export] *)
Lemma ws1_A_f D : PQATSSa.ws1_spec L ar (HIk D).
Proof. exact (PQATWS.ws1_ok L ar C IL (HIk D) LY (proj1 (IOKD D)) (proj1 (proj2 (IOKD D))) ILY (opnew_c (HIk D) (IOKD D))). Qed.   (* [comment removed for export] *)
Lemma lt0_f D : PQATSS2a.lt0_spec L ar (HIk D).
Proof. exact (PQATLT.lt0_ok L ar C (HIk D) LY (proj1 (IOKD D))). Qed.   (* [comment removed for export] *)
Lemma addu21_f D : PQATSS2a.addu21_spec L ar (HIk D).
Proof. exact (PQATAU.addu21_ok L ar C (HIk D) LY (proj1 (IOKD D))). Qed.   (* [comment removed for export] *)
Lemma addu22_f : PQATSS2a.addu22_spec L ar HIk LR.
Proof. exact (PQATAU2.addu22_ok L ar C LR HIk LY (proj1 FAM)). Qed.   (* [comment removed for export] *)
Lemma subbig1_f D : PQATSS2a.subbig1_spec L ar (HIk D).
Proof. exact (PQATSB1.subbig1_ok L ar C (HIk D) LY (proj1 (IOKD D))). Qed.   (* [comment removed for export] *)
Lemma subbig2_f : PQATSS2a.subbig2_spec L ar HIk LR.
Proof. exact (PQATSB2.subbig2_ok L ar C LR HIk LY (proj1 FAM)). Qed.   (* [comment removed for export] *)
Lemma ws2i_A_f D : PQATSW2a.ws2i_spec L ar (HIk D).
Proof. exact (PQATWS2.ws2i_ok L ar C IL (HIk D) LY (proj1 (IOKD D)) (proj1 (proj2 (IOKD D))) ILY (opnew_c (HIk D) (IOKD D)) (opdel_c (HIk D) (IOKD D))). Qed.   (* [comment removed for export] *)
Lemma ws2d_A_f : PQATSW2a.ws2d_spec L ar HIk (fun D _ r RC => tswe D r RC).
Proof. exact (PQATWS2D.ws2d_ok L ar C IL LR HIk LY (proj1 FAM) ILY (fun D => proj1 (proj2 (IOKD D))) (fun D => opnew_c (HIk D) (IOKD D)) (fun D => opdel_c (HIk D) (IOKD D))). Qed.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma VALF_A_c HI (IOK : inst_ok HI) : PECVSA.validate_fun_spec RSEGS AD L ar HI (pa_validate AD).
Proof. exact (PECVALAR.validate_fun_ok L ar C HI LY (proj1 IOK) (proj2 (proj2 (proj2 IOK)))). Qed.   (* [comment removed for export] *)
Lemma read_item_f : PQRAR.read_item_specFR L ar HIk tsp.
Proof. exact (PQARI.read_item_okF L ar C IL LR HIk tsp TSRESA LY (proj1 FAM) (fun D => proj1 (proj2 (IOKD D))) ILY TSP_LE tspV (fun D => conj (src_read_c _ (IOKD D)) (conj (make_ec_c _ (IOKD D)) (conj (begin_array_f D) (conj (begin_object_f D) (conj (v_uint64_f D) (conj (v_int64_f D) (conj (v_double_f D) (conj (v_null_f D) (conj (v_bool_f D) (conj (get_size_c _ (IOKD D)) (conj (read_span_v_c _ (IOKD D)) (conj (v_bstr_tag_f D) (conj (v_bstr_raw_f D) (VALF_A_c _ (IOKD D))))))))))))))) v_string_f TSP_V (PQARIT8.TS8A_ok L ar C IL LR HIk tsp TSRESA tspV v_string_f TSP_V mulu_f add64_f ws1_A_f) (PQARIT12.TS12A_ok L ar C IL LR HIk tswe tspV PQATSTW.TSWMAX TSPVMAX TSRESA LY TSWE TSPV_OK RESGE v_string_f mulu_f lt0_f addu21_f addu22_f subbig1_f subbig2_f ws1_A_f ws2i_A_f ws2d_A_f)). Qed.   (* [comment removed for export] *)
Lemma parse_f : PNRNA.parse_specF RSEGS AD AQ AAD AE L ar HIk TSRESA.
Proof. exact (PQALP2.parse_ok L ar C IL LR HIk tsp TSRESA LY (proj1 FAM) (fun D => proj1 (proj2 (IOKD D))) ILY TSP_LE (fun D => proj1 (proj2 (proj2 (IOKD D)))) read_item_f v_end_array_f v_end_object_f v_flush_f). Qed.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ledger_rowsA (D : list (list Z)) : Prop :=
  NESKA.push_back_specA RSEGS AD AE L ar (HIk D) (NESKA.PMEA L) /\ NECSA.v_null_spec RSEGS AD AQ AAD AE L ar (HIk D) (NESKA.PMEA L)
  /\ NECSA.v_string_specF RSEGS AD AQ AAD AE L ar HIk (NESKA.PMEA L) tspE /\ PNVA.v_uint64_spec RSEGS AD AQ AAD AE L ar (HIk D)
  /\ PNVA.v_string_specF RSEGS AD AQ AAD AE L ar HIk tspV /\ PQRAR.read_item_specFR L ar HIk tsp /\ PNRNA.parse_specF RSEGS AD AQ AAD AE L ar HIk TSRESA
  /\ PQRAa.reset_spec L ar (HIk D) /\ PQRAa.reader_ctor_spec L ar (HIk D) /\ PQRAa.reader_dtor_spec L ar (HIk D).
Lemma ledger_rowsA_ok D : ledger_rowsA D.
Proof.
  exact (conj (push_back_f D) (conj (eo_null_f D) (conj eo_string_f (conj (v_uint64_f D) (conj v_string_f (conj read_item_f (conj parse_f
        (conj (reset_c _ (IOKD D)) (conj (reader_ctor_c _ (IOKD D)) (reader_dtor_c _ (IOKD D))))))))))).
Qed.

(* [comment removed for export] *)
Record harness_depsA : Prop := HDEPSA {
  hda_str_ctor : forall D, PMA.str_ctor_spec L ar (HIk D);
  hda_iss_ctor : forall D, PMA.iss_ctor_spec L ar (HIk D);
  hda_reader_ctor : forall D, PQRAa.reader_ctor_spec L ar (HIk D);
  hda_syscat : forall D, PMA.syscat_spec L ar (HIk D);
  hda_reset : forall D, PQRAa.reset_spec L ar (HIk D);
  hda_parse : PNRNA.parse_specF RSEGS AD AQ AAD AE L ar HIk TSRESA;
  hda_reader_dtor : forall D, PQRAa.reader_dtor_spec L ar (HIk D);
  hda_opdel : forall D, PMA.opdel_spec L ar (HIk D);
  hda_locale_dtor : forall D, PMA.locale_dtor_spec L ar (HIk D);
  hda_ios_dtor : forall D, PMA.ios_dtor_spec L ar (HIk D)
}.
Theorem deps_closed : harness_depsA.
Proof.
  exact (HDEPSA (fun D => str_ctor_c _ (IOKD D)) (fun D => iss_ctor_c _ (IOKD D)) (fun D => reader_ctor_c _ (IOKD D)) (fun D => syscat_c _ (IOKD D))
                (fun D => reset_c _ (IOKD D)) parse_f (fun D => reader_dtor_c _ (IOKD D)) (fun D => opdel_c _ (IOKD D)) (fun D => locale_dtor_c _ (IOKD D))
                (fun D => ios_dtor_c _ (IOKD D))).
Qed.

(* [comment removed for export] *)
Lemma cr_nonneg D LB FF LK cr A M V : ri_inv (HIk D) LB FF LK cr A M V -> 0 <= fst cr /\ 0 <= snd cr.
Proof.
  intros H. pose proof (HAJ.aior_wf _ _ _ _ _ (proj1 (IOKD D)) _ _ _ _ _ _ _ H) as W.
  destruct W as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C1 & C2 & _). split; assumption.
Qed.
Lemma weaken0 D LB FF LK cr A M V : ri_inv (HIk D) LB FF LK cr A M V -> ri_inv (HIk []) LB FF LK cr A M V.
Proof.
  intros H. destruct (cr_nonneg _ _ _ _ _ _ _ _ H) as [C1 C2].
  apply (HAR.fr_weaken _ _ _ _ _ _ (proj1 FAM) [] D LB FF LK cr cr A M V H); [intros x Hx; destruct Hx| lia | lia].
Qed.
Theorem parse_0 : PNRNA.parse_specF RSEGS AD AQ AAD AE L ar (fun _ => HIk []) TSRESA.
Proof.
  unfold PNRNA.parse_specF.
  intros fx R M model K LBX FF LK Aw cr sp r fb cat n s st str sm e D HH AM K0 ENT FRM FRS SP16 FOK ARGS PRE INC MINV ROOM CRED KONT.
  apply (parse_f fx R M model K LBX FF LK Aw cr sp r fb cat n s st str sm e [] HH AM K0 ENT FRM FRS SP16 FOK ARGS PRE INC MINV ROOM CRED).
  intros fx' R' M' model' LK' Aw' s' st' sm' e' b' cr' D' RP PP HP CK MRT IL' IA AM' ID HH'.
  apply (KONT fx' R' M' model' LK' Aw' s' st' sm' e' b' cr' D RP PP HP CK MRT IL' IA AM' (incl_refl D)). exact (weaken0 _ _ _ _ _ _ _ _ HH').
Qed.
(* [comment removed for export] *)
Theorem deps_std : harness_depsS L ar (HIk []) TSRESA.
Proof.
  (* [comment removed for export] *)
  pose proof (conj LY (conj ILY (conj MCC (conj SNPC (conj (TSPE_OK 0 0 [] []) (conj RESGE (conj FAM OPEN))))))) as PIN.
  exact (HDEPSS L ar (HIk []) TSRESA (str_ctor_c _ (IOKD [])) (iss_ctor_c _ (IOKD [])) (reader_ctor_c _ (IOKD [])) (syscat_c _ (IOKD [])) (reset_c _ (IOKD []))
                parse_0 (reader_dtor_c _ (IOKD [])) (opdel_c _ (IOKD [])) (locale_dtor_c _ (IOKD [])) (ios_dtor_c _ (IOKD []))).
Qed.
End Asm.
End SCFG_1.
End NTASMA.

End NTopAsmA.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Module PnAHarnessStmts.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0080. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.LibIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.LibIfaceAB OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMr OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PmLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PmStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutQA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnQStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.PnAImgGap OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104.PnTopS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0080.PnTopAL OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnRunNA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0290.NTopAsmA.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAHarnessStmts () := "C47Corelib7Classes?RelationClasses9ReflexiveK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC56Stdlib6ZArith6BinInt1Z6of_natC45stdpp9bitvector;definitions7Z_to_bvC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z2leC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00c69OSSVerify5KrLib7Mh_0290?PnAHarnessStmts5PQHAS1UC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powK47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_00846L5Defs2L5<unsigned_litC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rI47Corelib7Numbers7BinNums1Z00C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic3and01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c69OSSVerify5KrLib7Mh_0290?PnAHarnessStmts5PQHAS3STKC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3mulK47Corelib4Init9Datatypes4prod01c69OSSVerify5KrLib7Mh_0290?PnAHarnessStmts5PQHAS6CREDITC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndK46Stdlib9micromega5Tauto8GFormula08C59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C46Stdlib5Lists4List2InC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indc69OSSVerify5KrLib7Mh_0290?PnAHarnessStmts5PQHAS4LEAKC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0290?PnAHarnessStmts5PQHAS6FRAMESC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6ff_capC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z3divI47Corelib4Init5Logic5False00I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison01K47Corelib4Init9Datatypes:comparison03K47Corelib4Init9Datatypes:comparison02K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes6option00C56Stdlib6ZArith6BinInt1Z3subc69OSSVerify5KrLib7Mh_0290?PnAHarnessStmts5PQHAS4tfrkC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0290?PnAHarnessStmts5PQHAS6tocellC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C8agree_onC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04C69OSSVerify5KrLib7Mh_00906L5Core3L5C<u64_at_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op205c69OSSVerify5KrLib7Mh_0290?PnAHarnessStmts5PQHAS5rinvHC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02K47Corelib4Init5Logic2or01c69OSSVerify5KrLib7Mh_0290?PnAHarnessStmts5PQHAS4HIDXC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3eqbC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC46Stdlib5Lists4List7existsbI47Corelib4Init5Logic2ex00C46Stdlib5Lists4List>existsb_existsC56Stdlib5Arith8PeanoNat3Nat6eqb_eqc69OSSVerify5KrLib7Mh_0290?PnAHarnessStmts5PQHAS:rinvH_keepC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbC59OSSVerify5KrLib7Mh_00849HeapIface>regs_preservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface@callee_saved_idxC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQHAS.
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Definition U (R : bvmap 5 word) (k : nat) : Z := bv_unsigned (getr R (reg k)).
Lemma UR R k : 0 <= U R k < 2 ^ 64.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAHarnessStmts ()) [] "h01Rh11kh21Xp;1p;2p-1p10000p4p710p9g000\j10Tg001Aj1@Tg001fj12Tg002Dj16Tg002gj2?Tg003Sj1<Tg0043j2;Tg004Yj2:Tg005Kj29Tg006>j27Tg006hj21Tg007Dj18Tg007mj24Tg008Ij25Tg008dj2>Tg009hj13Tg00:Fj2=Tg00:c#0R0#@#2R1%00#0#0#0#0R2#2R3#6'?R4g00;HR5f1R6f0R7#<,;1':R1,93g00;gR81731R1'1%83,41'5P7b21>67R1,18%30%32'=,41'5eX15X04P6P7O2W1W0o"). Qed.
Lemma U_of R k z : getr R (reg k) = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> U R k = z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAHarnessStmts ()) [] "h01Rh11kh21zh31Hh42Hzh51bp;1p;2p;3p;6p-1p10000p4p710p9g000\j10Tg001Aj1ATg001fj14Tg002Dj17Tg002gj2@Tg003Sj16Tg0043j21Tg004Yj23Tg00<Ej32Tg006hj28Tg009hj15Tg00:Fj29Tg007mj2:Tg008Ij2?Tg006>j2>Tg00<_j2<Tg00=bj6;Tg008dj2=Tg00:c#0R0#A#4R1%00#0#0#0#0R2#4R3#7R4'@R5g00;HR6g00>@R7f2R8f1R9#6,11'3f0R:,13524g00;g/89%50%52'9,:9'?P411381>3:f3R3527X541<8:f4R4%63,11'3P9E;1=43=278eW4W3X27X16X05P8P9P:O3W2W1W0o"). Qed.
Lemma U_to R k : getr R (reg k) = Z_to_bv 64 (U R k).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAHarnessStmts ()) [] "h01Rh11kp;1p;2p;4p;3p-1p10000p4p710p9g000\j10Tg001Aj1<Tg001fj12Tg002Dj13Tg002gj2;Tg003Sj1:Tg0043j21Tg004Yj24Tg006>j25Tg00>^j26Tg00?Pj47Tg008dj28Tg00<Ej39Tg00:c#0R0#<#2R1%00#0#0#0#0#2R0#3R2';R3g00;HR4P2f1R5f0R6#:,11'4R1,50,10P11601C71856,109921eX14X03P5P6O2W1W0o"). Qed.

(* [comment removed for export] *)
Definition STK : Z := 36864.                          (* [comment removed for export] *)
Definition FRAMES (k : Z) : Z := 14.                  (* [comment removed for export] *)
Definition LEAK (k : Z) : Z := 0.
Definition CREDIT (RES : credit) (n : Z) : credit := (1320 + fst RES, 12 * 2 ^ 30 + 8 * n + snd RES).      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition LayA (RES : credit) (L : asan_layout) : lib_layoutA := PNTAL.TopLayA_a STK FRAMES LEAK (CREDIT RES) L.
(* [comment removed for export] *)
Lemma STK_ok : 4096 <= STK <= 2 ^ 20 /\ STK mod 8 = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAHarnessStmts ()) [] "h02Hah17__arithh24__ffh36__sat0h46__sat1h58__varmaph65__witp;1p;2p;3p;4p;7p-1p10000p4p710p9g000\j10Tg009hj12Tg001Aj17Tg006hj21Tg00:Fj2DTg008Ij25Tg00?lj2<Tg00<Ej36Tg00@Lj2>Tg007mj29Tg00A4j3=Tg00AXj1NTg00B8j1MTg00BXj1LTg00C6j1HTg00CTj1FTg00D?j24Tg00Dbj4:Tg001fj1CTg00EMj3BTg00F0j7ATg00FTj2ETg00G6j2;Tg00GPj2@Tg00H<j3GTg00H[j4?Tg00IMj4JTg00Ihj7KTf0R0#0#0#0#0p=3%00#0p=If1R1g00JLR2g00JkR3P3g00KKR4P0g00KkFKp=8g00:c#0R5#0R6#0R7#0#3#3#2R8%76#3#3#3#2R6'1%25R9%75#IR5#2R:'DR;,16'5R<g00>@R=%27R7,<6g00;gR>361>9:19>911>:19>;[[11>9R?g00LKR@A=9:1UW011>;\@^0?g00LgR?#N%M?%L=%H=%F=R?P2P3P3P4P=14=8g00MSR314=6R6C:,8?P=P6P314=9%C55B=C:,8?FA1E?4P0f2R?g00N:R4g00NZR5';1@0?=645dAG=>1C?b2b5b6P<P0b1b3b41;=>CJg00O:R0,18110;'51<07=6=>'5eo"). Qed.
Lemma CREDIT_ok (RES : credit) : 0 <= fst RES -> 0 <= snd RES -> forall n, 0 <= n -> 0 <= fst (CREDIT RES n) /\ 0 <= snd (CREDIT RES n).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAHarnessStmts ()) [] "h02Hah13RESh24__x1h34__x2h44__x3h52H1h62H2h72Hnh87__arithh94__ffh:6__sat3h;6__sat4h<8__varmaph=5__with>1np;1p;2p;3p;4p;7p;8p-1p10000p4p710p9g000\j11Tg009hj16Tg001Aj13Tg00@Lj2UTg007mj2BTg00:Fj2MTg00A4j3ITg00P@j2HTg00Pij1;Tg00QHj2?Tg00R1j3bTg00RZj3DTg00SCj2]Tg00AXj1YTg00Soj3WTg00B8j1VTg00TOj2CTg00Tmj4TTg00C6j1QTg00CTj1NTg00D?j27Tg00UKj2<Tg00Unj1LTg00VPj3:Tg001fj1JTg00EMj3KTg00W3j3ATg00F0j7GTg00FTj2FTg00G6j2OTg00GPj2PTg00<Ej3ETg00H<j3RTg00H[j4STg00WVj22Tg00X3j2@Tg008Ij2>Tg00XPj4aTg00Y0j2`Tg00Z9j3_Tg006hj2\Tg00ZVj3ZTg00Dbj4[Tg00Ihj7XTg00[3j8^Tg00>@R0f0R17_0p=9g00;gR2/\1p=0AZ001p=8P0f1R3g00MSP1C[p=4P3g00JLR4g00JkR5P5g00KKR6P1g00KkFXp=5f3R7P4P5P5P6f2R8P3P1G^p==g00[WR9%91#0%83#0%01g00:cR:#1R;#6R<%3:R=#3#3#1R>#6R?'U1B2<%0?1M<?R@,B2[[%0<RAg00LKRBAI<?3UW0%0@\B^0Ag00LgRA%1;#1#6RB,H0g00\TR?#;#;RC#;,?05b01?0C1?0?5D05D0g00]3']%YA3W%VAP01C08P31C07CT%Q0%N0RA1702R?1<0;RC'4,5A%L5RDPA1<0=RE,4?,5APDPA1<0:R:,4?,5APDPAP4P5P5P6%3;#1#1#3#1#3#1#1#1#6R;,70=:0:,4?,5A%1=#1#6R=,70170<%J>5K05A0170B=A0C5:0=:0E,4?,5AFGC=C=C=1FA6P1P8g00N:RAg00NZR6'O1P18=EA6dAR023CSb9b<b=X20X30X40%03%07%0812;7#01@=@R=f4R@,@B'2f5R8'2#0'>[[[^20^30^40P1f7R2#8P@%92P7P8f6O6b8b:b;P0P0%9@,2;1@B3,2=%8@'2CaR=#9#0%8=#0'>e1`@3R@#9#0%8@#0'>eW7X>0W6W5X19P1O1W1o"). Qed.
Lemma FRAMES_ok : forall k, In k [0; 1; 2; 3; 4; 5] -> 0 <= LEAK k /\ 4 * LEAK k + FRAMES k <= ff_cap k.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAHarnessStmts ()) [] "p'0h01Hh11xh21eh31kh42Hki001cp;1p;3p;2p;6p;4p-1p10000p4p710p9g009hj15Tg000\j13Tg001Aj1=Tg00AXj1ATg00Soj38Tg00]_j3HTg00<Ej32Tg006hj2:Tg00X3j2<Tg00WVj2?Tg00:Fj2>Tg00^6j66Tg00^Rj2ITg00IMj4GTg00_1j1FTg00`8j1ETg00aAj1DTg00b?R0j29Tg00bYj2BTg008Ij2@Tg00>@R1f1R2f0R332g00c6R4'9p=7f4R5f3R6521f2R7=212/93'9p=4f5R81>23,<7,B6,:5'@p=0A2123p=1A2167A2123/94'9p=;1:23,@7p=Cg00;gR9g00:cR:#5R;%3:R<#5R=%=:R:#5R>%3<R?#5R@%=<R<#5RA%A15815815815815815819H13P0A2192P;P2P=P2P>P2P@P217A2D4D41:99RB1<@9%=:#3#5'?R:%3<#3#5,>=R<%3?#3#3#3#5R?P=P7E0P3A2197P1P9PBP:P<P?P=P3E0X31RCg00cSRDg00d9REg00d_RF32RGP4]1g00eERH=2DFRIP4]1PDPEPDp-0REP3g00LKRJP4P4n011000003000000X2Dg00ekRKPFP3E6P41I43RLb0X1GPDPHPDPEP3P4PJP4n011000003000000X2DPKPFP3E6P4PLb0X1ICGRIPBP:P<P?P=P9E0dP6P3E6W0P3O1P;P7P=P7P>P7P@P717A7D4D4P011;6P=P6P>P6P@P6PAP6C;D4PBP:P<P?P=P5E0P311;5P1P;PCPIPBP:P<P?P=P;E0dP8P3E6W0P3O1P=P5P>P5P@P5PAP5C;D4P011=8P>P8P@P817A8D4PBP:P<P?P=f6R8E0P311=8P1P=PCPIPBP:P<P?P=P=E0df7R5P3E6W0P3O1P>P8P@P817A8D4P011>5P@P5PAP5C;PBP:P<P?P=f8R5E0P311>5P1P>PCPIPBP:P<P?P=P>E0df9R>P3E6W0P3O1P@P5PAP5C;P011@>17A>PBP:P<P?P=f:R>E0P311@>P1P@PCPIPBP:P<P?P=P@E0df;R5P3E6W0P3O117A>P011A5P4PBP:P<P?P=f<R5E0P311A5P1PAPCPIPBP:P<P?P=PAE0df=P3E6W0P3O1P4PBP:P<P?P=f>E0P3n010000000X04P3O1n200100000021000010000W0P3O1n200100000021000011000W0P3O1n200100000021000011000W0P3O1n200100000021000011000W0P3O1n200100000021000011000W0P3O1n200100000021000011000%F2R3,:91<@3%E2'?%D23CeW4X31o"). Qed.

(* [comment removed for export] *)
Definition tfrk (S : Z) (R : bvmap 5 word) (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (S - 8) (U R 1) /\ L5.u64_at RSEGS M (S - 16) (U R 8) /\ L5.u64_at RSEGS M (S - 24) (U R 9) /\ L5.u64_at RSEGS M (S - 32) (U R 18) /\
  L5.u64_at RSEGS M (S - 40) (U R 19) /\ L5.u64_at RSEGS M (S - 48) (U R 20) /\ L5.u64_at RSEGS M (S - 56) (U R 21) /\ L5.u64_at RSEGS M (S - 64) (U R 22) /\
  L5.u64_at RSEGS M (S - 72) (U R 23) /\ L5.u64_at RSEGS M (S - 80) (U R 24) /\ L5.u64_at RSEGS M (S - 88) (U R 25) /\ L5.u64_at RSEGS M (S - 96) (U R 26) /\
  L5.u64_at RSEGS M (S - 104) (U R 27).
(* [comment removed for export] *)
Definition tocell (S : Z) (a : Z) : Prop := S - 104 <= a < S.
Lemma tfrk_agree S R M1 M1' : 4096 <= S - 104 -> S <= 2 ^ 47 -> tfrk S R M1 -> (forall a, tocell S a -> M1' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> tfrk S R M1'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAHarnessStmts ()) [] "h04__x1h17__arithh24__ffh36__sat2h46__sat3h58__varmaph65__with74__x2h82Hjh96__sat4h:6__sat5h;1ah<1jh=1Hh>2Hah?2M1h@3M1'hA1RhB1ShC2AGhD2C1hE3C10hF3C11hG3C12hH3C13hI2C2hJ2C3hK2C4hL2C5hM2C6hN2C7hO2C8hP2C9hQ2H0hR2H1hS1xp%0p;1p;2p;3p;4p;7p;8p;9p-1p10000p4p710p9g000\j16Tg001Aj1HTg001fj1NTg002Dj1VTg002gj2tTg00fGj1mTg009hj17Tg00fij21Tg006hj2GTg00:Fj2WTg00gFj3;Tg00Pij19Tg00hMj2@Tg0043j2jTg00<Ej3<Tg008dj28Tg008IR0j2:Tg00@Lj2ZTg007mj2MTg00A4j3YTg00AXj1fTg00B8j1eTg00TOj2XTg00BXj1dTg00Tmj4cTg00C6j1bTg00CTj1aTg00UKj2UTg00Unj1_Tg00FTj2qTg00G6j2pTg00GPj2oTg00H<j3nTg00H[j4lTg00iVj4>Tg00D?j2RTg00EMj3^Tg00jVj4QTg00WVj2]Tg00kSj3\Tg00VPj3hTg00Dbj4KTg00Ihj7LTg00F0j7PTg00[3j8STg00l6l9gTg00IMj4[Tf0R1#6#6p=Fg00m:R2f4R3f3R4f2R5'1f1R6/81CQp=2%91#9p=IP2f5R711341856CQ/:1p=0P2P5P6P1CQp==1G341]61,M5':p=3g00;gR8/G1p=5g00>@R9/R1p=OA\961p=`Ah961p=BP5g00JLR:g00JkR;P;g00KKR<P9P6g00nOR=P1CKg00KkR>FLp=C1R919\96p=DP5P:P;P;P<P9P6g00MSR?P1CKP>FLp=TP9P6P=P1CKp=sP4P:P;P;P<P5P6P:P;P;P<P1P>FLFPp=rf7R@P:P;P;P<f6RAP:P;P;P<P7P:P;P;P<P9P3P?P4CKP>FLP5FPP6P1GSp=E1G56/:1p=kP7P:P;P;P<P3P4P5P:P;P;P<P9P6P?P1CKP>FLGSp=41]56/G1p=AP2P@PAP7P3P4P5P6P1M9gp=?P@P:P;P;P<PAP:P;P;P<P7P3P:P;P;P<P9P4P=P5CKP>FLFPP6P1GSp=iPAP7P3P4P5P6P1C[C[p=Jg00:cR>#6R=#HR:#N%6=R2#6R?#6RB#6RC#6RD#NRE#VRF'tS00%N?#V#mRG\FS01PG^SFS02Q00Q01Q02%FD#F#F#7RF%H>RH#6RI#H#6#F#7RJ,14'G%7=RK%H:RL#H#HS03#7RM'WRN,G3A;734P0P3PA%7?R?P7g00\T#9ROD2P3PA%7BRBP7%9O#I#I#IRPP3PA%FIRI#7RQP7%9PRRP3PA%7CRCP7%9R#I#I#I#IRSP3PA%6:#FR:#7RTP7%9SRUP3PA%6IRI#7RVP7%9URWP3PA%HH#6#F#7RHP7%9WRXP3PA%7DRDP7%9XRYP3PA%H2#6#F#7R2P7%9YRZP3PA%6:#7R:P7%9ZR[P3PA%6L#F#7RLP7%9[R\P3PA%6I#7RIP7%9\R]P3PAPJP7%9]R^D2E0E0E0E0E0E0E0E0E0E0E0f8R_/@1PA1jE6R`O1P@P`O15<G[^;9A;_@7[P1PAP_P?P@POD2P@f9R7PBP_PPP@P7PQP_PRP@P7PCP_PSP@P7PTP_PUP@P7PVP_PWP@P7PHP_PXP@P7PDP_PYP@P7P2P_PZP@P7P:P_P[P@P7PLP_P\P@P7PIP_P]P@P7PJP_P^D2E0E0E0E0E0E0E0E0E0E0E0P0P_f:R@PBP7PPD2P_P@PQP7PRP_P@PCP7PSP_P@PTP7PUP_P@PVP7PWP_P@PHP7PXP_P@PDP7PYP_P@P2P7PZP_P@P:P7P[P_P@PLP7P\P_P@PIP7P]P_P@PJP7P^D2E0E0E0E0E0E0E0E0E0E0f<R_/@1P@P`O1f;RaP`O15<G[^;9A;_a7[P1P@P_PBPaPPD2Paf=R7PQP_PRPaP7PCP_PSPaP7PTP_PUPaP7PVP_PWPaP7PHP_PXPaP7PDP_PYPaP7P2P_PZPaP7P:P_P[PaP7PLP_P\PaP7PIP_P]PaP7PJP_P^D2E0E0E0E0E0E0E0E0E0E0P0P_f>RaPQP7PRD2P_PaPCP7PSP_PaPTP7PUP_PaPVP7PWP_PaPHP7PXP_PaPDP7PYP_PaP2P7PZP_PaP:P7P[P_PaPLP7P\P_PaPIP7P]P_PaPJP7P^D2E0E0E0E0E0E0E0E0E0f@R_/@1PaP`O1f?RbP`O15<G[^;9A;_b7[P1PaP_PQPbPRD2PbfAR7PCP_PSPbP7PTP_PUPbP7PVP_PWPbP7PHP_PXPbP7PDP_PYPbP7P2P_PZPbP7P:P_P[PbP7PLP_P\PbP7PIP_P]PbP7PJP_P^D2E0E0E0E0E0E0E0E0E0P0P_fBRbPCP7PSD2P_PbPTP7PUP_PbPVP7PWP_PbPHP7PXP_PbPDP7PYP_PbP2P7PZP_PbP:P7P[P_PbPLP7P\P_PbPIP7P]P_PbPJP7P^D2E0E0E0E0E0E0E0E0fDR_/@1PbP`O1fCRcP`O15<G[^;9A;_c7[P1PbP_PCPcPSD2PcfER7PTP_PUPcP7PVP_PWPcP7PHP_PXPcP7PDP_PYPcP7P2P_PZPcP7P:P_P[PcP7PLP_P\PcP7PIP_P]PcP7PJP_P^D2E0E0E0E0E0E0E0E0P0P_fFRcPTP7PUD2P_PcPVP7PWP_PcPHP7PXP_PcPDP7PYP_PcP2P7PZP_PcP:P7P[P_PcPLP7P\P_PcPIP7P]P_PcPJP7P^D2E0E0E0E0E0E0E0fHR_/@1PcP`O1fGRdP`O15<G[^;9A;_d7[P1PcP_PTPdPUD2PdfIR7PVP_PWPdP7PHP_PXPdP7PDP_PYPdP7P2P_PZPdP7P:P_P[PdP7PLP_P\PdP7PIP_P]PdP7PJP_P^D2E0E0E0E0E0E0E0P0P_fJRdPVP7PWD2P_PdPHP7PXP_PdPDP7PYP_PdP2P7PZP_PdP:P7P[P_PdPLP7P\P_PdPIP7P]P_PdPJP7P^D2E0E0E0E0E0E0fLR_/@1PdP`O1fKReP`O15<G[^;9A;_e7[P1PdP_PVPePWD2PefMR7PHP_PXPeP7PDP_PYPeP7P2P_PZPeP7P:P_P[PeP7PLP_P\PeP7PIP_P]PeP7PJP_P^D2E0E0E0E0E0E0P0P_fNRePHP7PXD2P_PePDP7PYP_PeP2P7PZP_PeP:P7P[P_PePLP7P\P_PePIP7P]P_PePJP7P^D2E0E0E0E0E0fPR_/@1PeP`O1fORfP`O15<G[^;9A;_f7[P1PeP_PHPfPXD2PffQR7PDP_PYPfP7P2P_PZPfP7P:P_P[PfP7PLP_P\PfP7PIP_P]PfP7PJP_P^D2E0E0E0E0E0P0P_fRRfPDP7PYD2P_PfP2P7PZP_PfP:P7P[P_PfPLP7P\P_PfPIP7P]P_PfPJP7P^D2E0E0E0E0fTR_/@1PfP`O1fSRgP`O15<G[^;9A;_g7[P1PfP_PDPgPYD2PgfUR7P2P_PZPgP7P:P_P[PgP7PLP_P\PgP7PIP_P]PgP7PJP_P^D2E0E0E0E0P0P_fVRgP2P7PZD2P_PgP:P7P[P_PgPLP7P\P_PgPIP7P]P_PgPJP7P^D2E0E0E0fXR_/@1PgP`O1fWRhP`O15<G[^;9A;_h7[P1PgP_P2PhPZD2PhfYR7P:P_P[PhP7PLP_P\PhP7PIP_P]PhP7PJP_P^D2E0E0E0P0P_fZRhP:P7P[D2P_PhPLP7P\P_PhPIP7P]P_PhPJP7P^D2E0E0f\R_/@1PhP`O1f[RiP`O15<G[^;9A;_i7[P1PhP_P:PiP[D2Pif]R7PLP_P\PiP7PIP_P]PiP7PJP_P^D2E0E0P0P_f^RiPLP7P\D2P_PiPIP7P]P_PiPJP7P^D2E0f`R_/@1PiP`O1f_RjP`O15<G[^;9A;_j7[P1PiP_PLPjP\D2PjfaR7PIP_P]PjP7PJP_P^D2E0P0P_fbR0PIP7P]D2P_P0PJP7P^D2fdR_/@1P0P`O1fcRjP`O15<G[^;9A;_j7[P1P0P_PIPjP]D2PjfeRjPJP_P^D2fgR0/@1PjP`O1ffR7P`O15<G[^;9110?RG187ORO5=_110BR`187PS045=_S05110QRP187RS065=_S07110CRR187SS085=_S09110TRS187US0:5=_S0;110VRU187WS0<5=_S0=110HRW187XS0>5=_S0?110DRX187YS0@5=_S0A1102RY187ZS0B5=_S0C110:RZ187[S0D5=_S0E110LR[187\S0F5=_S0G110IS0H187]S0I5=_S0J110JS0K187^S0L5=_S0M':S0N':S0O':S0P':S0Q':S0R':S0S':S0T':S0U':S0V':S0W':PjP_PGPOfhRO/1?R^P1P1P^P?D3P5P61ZKMR^1M8KR]%5M1M8N[[R\%5KRkg00LKRlAYKM6UW>RM%5N\l^>kRmg00LgRn#fRo%enRnP91X95P6%d9CcRp%b9Rq%a9RrPrPr1U9>R>%O?Rs'`Rt1U9=R=1BtsS0X9Cr=%_;R;Pr1D>JRu=Tr=S0YPr1s=>CrRvGE1qr<R<P1P5g00N:Rwg00NZRx'p1o15=<wxdAn986ClRxb2b5b6X09X79111?RwP6P6PwP?D3116JRw1M567k5Ry[^09^79P1P3flS0ZP4O3R3b1b3b4O2W8X<9PjP_PGP?C>eP^P\PMPmPoPn1X96RGPqPr%OF=TruRzP;Pr1R98R{PtE4P<Pxb2b5b6X09111JS0[,GFRF116?Rt#5[^09P1fjP7O2R|b1b3b4P^P\PMPm1ZKDR}%5D1WKDR~,M8[\]R]AYKD6VlX>kR8%5~\l^>kRkPoPnPGPqPr%OKRKQ03#N5^99Tr>RlP;PrQ0XA^9KERKE4P<Pxb2b5b6X091G1NRNAAt?~[^09P1Q0ZP0O2Rtb1b3b4b9b:PiG?Q05Q0WPjP_P`Q0411OBRiP1P1PiP?D3P5P6P^P\PMPmPoPnPpPqPrPrPr1D>BRiP=1BisS049Cr=P;PvGEP<Pxb2b5b6X09X79111BREP6P6PEP?D3Py[^09^79P3b1b3b4O2W8X<9PjP_P`P?C>eP^P\PMPmPoPnPGPqPrPzP;PrP{PiE4P<Pxb2b5b6X09116BRB#5\F^09P|b1b3b4P^P\PMPmP}P]P8PkPoPnPGPqPrPlP;PrQ04PKE4P<Pxb2b5b6X09AAB?~\N^09Ptb1b3b4b9b:PhG?Q07Q0VPjP_PPQ0611OQRhP1P1PhP?D3P5P6P^P\PMPmPoPnPpPqPrPrPr1D>QRhP=1BhsRB9Cr=P;PvGEP<Pxb2b5b6X09X79111QRiP6P6PiP?D3Py[^09^79P3b1b3b4O2W8X<9PjP_PPP?C>eP^P\PMPmPoPnPGPqPrPzP;PrP{PhE4P<Pxb2b5b6X09116QRQ#5\F^09P|b1b3b4P^P\PMPmP}P]P8PkPoPnPGPqPrPlP;PrPBPKE4P<Pxb2b5b6X09AAQ?~\N^09Ptb1b3b4b9b:PgG?Q09Q0UPjP_PRQ0811OCRgP1P1PgP?D3P5P6P^P\PMPmPoPnPpPqPrPrPr1D>CRgP=1BgsRQ9Cr=P;PvGEP<Pxb2b5b6X09X79111CRBP6P6PBP?D3Py[^09^79P3b1b3b4O2W8X<9PjP_PRP?C>eP^P\PMPmPoPnPGPqPrPzP;PrP{PgE4P<Pxb2b5b6X09116CRC#5\F^09P|b1b3b4P^P\PMPmP}P]P8PkPoPnPGPqPrPlP;PrPQPKE4P<Pxb2b5b6X09AAC?~\N^09Ptb1b3b4b9b:PfG?Q0;Q0TPjP_PSQ0:11OTRfP1P1PfP?D3P5P6P^P\PMPmPoPnPpPqPrPrPr1D>TRfP=1BfsRC9Cr=P;PvGEP<Pxb2b5b6X09X79111TRQP6P6PQP?D3Py[^09^79P3b1b3b4O2W8X<9PjP_PSP?C>eP^P\PMPmPoPnPGPqPrPzP;PrP{PfE4P<Pxb2b5b6X09116TRT#5\F^09P|b1b3b4P^P\PMPmP}P]P8PkPoPnPGPqPrPlP;PrPCPKE4P<Pxb2b5b6X09AAT?~\N^09Ptb1b3b4b9b:PeG?Q0=Q0SPjP_PUQ0<11OVReP1P1PeP?D3P5P6P^P\PMPmPoPnPpPqPrPrPr1D>VReP=1BesRT9Cr=P;PvGEP<Pxb2b5b6X09X79111VRCP6P6PCP?D3Py[^09^79P3b1b3b4O2W8X<9PjP_PUP?C>eP^P\PMPmPoPnPGPqPrPzP;PrP{PeE4P<Pxb2b5b6X09116VRV#5\F^09P|b1b3b4P^P\PMPmP}P]P8PkPoPnPGPqPrPlP;PrPTPKE4P<Pxb2b5b6X09AAV?~\N^09Ptb1b3b4b9b:PdG?Q0?Q0RPjP_PWQ0>11OHRdP1P1PdP?D3P5P6P^P\PMPmPoPnPpPqPrPrPr1D>HRdP=1BdsRV9Cr=P;PvGEP<Pxb2b5b6X09X79111HRTP6P6PTP?D3Py[^09^79P3b1b3b4O2W8X<9PjP_PWP?C>eP^P\PMPmPoPnPGPqPrPzP;PrP{PdE4P<Pxb2b5b6X09116HRH#5\F^09P|b1b3b4P^P\PMPmP}P]P8PkPoPnPGPqPrPlP;PrPVPKE4P<Pxb2b5b6X09AAH?~\N^09Ptb1b3b4b9b:PcG?Q0AQ0QPjP_PXQ0@11ODRcP1P1PcP?D3P5P6P^P\PMPmPoPnPpPqPrPrPr1D>DRcP=1BcsRH9Cr=P;PvGEP<Pxb2b5b6X09X79111DRVP6P6PVP?D3Py[^09^79P3b1b3b4O2W8X<9PjP_PXP?C>eP^P\PMPmPoPnPGPqPrPzP;PrP{PcE4P<Pxb2b5b6X09116DRD#5\F^09P|b1b3b4P^P\PMPmP}P]P8PkPoPnPGPqPrPlP;PrPHPKE4P<Pxb2b5b6X09AAD?~\N^09Ptb1b3b4b9b:PbG?Q0CQ0PPjP_PYQ0B11O2RbP1P1PbP?D3P5P6P^P\PMPmPoPnPpPqPrPrPr1D>2RbP=1BbsRD9Cr=P;PvGEP<Pxb2b5b6X09X791112RHP6P6PHP?D3Py[^09^79P3b1b3b4O2W8X<9PjP_PYP?C>eP^P\PMPmPoPnPGPqPrPzP;PrP{PbE4P<Pxb2b5b6X091162R2#5\F^09P|b1b3b4P^P\PMPmP}P]P8PkPoPnPGPqPrPlP;PrPDPKE4P<Pxb2b5b6X09AA2?~\N^09Ptb1b3b4b9b:PaG?Q0EQ0OPjP_PZQ0D11O:RaP1P1PaP?D3P5P6P^P\PMPmPoPnPpPqPrPrPr1D>:RaP=1BasR29Cr=P;PvGEP<Pxb2b5b6X09X79111:RDP6P6PDP?D3Py[^09^79P3b1b3b4O2W8X<9PjP_PZP?C>eP^P\PMPmPoPnPGPqPrPzP;PrP{PaE4P<Pxb2b5b6X09116:R:#5\F^09P|b1b3b4P^P\PMPmP}P]P8PkPoPnPGPqPrPlP;PrP2PKE4P<Pxb2b5b6X09AA:?~\N^09Ptb1b3b4b9b:P@G?Q0GQ0NPjP_P[Q0F11OLR@P1P1P@P?D3P5P6P^P\PMPmPoPnPpPqPrPrPr1D>LR@P=1B@sR:9Cr=P;PvGEP<Pxb2b5b6X09X79111LR2P6P6P2P?D3Py[^09^79P3b1b3b4O2W8X<9PjP_P[P?C>eP^P\PMPmPoPnPGPqPrPzP;PrP{P@E4P<Pxb2b5b6X09116LRL#5\F^09P|b1b3b4P^P\PMPmP}P]P8PkPoPnPGPqPrPlP;PrP:PKE4P<Pxb2b5b6X09AAL?~\N^09Ptb1b3b4b9b:PAG?Q0JQ0MPjP_Q0HQ0I11OIRAP1P1PAP?D3P5P6P^P\PMPmPoPnPpPqPrPrPr1D>IR>P=1B>sRA9Cr=P;PvGEP<Pxb2b5b6X09X79111IRLP6P6PLP?D3Py[^09^79P3b1b3b4O2W8X<9PjP_Q0HP?C>eP^P\PMPmPoPnPGPqPrPzP;PrP{P>E4P<Pxb2b5b6X09116IRI#5\F^09P|b1b3b4P^P\PMPmP}P]P8PkPoPnPGPqPrPlP;PrPAPKE4P<Pxb2b5b6X09AAI?~\N^09Ptb1b3b4b9b:P5G?PjP_Q0KQ0L11OJROP1P1POP?D3P5P6P^P\PMPmPoPnPpPqPrPrQ0YPrP=1BusRsP;PvGiP<Pxb2b5b6X09X79Q0[P6P6Q0[P?D3Py[^09^79P3b1b3b4O2W8X<9PjP_Q0KP?C>eP^P\PMPmPoPnPGPqPrPzP;PrP{PuE4P<Pxb2b5b6X09%5w\F^09P|b1b3b4P^P\PMPmP}P]P8PkPoPnPGPqPrPlP;PrPsPKE4P<Pxb2b5b6X09AAw?~\N^09Ptb1b3b4b9b:P6G?FJFJFJFJFJFJA;07_eWCWHWGP6P1O2n2001000000121000000W=WFP6P1O2n2001000000121000000W=WEP6P1O2n2001000000121000000W=WPP6P1O2n2011000000121000000W=WOP6P1O2n2011000000121000000W=WNP6P1O2n2011000000121000000W=WMP6P1O2n2011000000121000000W=WLP6P1O2n2011000000121000000W=WKP6P1O2n2011000000121000000W=WJP6P1O2n2011000000121000000W=WIP6P1O2n2011000000121000000W=WDP6P1O2n2011000000121000000W=WRWQW@W?WAXB9P4P5P6P1O4W@W?WAXB9o"). Qed.

(* [comment removed for export] *)
Definition rinvH (R0 Rc : bvmap 5 word) (V2 cls F : Z) : Prop :=
  getr Rc (reg 2) = Z_to_bv 64 (V2 - 160) /\ getr Rc (reg 8) = Z_to_bv 64 (V2 + cls) /\ getr Rc (reg 9) = Z_to_bv 64 (V2 - 160) /\
  getr Rc (reg 19) = Z_to_bv 64 (F / 8 + 2147450880) /\ getr Rc (reg 21) = Z_to_bv 64 (F + 96) /\ getr Rc (reg 27) = Z_to_bv 64 F /\
  getr Rc (reg 3) = getr R0 (reg 3) /\ getr Rc (reg 4) = getr R0 (reg 4).
Definition HIDX : list nat := [2; 3; 4; 8; 9; 19; 21; 27]%nat.
Lemma rinvH_keep R0 Ra Rb V2 cls F : rinvH R0 Ra V2 cls F -> (forall k, In k HIDX -> getr Rb (reg k) = getr Ra (reg k)) -> rinvH R0 Rb V2 cls F.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAHarnessStmts ()) [] "h01bh11kh21Hh31Fh42R0h52Rah62Rbh72V2h83clsh92KSh:3X19h;2X2h<3X21h=3X27h>2X3h?2X4h@2X8hA2X9p;1p;2p;5p;3p;4p;6p-1p10000p4p710p9g000\j1:Tg001Aj1TTg001fj1WTg002Dj1`Tg002gj2ZTg00o6j5ATg009hj1RTg00Pij1QTg004Yj20Tg0043j2;Tg00<Ej34Tg008IR0j25Tg00WVj2LTg00IMj4ITg00b?j22Tg00=bj6GTg010>j3KTg003Sj1_Tg00fij2^Tg00bYj2XTg00]_j3]Tg00G6j2\Tg010Xj3[Tf0R1#:#:p=U%Q1#Qp=8f1R2%_1';p=?%:1#:#:#:p=Pf2R31^21';p=@f3R41032;41p=3%T1#Tp=J1X32/L1,;4p=Df4R51043102134p==1043=452/51p=6f5R610541;3234/51p=<f6R710651L32,;434/51p=>g00;HR8g01127]1p=B1L21,;3p=N10219443p=HA4432/51p=71521,53p=M1521,53,54,55p=O1;219443p=S1X32/L1p=YA4821p=1g00c6R9,21p=FA4854A4832/21'2p=C1\819[32p=EAK3219K54p=9A4832/21p=Vg00:cR:#:R;#TR<#WR=%U;R;#:#U#WR>#`R?'ZR@g00>@RAP6P5P3P2P1DAP0P?P6g00\T#8RB,?=RC%:<#P#RR<9@>4RDC3P?P6%QBRE#QRF#8#8RG,?=RHP>P4P3P?P6%QGRI,?=RJPDP?P6%8I#8#8#8#8RD,?=RKP>P2%R;R;%T:R:#J#J#J#J#J#J#J#:#U#P#P#P#RRLCDP?P6%8DRM,?=RNP>P2%::#P#RR:P?P6%8M#8#8RO,?=RPP>P2P?P61?=ERQ107QP?P61?=FRRP7PRD=D6E<F>D6D6F>%B1RSP?f7RT1?=2R=f8RUP=D=[^18PUP7P6P5P4DA[P1P?PTPCA@>6<C3P?PUPHP>P7P6P?PUPJA@>7<P?PUPKP>P5P;PLCDP?PUPNP>P5P:P?PUPPP>P5P?PUPQf9RV/0QRWP?PUPR10VRRXC3D6E<F>D6D6F>P0P?PVPHAN>T7C3P?PVPJA@>T<P?PVPKP>P6P;PLCDP?PVPNP>P6P:P?PVPPP>P6P?PWf:RW/0QP?PXPWPRCHC7E<F>D6D6P?f;RXP=f<RYP=D=\S^18PYPWPVPUPTDA[P1P?PXPHAN>VUC3P?PYPJA@>W<P?PYPKP>PUP;PLCDP?PYPNP>PUP:P?PYPPP>PUP?PYPQf=RU/0QRTP?PYPR10URRZC3D6E<F>D6D6P0P?PUPJA@>X<C3P?PUPKP>PVP;PLCDP?PUPNP>PVP:P?PUPPP>PVP?PTf>RT/0QP?PZPTPRCHC7E<F>D6P?f?RZP=f@RVP=D=\S^18PVPTPUPYPXDA[P1P?PZPJA@>U<C3P?PVPKP>PYP;PLCDP?PVPNP>PYP:P?PVPPP>PYP?PVPQfARY/0QRXP?PVPR10YRR[C3D6E<F>D6P0P?PYPKP>PUP;PLCDC3P?PYPNP>PUP:P?PYPPP>PUP?PXfBRX/0QP?P[PXPRCHC7E<F>P?fCR[P=fDRUP=D=\S^18PUPXPYPVPZDA[P1P?P[PKP>PZP;PLCDC3P?PUPNP>PVP:P?PUPPP>PVP?PUPQfERV/0QRZP?PUPR10VRR\C3D6E<F>P0P?PVPNAN>Y:C3P?PVPPP>PYP?PZfFRZ/0QP?P\PZPRCHC7E<P?fGR\P=fHRYP=D=\S^18PYPZPVPUP[DA[P1P?P\PNAN>[:C3P?PYPPP>PUP?PYPQfIRU/0QR[P?PYPR10URR]C3D6E<P0P?PUPP1;>VC3P?P[fJR[/0QP?P]P[PRCHC7P?fKR]P=fLRVP=D=\S^18PVP[PUPYP\DA[P1P?P]PP1;>\C3P?PVPQfMR\/0QRYP?PVPR10\RRUC3D6P0P?PYfNRYPQCHP?PUPYPRCHP?fORUP=fPR0P=D=\S^18P0PYP\PVP]DA[P1P?PUPQP0PQD=P?P0PRfQR]/0RRVC3P?fRR\P=fSR^P=D=\S^18P?10\CR8A@>]<RS94?1R=10\HR_AN>]0R`54?P?10\JRaPSP?10\KRbP>PUP;PLCDRcP?10\NRdAN>U:ReP?10\PRf1;>URgP?10\QRhfTRi/0QRj10\RR\10iRRi54?RkC7RlC7RmC7RnC7RoC7Rp3MX0?P?P_P?P^PCPSC3RqA4?1`;MpX0?P?PaP?P^PHP`C3R`15=o5MqX0?P?PbPqP`P?P^PJPSC3RSA4?1cPnDOX0?P?PdPqP`PSP?P^PKPcC3RcP?P1PePmC7DOX0?P?PfPqP`PSPcP?P^PNPeC3ReA4?1g;MlDOX0?P?PhPqP`PSPcP?P^PPPgC3RgP?P1PjPkC75MeDOX0?P?P\PqP`PSPcP?10^QRcPjA4?1iC79MegDOX0?A@>0<R<94?8P?P_P>1L0UCSR_A4?a<R<P?PbP>AYY;LCSRLP?PdP>1LY:CSR:P?PfP>PYCSR>A4?hcRcP?P\P^PRCHRR'5R\'5R?'5Rh'5Rf'5Rd'5P[P_PdPZP<PfPXPLPhPTP:P?PWP>P\P7PcPRP3P2CICICICICICICIPVP1PF11BF11EFRV11FFRRPGPFPIPFPDPFPMPF11OF#FDCDCRc'2R7'2PVP7AERcFD9%BFeO2EG10]QP1PE11BE11EERQPFPEPGPEPIPEPDPE11OE#F9VMEDCDCRc'2AEQcE3K%BEeO2EG10]PP1PO11BO11EORP11FORc11GORQ11IORR11DOR711MORV11OOR\#FR>'2RW'2R?'2R:'2RT'2Rh'2PPPhPcPTPQP:PRP?P7PWAE\9O9KV>D9D9D9%BOeO2EG10]NP1PM11BM11EMRN11FMR>11GMRV11IMR\11DMR911MMRW11OM#FR7'2R?'2RR'2R:'2RQ'2RT'2PNPTP>PQPVP:P\PRP9P?AEW7MD9D9D9%BMeO2EG10]KP1PD11BD11EDRK11FDR711GDRW11IDR?11DDR911OD#F9VMDRR'2R\'2R:'2RV'2RQ'2PKPQP7PVPWP:AE9RD9K?\D9D9%BDeO2EG10]JP1PI11BI11EIRJ11FIR\11GIR?11IIRRPDPIPMPI11OI#FDCR9'2R:'2RW'2RV'2PJPVP\PWP?P:AER9ID9D9%BIeO2EG10]HP1PG11BG11EGRH11FGR911GGRRPIPGPDPG11OG#F9VMGDCR:'2R?'2RW'2PHPWAER:G9K9?D9%BGeO2EG10]CP1PB11BBPEPBPFPBPGPBPIPBPDPBPMPB11OB#FDCDCDC;EB%BBeO2EGP^P]P0PUPYDAeW9W?W>P2P1O2n2001000000121000000W2W=P2P1O2n2001000000121000000W2W<P2P1O2n2001000000121000000W2W:P2P1O2n2011000000121000000W2WAP2P1O2n2011000000121000000W2W@P2P1O2n2011000000121000000W2W;P2P1O2n2011000000121000000W2X3AX8AX7AX6@X5@X4@P6P5P4P3P2P1O6X3AX8AW7X6@X5@W4o"). Qed.
Lemma rinvH_ks R0 Ra Rb V2 cls F (KSL : list nat) : rinvH R0 Ra V2 cls F -> (forall k, In k KSL -> getr Rb (reg k) = getr Ra (reg k)) ->
  forallb (fun k => existsb (Nat.eqb k) KSL) HIDX = true -> rinvH R0 Rb V2 cls F.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAHarnessStmts ()) [] "p'0h01xi001xh11kh22HBh31Hh42Hxh51Ah61Eh71Fh83KSLh92R0h:2Rah;2Rbh<2V2h=3clsh>1fh?1lh@1mhA1nhB2HkhC2KShD2RIhE5lemmap;1p;2p;5p;3p;7p;8p-1p10000p4p710p9g000\j14Tg001Aj1LTg001fj1=Tg002Dj1?Tg002gj2KTg00B8j1>Tg00o6j5DTg003Sj1ATg0043j2@Tg004Yj2<Tg00<Ej35Tg0129j19j22Tg00]_j37Tg012Yj2JTg0132j3ITg013cj3CTg014FR0j3:Tg008IR1j23Tg014bR2j28Tg015<j3BTg015_j2ETg00^6j7FTg016Bj8GTg017Oj3HTg00;HR3f1R4f0R537p=1A:345p=6g0112R69H35p=;g00N:R7g00NZ755p=0g00:c#4R8#L#=R9%48#4#4#4#4#=#?R8'KR:g00>@R;%>3R<f6R=f5R>f3R?f2R@P4DD115@f7RA%A4,@9R9'<f8RB/<9558[^13%95R8/6?X13#;#0f9R9PBPAP=P>f4RCP@A7356RDP?P4168=X13RE#;#0168BX13P4O1#0\D^03RF'J168AX13#;#01689X13P4O1#0\D^03;I5WEAC3E6P@O2PFP5P@P4O2%9@/6=#0P0p4p710R0P7\5R7%>4RFP1A:@45#0A7C5@P?P5O1#0'3X0?,8?[REA7?54P@P5O1#0'3X0@,8@A:?@4#0R6[A7>5?PCP5O1#0'3X0C,8C\6AB@45P4n2001000000120000000W?W>W5PE^?F^>7^50P5P3%9CPBP4O4115912>5#0'3X03,83P2P3f:R2,1512=5#0'3X0311=2P5f<R0,1512B5#0'3P1f=,141294#0f>R9,12P5f?R2,1?120C#0P11245#0A53@4[R1A534512@4#0R0[A53?@\01E45P4n2001000000120000000X@3XA3P1^@3^A3P5P9P=P4O3A539=P3P2fD,15fAfE'1]4X03fC,12P5W4PAP5P?FFb6b3W6W4P4P5O2n2001000000120000000W3X03P4P5O2n2001000000120100000b2b3b2b2O2WBX13GGW2WCWDX8<X7;X=;X<;X;:X::X9:P=P>PCP?P@P4P5O7W8X7;X=;W<X;:X::W9o"). Qed.
Lemma rinvH_pres R0 Ra Rb V2 cls F : rinvH R0 Ra V2 cls F -> regs_preserved Ra Rb -> rinvH R0 Rb V2 cls F.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAHarnessStmts ()) [] "h02Hkh11Hh21Fh32R0h42Rah52Rbh62V2h73clsh81kh92RIh:2RPp;1p;2p;5p;3p;8p;6p-1p10000p4p710p9g000\j17Tg001Aj1:Tg001fj1KTg002Dj1PTg002gj2VTg00o6j5UTg017kj2RTg00]_j3DTg00Pij1ETg00AXj1LTg009hj16Tg00b?R0j21Tg010>j3FTg006>j2JTg016Bj8OTg003Sj1ITg0043j2HTg00<Ej3BTg00Soj3GTg00G6j2NTg010Xj3MTg00^6j6STf1R1f0R2#I'Hp=Q%E2#Ep=8g00;HR3?B12p=5AG312p=AAD312p=4g00>@R4?G12p=Tf2R5AG4125G4p=@f3R6%I1,H5'J=D42p=9%I2,H1,J5p=?AB412p=0g00c6R7,12p=>AB451/12p=Cf4R8=B46AB451/12'1p=21N429M51p==AD412p=;P3P8P6P5P1P2ESp=<AF5129F86p=3g00:cR9#7R:#:R;#KR<%7:R=#7R>#7#7#7#K#P'VR?f5R@P8P5P1P2DU1R@8f7RAf6RBP@P8P6P5P1g01129D32P51Q<1RCP0g00\T#8RD/51%EDRE%EERF%8F#8RG%EGRH%8H#8#8#8#8RI%8IRJ%8J#8#8RK%L3RL'ARM'ARN'ARO'ARP'ARQ'ARR'ARS,41P<P<P5%6:R:%:9R9#6RT%6=RU%6>R>%:=R=#6RV%7=#6RW%:=#6R=%7;RX#7#6RY%:X#6RX%:;R;#7#6RZ%:;#6R;%79R9#7R[#7#6R\%:[#6R[%:9R9#7#6R]%:9#6R9%L4'T3@3@3@3@3@3@3@R^C9P215D5PDP<P<P2P^C9X83R_A?<<DRD,0:PTPDPUPDP>PDPVPDPWPDP=PDPYPDPXPDPZPDP;PDP\PDP[PD109D#>9C]DD2D2D2D2D2D2;=D1;D^eP6P2D<W1P2O1145SP015E6146RP<P<P8P^C9P215E8PEP_A?<<ERE,0:10TERSPUPEP>PEPVPEPWPEP=PEPYPEPXPEPZPEP;PEP\PEP[PEP]PE109E#>D2D2D2D2D2D2RD'1A=SDE3F1;E^eP@P2D<W1P2O1148RP015F@14@QP<P<PBP^C9P215FBPFP_A?<<FRF,0:10TFRR10UFREP>PFPVPFPWPFP=PFPYPFPXPFPZPFP;PFP\PFP[PF109F#>9C]FD2D2D2D2D2RD'1RS'1PRPSA=EDFD31;F^ePAP2D<W1P2O114BQP015GA14APP<P<f8RAP^C9P215GAPGP_A?<<GRG,0:10TGRQ10UGRB10>GRFPVPGPWPGP=PGPYPGPXPGPZPGP;PGP\PGP[PGP]PG109G#>D2D2D2D2D2RD'1RE'1RS'1PQPSA=FDG9FBED31;G^ef9RGP2D<W1P2O114APP015HG14GOP<P<f:RGP^C9P215HGPHP_A?<<HRH,0:10THRA10UHRP10>HRE10VHRBPWPHP=PHPYPHPXPHPZPHP;PHP\PHP[PH109H#>9C]HD2D2D2D2RD'1RF'1RS'1RQ'1PAPQPPPSPEPFA=BDHD3D31;H^ef;RHP2D<W1P2O114GOP015IH14HNP<P<f<RHP^C9P215IHPIP_A?<<IRI,0:10TIRG10UIRO10>IRD10VIRB10WIRF10=IREPYPIPXPIPZPIP;PIP\PIP[PI109I#>9C]ID2D2D2RS'1RP'1RQ'1RA'1RR'1R`'1PGP`POPRPDPAPBPQPFPPA=ESID3D3D31;I^ef=RIP2D<W1P2O114HNP015JI14IMP<P<f>RIP^C9P215JIPJP_A?<<JRJ,0:10TJRH10UJRN10>JRS10VJRE10WJRP10=JRF10YJRQ10XJRBPZPJP;PJP\PJP[PJ109J#>9C]JD2D2RA'1RD'1RR'1RO'1R`'1RG'1Ra'1Rb'1PHPbPNPaPSPGPEP`PPPOPFPRPQPDA=BAJD3D3D3D31;J^ef?RJP2D<W1P2O114IMP015KJ14JLP<P<f@RJP^C9P215KJPKP_A?<<KRK,0:10TKRT10UKRU10>KR>10VKRV10WKRW10=KR=10YKRY10XKRX10ZKRZ10;KR;10\KR\10[KR[10]KR]109KR9#>R:'1R_'1R0'1RI'1RM'1RA'1RB'1RD'1RQ'1RR'1RF'1RO'1RP'1PTPPPUPOP>PFPVPRPWPQP=PDPYPBPXPAPZPMP;PIP\P0P[P_P]P:A=97KD3D3D3D3D3D3D31;K^efAP2D<W1P2O114JLP7P<P<fBP^C9P2n010000000W0P2O1n200100000021100010000W0P2O1n200100000021100011000W0P2O1n200100000021100011000W0P2O1n200100000021100011000W0P2O1n200100000021100011000W0P2O1n200100000021100011000W0P2O1n200100000021100011000W0P2O1n2001000000211000110001J<Cg01905D4eO2W0X83GOW:W9X24X74X64X5?X4?X3?P@P8P6P5P1P2O6X24X74X64X5?X4?W3o"). Qed.

(* [comment removed for export] *)
Section Stmt.
Context {SCFG_P : ScfgP}.
Definition harness_call_stmt (RES : credit) : Prop :=
  forall (L : asan_layout) (C : asan_statics_cells) (IL : icpt_layout) (ar : asan_run) (HI : asan_iface),
    PMA.layout L C -> as0_icpt_layout IL -> NTASMA.inst_ok L C IL ar HI ->
    NTASMA.harness_depsS L ar HI RES ->
    lib_call_okA (LayA RES L) ar SCFG (HAJ.strict_of HI) (PQSTA.TopLSA RSEGS PMA.AD PMA.AAD PnLayoutQA.QADDR_A).
End Stmt.
End PQHAS.

End PnAHarnessStmts.
