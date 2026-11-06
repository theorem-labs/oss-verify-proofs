(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import RzCPS NodesA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_objkit Pm_iface Pm_iface2 Pm_iface4 Pm_okit PmF_kit Cf_iface RT_fk D_iface D_defs Bi_fktw Bi_fkweak Bi_iface2.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import Po_rows Po_iface Po_udd_kit Po_csels_tail Po_csce_kit2.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_Po_csce_kit3 () := "I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes4prod01C46Stdlib5Lists4List2InC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01C69OSSVerify5KrLib2K53B23;Lept_objkit:keeps_liveC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03C69OSSVerify5KrLib2K53B238Po_iface5pix1cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B237PmF_kit:pix_chunksC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:Lept_iface7pix_objC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:Lept_iface3p_dC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib2K53B23:Lept_iface6p_dataC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC69OSSVerify5KrLib2K53B238Po_iface4res0C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C69OSSVerify5KrLib2K53B237PmF_kit=pix_chunks_inC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B23<Po_csce_kit3?keeps_live_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<Po_csce_kit2;pix1c_carryC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53B23:Lept_iface4pixv00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53B23:Lept_iface5cmapv00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01C69OSSVerify5KrLib2K53B238Po_iface7sel_objC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23=Po_csels_tail<sel_obj_monoC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53B238Po_iface4selv00C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma keeps_live_refl : forall L (m : mem), keeps_live L m m.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_csce_kit3 ()) [] "h01Lh12_Hh23_H0h31ah41bh51kh61mp;2p;1p;4p;3g0000j2>Tg000Pj1=Tg0010j10Tg001Uj11Tg0023j12Tg002Vj1:Tg0038j47Tg003Xj34Tg003oj25Tg004Yj26Tg0055j23Tg005Rj28Tg005nj29Tg006Ij2<Tg006cj3;Tg007eR0/>0R1#=g008C#0#0#0R2#0#0#0#1R3#2R4%12#2#:R2[P0P0f1R5f0R6C7f3R75411536R3,67f2,37,83'9f5P5O1,<2W2X34W1X50X40A;566eW6W0o"). Qed.

Lemma pix1c_mono : forall (L L' : list (Z * Z)) (m : mem) p v cv, pix1c L m p v cv -> (forall e, In e L -> In e L') -> pix1c L' m p v cv.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_csce_kit3 ()) [] "h01eh12Heh21Lh32L'h41Ph53SUBh62cvh71mh81ph91vp;2p;1p;5p;3p;8p;:g0000j2DTg000Pj1CTg0010j10Tg001Uj14Tg0023j15Tg002Vj1;Tg008hj5:Tg003Xj31Tg009bj38Tg00:`j57Tg00;^j16Tg00<Xj19Tg00=6j33Tg00=Pj1BTg00>Mj1ATg00>fj1<Tg005nj22Tg00?_j3=Tg00@:j8>Tg00A;j2?Tg00BCl:@Tg007eR0/D0R1#CR2g008CR3#0#0#0R4#0#0#0#4#5%44#5#;[g00CGg00DDf5R4f3R5f2R6f1R7f0R8D:f7R99118A1179[^01P9f6R:P4P4f4R;P5P6P7A84;59118P6P7f9R6P9P:P4P;P6P9P:P4P;D7%64%93530%B4g00EB530#A%<4'2'2;=5P7P8G>O2W1X011?:4M:@W5W4W6W9X80W7X32W2o"). Qed.

Lemma sel_mono : forall (L L' : list (Z * Z)) (m : mem) s sv, sel_obj L m s sv -> (forall e, In e L -> In e L') -> sel_obj L' m s sv.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_csce_kit3 ()) [] "h01Lh12L'h22SOh33SUBh41eh51mh61sh72svp;2p;1p;4p;3p;7g0000j28Tg000Pj17Tg0010j10Tg001Uj11Tg0023j13Tg002Vj16Tg00E`j45Tg003Xj32Tg00F\j74Tg007eR0/80R1#7R2g008C#0#0#0R3#0#0#0#1#3%13#3#6[g00Gbf4R3f2R4f1R5f0R6C5f6R79216A2157[^41P7f5P3f3P4P6P5F4W3W2W7X60W5X12W0o"). Qed.
