(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require AW_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.boost_json.fuzz_parse.images Require Import Asan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanAllocModel SReach LazyRestrict LazyLedger LazySR LazyNodes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AllocWf AllocKit AllocBudget AllocRep AllocRepFacts AllocRepFacts2 AllocRepX CidBits CidBits2
     AsDepotInv AsDepotHash AsDepotPut AsUnwind AW_DepotFrame AW_MallocBase AW_AllocBase AW_LargeAlloc1 AW_InitCache AW_IAInit AW_FreePre
     AW_Refill AW_Put1 AW_Enqueue1 AW_Enqueue2 AW_Put2 AS_Free1 AS_Free2 AS_Free3 AllocWalkKit
     AG_MallocModel AG_WFHit AG_Malloc AG_Malloc2 AG_RefillModel AG_ColdModel AS_Refill1 AS_Refill2 AS_Refill4 AG_Refill1 AG_Refill2 AG_Refill3 AG_MallocCold
     AG_FreeModel AG_WFFree AG_Free1 AG_FreeFacts AG_Free2 AG_Free3 AG_Free4 AG_Free5 AG_Free6 AG_Free7 SecLazy.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_AG_Free8 () := KReplay.lz_vm "#$/UI47Corelib4Init9Datatypes4list00C89OSSVerify6Proofs:boost_json:fuzz_parse3lib2As9AllocRepX7AMODELXC13~~~I!snR8!sn'3a!tU$!sk%4ELinuxProcessSemantics?!s<25State5Model00I7!tIN>Asan!tJ$!sd$5chunk!tN+!sp^6qcache!sqhpclass!sq'C!vy[4AREP!vx'!xu;prod00I46Stdlib5Lists4!s+#5NoDup00C!sB62InC!x`]lb!uP&!td15Logic3iffI!s?8and!t\#!sA65proj1!s\,7Numbers7BinNums1Z!{PU!t~+6ast_ok!wSb8inst_rep!snb9flags!sof:thread!spf7sec!smf6ia!sl-5!z3&6ZArith6BinInt1Z2le!sB>t!v,]region!vwg!}u%!spfA!tb&shadow!swf?!sw&junk!suf4a_st!sj&!#5F]:!#7'#_li!ss+!|'\!sp%!uP,!#8i^as_tq!sne7qc!uQg;batches!uSmg!uS&K!#65>1!t4_;kNumC!{s#es!xHcplaced!#7-[7!so$Wf2WF!sg&!#9>;2!{v_AL!t,8!#<_+6length!#4r;6of_nat!w=_?compact_to_addr!t`'!#=]5hd!ucS:AS_Refill16rf_au'!wWY!sn-7rf_mfa!soe!t_#nf1!t_hnnew!t_hm!v@f4!t_#!~Te>rg_mapped_user!sweArg_a!s4#at!szlD!ts,free_array!s}e<rg_num!sz$d!#4;a4a_ri!#6;B8positive02!#6`?2!~i<3mul!sC=add!tKG1K!#5?62eq01I!s@;0!#;6`b!#3|-!sp^4zle!{\f7ch!zY#d!spe;!sp%r_beg!yYesb!sjb5a_ctx!sketh!ws'!z'24Znat5Nat2Z9is_nonneg!{3>N02I45stdpp9bitvector;definitions2bv00C!sI@;bv_unsigned!#:Q'9micromega9SatDivModCZ_mod!tc&!s,&!#<D<modulo!sF<>pow_pos!snC3pow!sC<:!sk#!vC3!#Ym71K!uP56VarMap1t!}O#!sD>0!sD6=RingM!s4'7Formula00!t567Env!sT#5PExpr!tX8!st:!sQ75Tauto8G!sJ'5C!sJ<B!sJ&!sH6:Z!t<+=Z!sT$CheckerC!v#<4find!sqAC!sq0_sound!u9F4!u9<5eKind!#YA<unit!w:8!se%4kind!#763!sf31!#7{F3!#Hd`Batch!#Hf#!~V%!#^6`!#K_#!#`Q+!#9J54True!zw8!wu-;!|\%!tM$!vd8!zU13Op203!wS=bool!sm#!sF@!#LL_@as_internal_ini!#OHV3Lib4TacX2b8!#?7%!seS5Cells4cell04!tQ`wz!tQf3!sjf2!sjf1!#:q8!#7p+sub!vFUStep8rw_!t1#!|K&!yy<3nat!#D&-!#8X72!u[`5!#>;bz!{m#!sk&!tw+!#P/$7!s+#Def6repeat!sE;3map!vfT2Nd;and_elimF17!ztZ2Nd:!sl+!{a&I!vm_!#k7Y5ASegs5aseg!#X5b7AIAINIT!smb6AFLAGS!t[dC!smg<ASHBASE_CELL!w$_!so#ADOW_!st#!tcb;AHIGHMEMEND!sqb:ACANPOISON!xleNITE!t_c8ACTXSIZE!sndTSD!zL,!#5?@1!wQ^ALLO!z%h6AHOOK!sleDYING!yxdREALMEMSET!y-d!smjGOT_LO!smb9!sm$VAL!#3fdPAGESZ!zedSECNAME!uNdPRIM!sof8ATLSSLO!wvc4!}6#!tZdLSANDI!wrc5!xc#2!skY9AW_IAInit8ia_aft!#a]'!so\;ia_pristine!srV!#>|3!#?i%".
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As9AllocRepX~~~~~~07AMODELX37Corelib4Init9Datatypesk84list3h5LinuxProcessSemanticsfLinuxProcessSem5Statem75Model79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AG_Free2~~~~~~pd7free_s'79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AllocRep~~~~~~u54a_ALu53a_Lu53a_Su53ast69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocModel~~~~~~hjc5chunkhjc6pclasshjc6qcache" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Ltac lia ::=
  first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].

(* [comment removed for export] *)
Ltac trp lem AG WM H Z B :=
  eapply (lem _ _ _ AG WM); [exact H|];
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul Z.mul length];
  let Ha := fresh in intros ? Ha; apply Z; clear - Ha B; try acb; lia.

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Lemma amodelx_free : ltac2:(zQ "b0!jf!m0!p5!tb!hi3!hia!hj0!hj6!hnd!ho6!hp0>1s$7>2mo$2>2ch$8>3tq'$a>6cache'@1$1$9>0@3$0?5HCEIL^5^4@3$0?5HCEIL@7$3^6^4^3^2@1$5^6@1$6^6@1$4^6^5").
Proof.
ltac2:(KReplay.run1 (kr_t_AG_Free8 ()) ["HCW"] "h01Ah16cache'h22chh32moh41sh53tq'p;1p;3g0000j11Tg000Pj30Tg001Xg002]g003Sg004]g005h#1p,5HCEILf4f330f0W0W1W5W2W3W4o"). Qed.

Section FreeRefillGlue.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (msF : machine_state) (mo : Model) (Q : config -> Prop).
  Variables (s : ast) (LB : list (Z * Z)) (d : depot) (lo : Z) (CH : list (Z * Z)) (ch : chunk) (bs sbs : list byte).

  Let st := a_st s.
  Let TH := a_thr s.
  Let CTX := a_ctx s.
  Let sb := a_sb s.
  Let U := ch_user_beg ch.
  Let size := ch_used ch.
  Let tq := as_tq st.
  Let l := qc_list tq.
  Let k := zlen l.
  Let lb := last l (mkQB 0 0 0 []).
  Let LA := qb_addr lb.
  (* [comment removed for export] *)
  Let c := kBatchClass.
  Let CA := TH + 208.
  Let P := CA + 80 * c.
  Let RI := a_ri s + 128 * c.
  Let r := get_region st c.
  Let nf := rg_num_freed r. Let mfa := rg_mapped_free_array r. Let au := rg_allocated_user r. Let mu := rg_mapped_user r. Let fl := rg_free_array r.
  Let n := rf_n c.
  Let mu' := rf_mu' c nf au mu. Let nnew := rf_nnew c nf au mu. Let nf1 := rf_nf1 c nf au mu. Let mfa' := rf_mfa' c nf mfa au mu.
  Let au' := rf_au' c nf au mu. Let fl1 := rf_fl1 c nf au mu fl.
  Let st2 := refilled st c.
  Let chunks2 := firstn (Z.to_nat n) fl1.
  Let cp := hd 0 chunks2.
  Let B := compact_to_addr st2 c cp.
  (* [comment removed for export] *)
  Let CHI := icpt_chain (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned sp) (a_top s) CH.
  Let T := utrace 0x90ca0 (bv_unsigned sp) (a_top s) (a_bot s) 30 CHI.
  Let nT := Z.of_nat (length T).
  Let d' := d_put d (depot_hash T) nT.
  (* [comment removed for export] *)
  Let L2 : list (word * word) :=
    if mfa <? mfa' then maps_subtract (if mu <? mu' then maps_subtract (a_L s) (RB s c + mu) (RB s c + mu') else a_L s) (FA s c + mfa) (FA s c + mfa')
    else (if mu <? mu' then maps_subtract (a_L s) (RB s c + mu) (RB s c + mu') else a_L s).
  Let S2 : list (word * word) :=
    (if mfa <? mfa' then [(wz (sh (FA s c + mfa)), wz ((mfa' - mfa) / 8))] else [])
    ++ (if mu <? mu' then [(wz (sh (RB s c + mu)), wz ((mu' - mu) / 8))] else []) ++ a_S s.
  Let AL' := a_AL s.   (* [comment removed for export] *)
  Let sR := mkAst st2 (a_thr s) (a_ctx s) (a_fsb s) L2 S2 (a_Zr s) AL' (a_top s) (a_bot s).
  Let tq' := tq_new tq B (ch_chunk_beg ch) size.
  Let cache' := upd_nth (as_cache st2) (zidx c) (mkPC (n - 1) (tl chunks2)).
  Let sF := free_s' sR ch tq' cache' L2 S2 AL'.
  (* [comment removed for export] *)
  Let Wh : list ivl := free_head_W lo (bv_unsigned sp) TH U size d.
  Let WR : list ivl := (lo, bv_unsigned sp) :: (TH + 3168, TH + 3169) :: rf_W lo (bv_unsigned sp) P RI (FA s c) (RB s c) TH CA nf mfa mu mfa' mu'.
  Let Wn : list ivl := enq_new_W lo (bv_unsigned sp) TH B LA.

  Hypothesis HR : ARHEAP s LB m.
  Hypothesis CHIN : In ch (chunk_list st).
  Hypothesis ALLOC : ch_state ch = CAllocated.
  Hypothesis UHI : aapp (ch_user_beg ch - 16) (16 + round_up (ch_used ch) 8).   (* [comment removed for export] *)
  Hypothesis AX : awin_vis s m /\ flagsx_rep m.
  Hypothesis AMX : AMODELX s mo.
  Hypothesis DEP : DEPOT asegs d m.
  Hypothesis DPL : depot_placed s d.
  Hypothesis DCOV : depot_cov d mo.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : aceil <= lo.
  Hypothesis HI : lo + 2944 <= bv_unsigned sp.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPT : bv_unsigned sp + 16 <= 2^47.
  Hypothesis TP : tp = wz ATP.
  Hypothesis DLO : d_nb d + 16 * 65536 <= lo /\ d_sb d + 8 * 32768 <= lo.
  Hypothesis DCAP : d_ids d + 1 < 65536 /\ d_frames d + 31 <= 32768.
  Hypothesis FCH : goodframe (a_bot s) (bv_unsigned sp) (a_top s) = true -> goodframe (bv_unsigned sp) (bv_unsigned s0) (a_top s) = true ->
                   bv_unsigned sp + 16 <= bv_unsigned s0 /\ frame_chain asegs m (a_top s) (bv_unsigned s0) CH.
  Hypothesis Ha0 : a0 = wz U.
  Hypothesis BLK : rw_cells asegs m U [CB (Z.to_nat size) bs].
  Hypothesis SHB : SHAD m U sbs /\ Z.of_nat (length sbs) = nsh size.
  (* [comment removed for export] *)
  Hypothesis QSZ : size <= kQuarantineMaxSize /\ size < 2^32.
  Hypothesis NN : need_new tq = true.
  Hypothesis MISS : pc_count (get_pc st c) = 0.
  Hypothesis NOD : qc_bytes tq + size + kBatchSize <= kMaxCacheSize.
  (* [comment removed for export] *)
  Hypothesis PROOM : pusage st + COLD_COST <= B_PRIM.   (* [comment removed for export] *)
  Hypothesis ROOM : mu + 2 * kUserMapSize <= kFreeArrayOffset.
  (* [comment removed for export] *)
  Hypothesis OK : lzok asegs (a_L s) (a_S s) (a_Zr s) (mkCfg msF mo).
  Hypothesis VISE : restrict (a_L s) (a_S s) msF
    = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x90b68) fc None m (seg_rom asegs).

  (* [comment removed for export] *)

  Let R : AREP s m. Proof. exact (proj1 HR). Qed.
  Let OKs : ast_ok s. Proof. exact (proj1 R). Qed.
  Let PL : placed_ok s. Proof. exact (proj1 OKs). Qed.
  Let WFs : WF st. Proof. exact (proj2 OKs). Qed.
  Let HC : 1 <= c <= 30. Proof. unfold c, kBatchClass. lia. Qed.
  (* [comment removed for export] *)
  Let FLG4 : rw_cells asegs m AIAINIT [C1 (b8 (if as_internal_init st then 1 else 0)); C1 (b8 0); C2 (wz 0)].
  Proof.
    pose proof R as RR. ndestruct RR as (_ & _ & FL & _).
    ndestruct FL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F16 & _). exact F16.
  Qed.
  Let IAX : if as_internal_init st then ia_after m else ia_pristine m.
  Proof. pose proof R as RR. ndestruct RR as (_ & _ & _ & _ & _ & IA & _). unfold ia_rep in IA. unfold ia_after, ia_pristine. exact IA. Qed.
  Let PURE := free_pure s m ch R CHIN UHI.
  Let RPURE := refill_pure s m c R HC MISS.
  Let RF := rf_facts st c WFs HC ROOM.
  Let PCc := rfd_pc_c st c WFs HC ROOM.
  Ltac zlets := repeat match goal with H := _ |- _ => subst H end.

End FreeRefillGlue.
End HCW.
(* [comment removed for export] *)
