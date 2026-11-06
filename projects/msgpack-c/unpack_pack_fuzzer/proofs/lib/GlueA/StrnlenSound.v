(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Cells Frame ITree Nodes.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib Require ALib.Mem ALib.Step.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore ExecF ITreeA NodesA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Shadow.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AMalloc_iface.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AMalloc_iface2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require I_printf_icpt I_printf_formats.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import RtCells.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Instr State Step Plan PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import Mem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib Defs DefsA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Ledger Op Adeq.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan PlanS CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64Proofs ValProofs MemProofs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import CtrFX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require HeapCtr HeapCtrB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require CallA GlueA CtrPre.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import UnreggSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import StackSh HalfC VprintfC VprintfSound FprintfC FprintfSound StrRegC StrReg FprintfSC MemsetPre RangePre FprintfSSound StrnlenC.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require I_fwrite.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import StrFun.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require InitLib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require UnreggPre.
Unset Nia Cache. Unset Nra Cache.
Import CtrFX ActrA VprintfC FprintfC StrRegC FprintfSC StrnlenC.
Module IS := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.I_fwrite.I_strnlen.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

Definition STRNLEN_SYM : Z := 0x4d7f8.

Definition strnlen_post (st1 : sstate) (r : int) (j : int) (H : sv) (m : w64) : sstate :=
  setpc (addfact (addfact (addfact (setr (clobber st1) X10 (sv_alu ALU_SUB H (VL wone))) (FULt (sv_alu ALU_SUB H (VL wone)) H))
                          (FULt (sv_alu ALU_SUB H (VL wone)) (VL m)))
                 (FEq (sv_ext false 0%uint63 1%uint63 (VBlob false j (sv_alu ALU_SUB H (VL wone)) 1%uint63)) (VL wzero))) r.

Lemma pad_room : forall x y, x <= y -> y mod 8 = 0 -> (- x) mod 8 <= y - x.
Proof.
  intros x y Hxy Hy. pose proof (Z.mod_pos_bound (- x) 8 ltac:(lia)) as B1.
  pose proof (Z.div_mod (- x) 8 ltac:(lia)) as D1. pose proof (Z.div_mod y 8 ltac:(lia)) as D2. rewrite Hy in D2.
  set (q1 := - x / 8) in *. set (q2 := y / 8) in *. set (r := (- x) mod 8) in *. clearbody q1 q2 r. lia.
Qed.

Lemma astrnlen_apply_shape : forall st sts, astrnlen_apply st = Some sts ->
  exists r hargs wnl st1 ks os m rs r12 j sh js,
    acall_pre ASTACK None st = Some (r, hargs, wnl, st1)
    /\ getr st X10 = VP ks os /\ getr st X11 = VL m
    /\ IMap.find ks (s_regs st) = Some rs /\ IMap.find CtrA.STRS_ID (s_regs st) = Some r12
    /\ rg_bg rs = BGBlob j sh /\ rg_cells r12 = IMap.Leaf /\ rg_bg r12 = BGBlob CtrA.STRS_ID 0%uint63
    /\ legal_str j js /\ str_ok_at X10 st wnl j js = true
    /\ rg_hi r12 = CtrA.SZ 15%uint63 /\ rg_lo r12 = 0%uint63
    /\ known_leu (s_facts st) (rg_hi rs) (VL m) = true
    /\ known_leu (s_facts st) (VP CtrA.STRS_ID wzero) (VP ks wzero) = true
    /\ known_leu (s_facts st) (sv_alu ALU_ADD (VP ks wzero) (rg_hi rs)) (sv_alu ALU_ADD (VP CtrA.STRS_ID wzero) (CtrA.SZ 15%uint63)) = true
    /\ aligned (s_facts st) (VP CtrA.STRS_ID wzero) 3%uint63 = true
    /\ sts = [strnlen_post st1 r j (rg_hi rs) m].
Proof.
  intros st sts H. unfold astrnlen_apply in H.
  destruct (acall_pre ASTACK None st) as [[[[r hargs] wnl] st1]|] eqn:P; [|discriminate H].
  destruct (getr st X10) as [|ks os| | | | | | | | |] eqn:G10; try discriminate H.
  destruct (getr st X11) as [m| | | | | | | | | |] eqn:G11; try discriminate H.
  destruct (IMap.find ks (s_regs st)) as [rs|] eqn:Hks; [|discriminate H].
  destruct (IMap.find CtrA.STRS_ID (s_regs st)) as [r12|] eqn:H12; [|discriminate H].
  destruct (rg_bg rs) as [| | | |j sh] eqn:BS; try discriminate H.
  destruct (rg_cells r12) as [|? ? ? ? ?] eqn:C12; [|discriminate H].
  destruct (rg_bg r12) as [| | | |j12 sh12] eqn:B12; try discriminate H.
  cbv zeta in H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:C; [|discriminate H] end.
  injection H as <-.
  repeat match type of C with (_ && _)%bool = true => let X := fresh "Q" in apply andb_prop in C as [C X] end.
  apply Uint63.eqb_correct in Q3, Q4, Q5. subst j12 sh12. apply ValP.sv_eqb_eq in Q6.
  exists r, hargs, wnl, st1, ks, os, m, rs, r12, j, sh, (if PrimInt63.eqb j 1%uint63 then 9%uint63 else 10%uint63).
  repeat (split; [first [reflexivity | assumption]|]).
  split.
  { apply orb_prop in C. destruct C as [C|C]; apply Uint63.eqb_correct in C; subst j; [left|right]; split; reflexivity. }
  repeat (split; [first [reflexivity | assumption]|]). reflexivity.
Qed.

Section Sound.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable Cw : client_world.
Variable OPS : optable.
Hypothesis AI_fake : AI_fake_law AI.
Hypothesis OPS_holds1 : forall args m mo, op_holds OPS HEAP_ID args m mo <-> heap_holdsX AI ACCT UNIV Cw args m mo.
Hypothesis OPS_holds_zarg : forall az m mo, op_holds OPS ZARG_ID [az] m mo -> zarg_holds az m.
Variable OTHER : Model -> Model -> Prop.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Hypothesis PB_str : forall b, PB b -> forall j js, legal_str j js ->
  exists s : list byte, b j = s ++ [Z_to_bv 8 0] /\ Forall (fun x : byte => bv_unsigned x <> 0) s
    /\ b js = Z_to_le_bytes 8 (Z.of_nat (length s) + 1) /\ Z.of_nat (length s) <= 131071.
Hypothesis PB12 : forall E, PB (eb E) -> bv_unsigned (den E (CtrA.SZ 15%uint63)) = Z.of_nat (length (eb E 12%uint63))
                                        /\ Z.of_nat (length (eb E 12%uint63)) mod 8 = 0.
Variable NMAXt : nat.
Notation twfS := (twfA node nstepA nexitA (nsafeA NMAXt) fstepS NMAXt).
Hypothesis ACCT_rng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (ATOP + 4096) (2^47 - (ATOP + 4096)).
Hypothesis ACCT_rng_aimg : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng_aimg RNG.
Hypothesis ACCT_rng_stk_sh : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (shad ATOP) (Shadow.KHIGH - shad ATOP).
Hypothesis ACCT_silent : forall aw L RNG st LBa mo,
  ACCT aw L RNG st LBa mo -> MP mo ->
  exists A0 moc, mrel A0 moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A0 (Ret (Exc.Ok tt)) moc (acct_leaf_silent ACCT OPS OTHER MP mo aw L st LBa).

Lemma slack_bytes : forall E st ms mo ks rs r12 (sstr : list byte),
  st_ok asegs OPS E st ms mo -> PB (eb E) ->
  IMap.find ks (s_regs st) = Some rs -> IMap.find CtrA.STRS_ID (s_regs st) = Some r12 ->
  rg_cells r12 = IMap.Leaf -> rg_bg r12 = BGBlob CtrA.STRS_ID 0%uint63 -> rg_hi r12 = CtrA.SZ 15%uint63 -> rg_lo r12 = 0%uint63 ->
  known_leu (s_facts st) (VP CtrA.STRS_ID wzero) (VP ks wzero) = true ->
  known_leu (s_facts st) (sv_alu ALU_ADD (VP ks wzero) (rg_hi rs)) (sv_alu ALU_ADD (VP CtrA.STRS_ID wzero) (CtrA.SZ 15%uint63)) = true ->
  aligned (s_facts st) (VP CtrA.STRS_ID wzero) 3%uint63 = true ->
  let A := bv_unsigned (ev E ks) in let NS := Z.of_nat (length sstr) + 1 in
  hiZ E rs = NS -> A + NS < 2 ^ 64 ->
  ALib.Mem.bytes_at asegs (ms_mem ms) A (sstr ++ [Z_to_bv 8 0]) ->
  exists slack : list byte,
    ALib.Mem.bytes_at asegs (ms_mem ms) A (sstr ++ Z_to_bv 8 0 :: slack)
    /\ (- (A + Z.of_nat (length sstr) + 1)) mod 8 <= Z.of_nat (length slack) /\ Z.of_nat (length slack) < 8.
Proof.
  intros E st ms mo ks rs r12 sstr HS HPB Hks H12 C12 B12 HI12 LO12 LOW CONT AL A NS HIZ ANS BYT.
  pose proof (so_facts _ _ _ _ _ _ HS) as Hfs.
  set (Bs := bv_unsigned (ev E CtrA.STRS_ID)). set (S12 := bv_unsigned (den E (CtrA.SZ 15%uint63))).
  pose proof (so_reg _ _ _ _ _ _ HS CtrA.STRS_ID r12 H12) as RO12.
  pose proof (ro_range _ _ _ _ _ _ RO12 eq_refl) as [RL12 RH12].
  assert (HI12z : hiZ E r12 = S12) by (unfold hiZ; rewrite HI12; reflexivity).
  assert (LZ12 : loZ r12 = 0) by (unfold loZ; rewrite LO12; reflexivity).
  rewrite HI12z in RH12. rewrite LZ12 in RL12. fold Bs in RL12, RH12. unfold two64 in RH12.
  pose proof (bv_unsigned_in_range _ (ev E ks)) as RA. fold A in RA.
  pose proof (bv_unsigned_in_range _ (den E (CtrA.SZ 15%uint63))) as RS12. fold S12 in RS12.
  apply (HeapCtr.known_leu_sound E _ _ _ Hfs) in LOW. rewrite !HeapCtr.den_VPz in LOW. fold A Bs in LOW.
  apply (HeapCtr.known_leu_sound E _ _ _ Hfs) in CONT. rewrite !ValP.den_sv_alu in CONT. cbn [alu64 alu] in CONT.
  rewrite !bv_add_unsigned, !HeapCtr.den_VPz in CONT. fold A Bs S12 in CONT.
  change (bv_unsigned (den E (rg_hi rs))) with (hiZ E rs) in CONT. rewrite HIZ in CONT.
  pose proof (ValP.aligned_sound E _ Hfs _ _ AL ltac:(change (to_Z 3%uint63) with 3; lia)) as AL8.
  rewrite HeapCtr.den_VPz in AL8. change (2 ^ to_Z 3%uint63) with 8 in AL8. fold Bs in AL8.
  destruct (PB12 E HPB) as [ES12 M8]. fold S12 in ES12.
  assert (CONT' : A + NS <= Bs + S12).
  { rewrite !bv_wrap_small in CONT by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2 ^ 64); unfold NS in *; lia). exact CONT. }
  assert (M8' : (Bs + S12) mod 8 = 0) by (rewrite ES12, Z.add_mod, AL8, M8 by lia; reflexivity).
  set (pad := (- (A + NS)) mod 8).
  pose proof (pad_room (A + NS) (Bs + S12) CONT' M8') as PADR. fold pad in PADR.
  pose proof (Z.mod_pos_bound (- (A + NS)) 8 ltac:(lia)) as PB8. fold pad in PB8.
  set (o := A + NS - Bs).
  set (slack := map (fun i => nth (Z.to_nat o + i)%nat (eb E CtrA.STRS_ID) (Z_to_bv 8 0)) (seq 0 (Z.to_nat pad))).
  assert (LSL : length slack = Z.to_nat pad) by (unfold slack; rewrite length_map, length_seq; reflexivity).
  exists slack. split; [| rewrite LSL, Z2Nat.id by lia; replace (A + Z.of_nat (length sstr) + 1) with (A + NS) by (unfold NS; lia); fold pad; lia].
  change (sstr ++ Z_to_bv 8 0 :: slack) with (sstr ++ ([Z_to_bv 8 0] ++ slack)). rewrite app_assoc.
  set (s0 := sstr ++ [Z_to_bv 8 0]) in *.
  assert (LS0 : Z.of_nat (length s0) = NS) by (unfold s0, NS; rewrite length_app; cbn [length]; lia).
  destruct BYT as (BY0 & BY1 & BY).
  apply bytes_at_of_rbA; [exact BY0 | rewrite length_app, LSL; lia |].
  intros q Hq. rewrite length_app, LSL in Hq.
  destruct (Z_lt_le_dec q NS) as [Q|Q].
  - rewrite app_nth1 by lia. rewrite (GlueA.rb_mrdA asegs). replace (A + q) with (A + Z.of_nat (Z.to_nat q)) by lia.
    rewrite (BY (Z.to_nat q)) by lia. apply nth_error_nth'. lia.
  - rewrite app_nth2 by lia.
    pose proof (ro_bg _ _ _ _ _ _ RO12 (o + (q - NS)) ltac:(intros _; rewrite LZ12, HI12z; unfold o; lia) ltac:(intros K; vm_compute in K; discriminate K)) as BG.
    assert (UNC : uncovered r12 (o + (q - NS))) by (intros g gr _ F; rewrite C12 in F; discriminate F).
    specialize (BG UNC). unfold bg_byte in BG. rewrite B12 in BG. change (to_Z 0%uint63) with 0 in BG. rewrite Z.sub_0_r in BG.
    fold Bs in BG. replace (Bs + (o + (q - NS))) with (A + q) in BG by (unfold o; lia). rewrite BG. f_equal.
    unfold slack. rewrite nth_map_seq by lia. f_equal. lia.
Qed.

Definition astrnlen_leaf : Prop :=
  forall st (K : TSet) E ms mo r hargs wnl st1 ks m rs j (sstr slack : list byte) (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word),
  st_ok asegs OPS E st ms mo -> PB (eb E) ->
  (forall st', In st' [strnlen_post st1 r j (rg_hi rs) m] -> forall E' ms' mo', env_ext (s_next st) E E' -> MP mo' -> st_ok asegs OPS E' st' ms' mo' ->
               realizes asegs (mkCfg ms' mo') K) ->
  acall_pre ASTACK None st = Some (r, hargs, wnl, st1) ->
  getr st X10 = VP ks wzero -> getr st X11 = VL m -> IMap.find ks (s_regs st) = Some rs ->
  eb E j = sstr ++ [Z_to_bv 8 0] -> hiZ E rs = Z.of_nat (length sstr) + 1 -> ~ In (Z_to_bv 8 0) sstr ->
  call_pre st = Some r -> forget_stack_below_sp_g st = Some st1 ->
  CtrPre.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw ->
  AHEAP AI L RNG sta LBa (ms_mem ms) -> ALib.Mem.mem_inv asegs (ms_mem ms) ->
  let R := ms_regs ms in
  ATOP + 4096 <= CtrPre.sp_lo E st -> CtrPre.sp_lo E st <= bv_unsigned (AP.getr R 2) - 4096 ->
  CtrPre.sp_lo E st <= bv_unsigned (AP.getr R 2) - 4384 -> bv_unsigned (AP.getr R 2) < 2 ^ 47 ->
  bv_unsigned (AP.getr R 11) = w2Z m -> Z.of_nat (length sstr) + 1 <= w2Z m ->
  forall ms' mo',
  IS.strnlen_i_post (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
     (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
     (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) (bv_unsigned (AP.getr R 10)) (bv_unsigned (AP.getr R 11))
     (sstr ++ Z_to_bv 8 0 :: slack) (CtrPre.sp_lo E st) (ms_mem ms) ms' ->
  MP mo' -> op_minv OPS mo' -> OTHER mo mo' -> ACCT aw L RNG sta LBa mo' ->
  realizes asegs (mkCfg ms' mo') K.

Theorem astrnlen_sound_of_leaf : astrnlen_leaf ->
  forall pc, to_Z pc = STRNLEN_SYM -> contract_sound asegs OPS MP PB (astrnlen_c pc).
Proof.
  intros LEAF pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply c_pc astrnlen_c] in Happ, Hspc.
  assert (HPC : to_Z (s_pc st) = STRNLEN_SYM) by (rewrite Hspc; exact Hpc).
  destruct (astrnlen_apply_shape st sts Happ) as (r & hargs & wnl & st1 & ks & os & m & rs & r12 & j & sh & js & PRE & G10 & G11 & Hks & H12 & BS & C12 & B12
                                                  & LEG & SOK & HI12 & LO12 & LEm & LOW & CONT & AL & ->).
  destruct (CtrPre.acall_pre_facts0 AI ACCT UNIV Cw OPS AI_fake OPS_holds1 ACCT_rng ASTACK None st r hargs wnl st1 E ms mo HS ltac:(vm_compute; split; congruence) PRE)
    as (L & RNG & sta & LBa & aw & Ems & AH & AC & UIN & MI & ST & BOT & LO & LOR & TP & RA & RR & SPT & SP16 & RSTK & CP & FS & CF).
  change (to_Z ASTACK) with 8192 in LOR.
  pose proof (AI_rtcells AI _ _ _ _ _ AH) as RT.
  set (R := ms_regs ms) in *.
  pose proof atop_range as ATR.

  destruct (str_ok_facts_at AI ACCT UNIV Cw OPS OPS_holds_zarg PB PB_str ACCT_rng ACCT_rng_stk_sh X10 E st ms mo r hargs wnl L RNG sta LBa aw j js HS HPB LEG CF AC BOT LO SPT SOK)
    as (k & rr & sstr & RLO & RHI & (GX & Hk & SRG & KN0 & Bj & HIZ & SAE) & BYT & NOZ & SPA & APB & SPOS & UNP & NSB & HULL & WRH & RNGS & RNGH).
  rewrite G10 in GX. injection GX as -> ->. rewrite Hks in Hk. injection Hk as <-.
  fold R in SAE, BYT, SPA, APB, SPOS, UNP, HULL, RNGS.
  rewrite SAE in BYT, SPA, APB, SPOS, UNP, HULL, RNGS.
  set (A := bv_unsigned (ev E k)) in *. set (NS := Z.of_nat (length sstr) + 1) in *.
  assert (EA0' : bv_unsigned (AP.getr R 10) = A) by exact SAE.
  assert (EA1' : bv_unsigned (AP.getr R 11) = w2Z m).
  { change (AP.getr R 11) with (AP.getr R (reg_of_r5 X11)). unfold R. rewrite (GlueA.getr_RA asegs OPS E st ms mo HS X11), G11. apply unsigned_VL. }
  pose proof (so_facts _ _ _ _ _ _ HS) as Hfs.
  apply (HeapCtr.known_leu_sound E _ _ _ Hfs) in LEm. rewrite unsigned_VL in LEm. change (bv_unsigned (den E (rg_hi rs))) with (hiZ E rs) in LEm. rewrite HIZ in LEm.
  assert (NONUL : ~ In (Z_to_bv 8 0) sstr).
  { intros IN. apply (proj1 (Forall_forall _ _) NOZ _ IN). rewrite Z_to_bv_unsigned. reflexivity. }
  destruct (slack_bytes E st ms mo k rs r12 sstr HS HPB Hks H12 C12 B12 HI12 LO12 LOW CONT AL HIZ
              ltac:(fold A NS; destruct APB as [_ [[_ Q]|[_ Q]]]; unfold Shadow.KLOW, Shadow.KEND in Q; lia) BYT) as (slack & BUF & PAD & SL8).
  fold A in BUF, PAD. set (buf := sstr ++ Z_to_bv 8 0 :: slack) in *.
  assert (LBUF : Z.of_nat (length buf) = NS + Z.of_nat (length slack)) by (unfold buf, NS; rewrite length_app; cbn [length]; lia).
  assert (HITL : IS.hitlen 0 (bv_unsigned (AP.getr R 11)) buf = NS).
  { unfold IS.hitlen, buf. rewrite (find_byte_cstr A _ sstr slack NONUL) by (rewrite EA1'; unfold NS in LEm; lia). reflexivity. }
  assert (MOK : memchr_ok A 0 (bv_unsigned (AP.getr R 11)) buf) by (apply (memchr_ok_cstr A _ sstr slack NONUL PAD)).
  assert (RNGB : rng RNG A (Z.of_nat (length buf))).
  { apply (rng_sub _ _ _ _ _ (ACCT_rng _ _ _ _ _ _ AC)); [lia|]. rewrite LBUF. destruct APB as [_ [[_ Q]|[_ Q]]]; unfold Shadow.KLOW, Shadow.KEND in Q; lia. }
  idtac "SN-1".
  destruct (ACCT_silent aw L RNG sta LBa mo AC HMP) as (AL0 & moc & MR & MINV & HH & TW).
  pose proof (ACCT_rng_aimg _ _ _ _ _ _ AC) as RIMG.
  assert (EV : evtF asegs RNG
            (IS.strnlen_i_post (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
               (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
               (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) (bv_unsigned (AP.getr R 10)) (bv_unsigned (AP.getr R 11)) buf
               (CtrPre.sp_lo E st) (ms_mem ms))
            (MS (mkR (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 5) (AP.getr R 6) (AP.getr R 7) (AP.getr R 8)
                (AP.getr R 9) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16)
                (AP.getr R 17) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
                (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (AP.getr R 28) (AP.getr R 29) (AP.getr R 30) (AP.getr R 31))
                (ms_fregs ms) (Z_to_bv 64 STRNLEN_SYM) (ms_fcsr ms) None (ms_mem ms) (seg_rom asegs))).
  { unfold artcells in RT. decompose [and] RT. clear RT.
    pose proof (IS.strnlen_i_spec RNG (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 5) (AP.getr R 6) (AP.getr R 7) (AP.getr R 8)
                (AP.getr R 9) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16)
                (AP.getr R 17) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
                (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (AP.getr R 28) (AP.getr R 29) (AP.getr R 30) (AP.getr R 31)
                (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) (CtrPre.sp_lo E st) buf RLO RHI) as W.
    cbv zeta in W. apply W.
    all: rewrite ?HITL, ?EA0'.
    all: try lazymatch goal with
         | |- ALib.Mem.mem_inv _ _ => exact MI
         | |- stk _ _ _ _ => exact ST
         | |- ALib.Step.rw_cells _ _ _ _ => assumption
         | |- ALib.Mem.bytes_at _ _ _ _ => exact BUF
         | |- memchr_ok _ _ _ _ => exact MOK
         | |- Shadow.app_blk _ _ => exact APB
         | |- Shadow.unpoisoned _ _ _ => exact UNP
         | |- ALib.Mem.wr_at _ _ _ _ => exact WRH
         | |- rng_aimg _ => exact RIMG
         | |- rng _ (shad _) _ => exact RNGH
         | |- rng _ _ _ => first [exact RSTK | exact RNGB | exact RIMG]
         | |- _ <= _ /\ _ => exact HULL
         | |- _ \/ _ => right; exact SPA
         end.
    all: try (unfold Shadow.KHIGH in *; lia).
    all: match goal with |- ?G => idtac "REMW" G end. }
  rewrite Ems, HPC. apply (GlueA.realizes_to_mkRA asegs).
  eapply (implS_twfS_realizes_silent asegs NMAXt (Ret (Exc.Ok tt)) RNG AL0
            (fun (_ : unit) (RNGq : footprint) ms' => RNGq = RNG /\ IS.strnlen_i_post (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
               (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
               (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) (bv_unsigned (AP.getr R 10)) (bv_unsigned (AP.getr R 11)) buf
               (CtrPre.sp_lo E st) (ms_mem ms) ms')
            _ _ moc mo K).
  - cbn [implF epostF]. eapply evtF_mono; [exact EV|]. intros ms' PO. split; [reflexivity| exact PO].
  - exact TW.
  - exact HH.
  - exact MINV.
  - exact MR.
  - intros rr RNG' A' ms' moc' mo' HQ HP' ACC' HH' MINV' MR'.
    destruct (HP' mo' MR') as (HMP' & HMI' & OTH & ACP). destruct HQ as [-> HQ].
    exact (LEAF st K E ms mo r hargs wnl st1 k m rs j sstr slack L RNG sta LBa aw HS HPB HK PRE G10 G11 Hks Bj HIZ NONUL CP FS CF AH MI BOT LO
             ltac:(fold R; lia) SPT EA1' LEm ms' mo' HQ HMP' HMI' OTH ACP).
Qed.
End Sound.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.AcctCore OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.NodesA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB AMalloc_iface.TwinB.
Import AMalloc_iface2.TwinB.
Import RtCells.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.PlanSound.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap.Op.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Defs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA.
Import Ledger.TwinB Op.TwinB Adeq.TwinB.

Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan PlanS CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

Import Actr.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CtrFX.

Import UnreggSound.TwinB.
Import StackSh.TwinB HalfC.TwinB VprintfC.TwinB VprintfSound.TwinB FprintfC.TwinB FprintfSound.TwinB StrRegC.TwinB StrReg.TwinB FprintfSC.TwinB MemsetPre.TwinB RangePre.TwinB FprintfSSound.TwinB StrnlenC.TwinB.

Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.StrFun.

Unset Nia Cache. Unset Nra Cache.
Import CtrFX ActrA VprintfC.TwinB.VprintfC FprintfC.TwinB.FprintfC StrRegC.TwinB.StrRegC FprintfSC.TwinB.FprintfSC StrnlenC.TwinB.StrnlenC.
Module IS := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.I_fwrite.TwinB.I_strnlen.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

Definition STRNLEN_SYM : Z := 0x4e188.

Definition strnlen_post (st1 : sstate) (r : int) (j : int) (H : sv) (m : w64) : sstate :=
  setpc (addfact (addfact (addfact (setr (clobber st1) X10 (sv_alu ALU_SUB H (VL wone))) (FULt (sv_alu ALU_SUB H (VL wone)) H))
                          (FULt (sv_alu ALU_SUB H (VL wone)) (VL m)))
                 (FEq (sv_ext false 0%uint63 1%uint63 (VBlob false j (sv_alu ALU_SUB H (VL wone)) 1%uint63)) (VL wzero))) r.

Lemma pad_room : forall x y, x <= y -> y mod 8 = 0 -> (- x) mod 8 <= y - x.
Proof.
  intros x y Hxy Hy. pose proof (Z.mod_pos_bound (- x) 8 ltac:(lia)) as B1.
  pose proof (Z.div_mod (- x) 8 ltac:(lia)) as D1. pose proof (Z.div_mod y 8 ltac:(lia)) as D2. rewrite Hy in D2.
  set (q1 := - x / 8) in *. set (q2 := y / 8) in *. set (r := (- x) mod 8) in *. clearbody q1 q2 r. lia.
Qed.

Lemma astrnlen_apply_shape : forall st sts, astrnlen_apply st = Some sts ->
  exists r hargs wnl st1 ks os m rs r12 j sh js,
    acall_pre ASTACK None st = Some (r, hargs, wnl, st1)
    /\ getr st X10 = VP ks os /\ getr st X11 = VL m
    /\ IMap.find ks (s_regs st) = Some rs /\ IMap.find CtrA.STRS_ID (s_regs st) = Some r12
    /\ rg_bg rs = BGBlob j sh /\ rg_cells r12 = IMap.Leaf /\ rg_bg r12 = BGBlob CtrA.STRS_ID 0%uint63
    /\ legal_str j js /\ str_ok_at X10 st wnl j js = true
    /\ rg_hi r12 = CtrA.SZ 15%uint63 /\ rg_lo r12 = 0%uint63
    /\ known_leu (s_facts st) (rg_hi rs) (VL m) = true
    /\ known_leu (s_facts st) (VP CtrA.STRS_ID wzero) (VP ks wzero) = true
    /\ known_leu (s_facts st) (sv_alu ALU_ADD (VP ks wzero) (rg_hi rs)) (sv_alu ALU_ADD (VP CtrA.STRS_ID wzero) (CtrA.SZ 15%uint63)) = true
    /\ aligned (s_facts st) (VP CtrA.STRS_ID wzero) 3%uint63 = true
    /\ sts = [strnlen_post st1 r j (rg_hi rs) m].
Proof.
  intros st sts H. unfold astrnlen_apply in H.
  destruct (acall_pre ASTACK None st) as [[[[r hargs] wnl] st1]|] eqn:P; [|discriminate H].
  destruct (getr st X10) as [|ks os| | | | | | | | |] eqn:G10; try discriminate H.
  destruct (getr st X11) as [m| | | | | | | | | |] eqn:G11; try discriminate H.
  destruct (IMap.find ks (s_regs st)) as [rs|] eqn:Hks; [|discriminate H].
  destruct (IMap.find CtrA.STRS_ID (s_regs st)) as [r12|] eqn:H12; [|discriminate H].
  destruct (rg_bg rs) as [| | | |j sh] eqn:BS; try discriminate H.
  destruct (rg_cells r12) as [|? ? ? ? ?] eqn:C12; [|discriminate H].
  destruct (rg_bg r12) as [| | | |j12 sh12] eqn:B12; try discriminate H.
  cbv zeta in H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:C; [|discriminate H] end.
  injection H as <-.
  repeat match type of C with (_ && _)%bool = true => let X := fresh "Q" in apply andb_prop in C as [C X] end.
  apply Uint63.eqb_correct in Q3, Q4, Q5. subst j12 sh12. apply ValP.sv_eqb_eq in Q6.
  exists r, hargs, wnl, st1, ks, os, m, rs, r12, j, sh, (if PrimInt63.eqb j 1%uint63 then 9%uint63 else 10%uint63).
  repeat (split; [first [reflexivity | assumption]|]).
  split.
  { apply orb_prop in C. destruct C as [C|C]; apply Uint63.eqb_correct in C; subst j; [left|right]; split; reflexivity. }
  repeat (split; [first [reflexivity | assumption]|]). reflexivity.
Qed.

Section Sound.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable Cw : client_world.
Variable OPS : optable.
Hypothesis AI_fake : AI_fake_law AI.
Hypothesis OPS_holds1 : forall args m mo, op_holds OPS HEAP_ID args m mo <-> heap_holdsX AI ACCT UNIV Cw args m mo.
Hypothesis OPS_holds_zarg : forall az m mo, op_holds OPS ZARG_ID [az] m mo -> zarg_holds az m.
Variable OTHER : Model -> Model -> Prop.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Hypothesis PB_str : forall b, PB b -> forall j js, legal_str j js ->
  exists s : list byte, b j = s ++ [Z_to_bv 8 0] /\ Forall (fun x : byte => bv_unsigned x <> 0) s
    /\ b js = Z_to_le_bytes 8 (Z.of_nat (length s) + 1) /\ Z.of_nat (length s) <= 131071.
Hypothesis PB12 : forall E, PB (eb E) -> bv_unsigned (den E (CtrA.SZ 15%uint63)) = Z.of_nat (length (eb E 12%uint63))
                                        /\ Z.of_nat (length (eb E 12%uint63)) mod 8 = 0.
Variable NMAXt : nat.
Notation twfS := (twfA node nstepA nexitA (nsafeA NMAXt) fstepS NMAXt).
Hypothesis ACCT_rng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (ATOP + 4096) (2^47 - (ATOP + 4096)).
Hypothesis ACCT_rng_aimg : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng_aimg RNG.
Hypothesis ACCT_rng_stk_sh : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (shad ATOP) (Shadow.KHIGH - shad ATOP).
Hypothesis ACCT_silent : forall aw L RNG st LBa mo,
  ACCT aw L RNG st LBa mo -> MP mo ->
  exists A0 moc, mrel A0 moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A0 (Ret (Exc.Ok tt)) moc (acct_leaf_silent ACCT OPS OTHER MP mo aw L st LBa).

Lemma slack_bytes : forall E st ms mo ks rs r12 (sstr : list byte),
  st_ok bsegs OPS E st ms mo -> PB (eb E) ->
  IMap.find ks (s_regs st) = Some rs -> IMap.find CtrA.STRS_ID (s_regs st) = Some r12 ->
  rg_cells r12 = IMap.Leaf -> rg_bg r12 = BGBlob CtrA.STRS_ID 0%uint63 -> rg_hi r12 = CtrA.SZ 15%uint63 -> rg_lo r12 = 0%uint63 ->
  known_leu (s_facts st) (VP CtrA.STRS_ID wzero) (VP ks wzero) = true ->
  known_leu (s_facts st) (sv_alu ALU_ADD (VP ks wzero) (rg_hi rs)) (sv_alu ALU_ADD (VP CtrA.STRS_ID wzero) (CtrA.SZ 15%uint63)) = true ->
  aligned (s_facts st) (VP CtrA.STRS_ID wzero) 3%uint63 = true ->
  let A := bv_unsigned (ev E ks) in let NS := Z.of_nat (length sstr) + 1 in
  hiZ E rs = NS -> A + NS < 2 ^ 64 ->
  ALib.Mem.bytes_at bsegs (ms_mem ms) A (sstr ++ [Z_to_bv 8 0]) ->
  exists slack : list byte,
    ALib.Mem.bytes_at bsegs (ms_mem ms) A (sstr ++ Z_to_bv 8 0 :: slack)
    /\ (- (A + Z.of_nat (length sstr) + 1)) mod 8 <= Z.of_nat (length slack) /\ Z.of_nat (length slack) < 8.
Proof.
  intros E st ms mo ks rs r12 sstr HS HPB Hks H12 C12 B12 HI12 LO12 LOW CONT AL A NS HIZ ANS BYT.
  pose proof (so_facts _ _ _ _ _ _ HS) as Hfs.
  set (Bs := bv_unsigned (ev E CtrA.STRS_ID)). set (S12 := bv_unsigned (den E (CtrA.SZ 15%uint63))).
  pose proof (so_reg _ _ _ _ _ _ HS CtrA.STRS_ID r12 H12) as RO12.
  pose proof (ro_range _ _ _ _ _ _ RO12 eq_refl) as [RL12 RH12].
  assert (HI12z : hiZ E r12 = S12) by (unfold hiZ; rewrite HI12; reflexivity).
  assert (LZ12 : loZ r12 = 0) by (unfold loZ; rewrite LO12; reflexivity).
  rewrite HI12z in RH12. rewrite LZ12 in RL12. fold Bs in RL12, RH12. unfold two64 in RH12.
  pose proof (bv_unsigned_in_range _ (ev E ks)) as RA. fold A in RA.
  pose proof (bv_unsigned_in_range _ (den E (CtrA.SZ 15%uint63))) as RS12. fold S12 in RS12.
  apply (HeapCtr.TwinB.known_leu_sound E _ _ _ Hfs) in LOW. rewrite !HeapCtr.TwinB.den_VPz in LOW. fold A Bs in LOW.
  apply (HeapCtr.TwinB.known_leu_sound E _ _ _ Hfs) in CONT. rewrite !ValP.den_sv_alu in CONT. cbn [alu64 alu] in CONT.
  rewrite !bv_add_unsigned, !HeapCtr.TwinB.den_VPz in CONT. fold A Bs S12 in CONT.
  change (bv_unsigned (den E (rg_hi rs))) with (hiZ E rs) in CONT. rewrite HIZ in CONT.
  pose proof (ValP.aligned_sound E _ Hfs _ _ AL ltac:(change (to_Z 3%uint63) with 3; lia)) as AL8.
  rewrite HeapCtr.TwinB.den_VPz in AL8. change (2 ^ to_Z 3%uint63) with 8 in AL8. fold Bs in AL8.
  destruct (PB12 E HPB) as [ES12 M8]. fold S12 in ES12.
  assert (CONT' : A + NS <= Bs + S12).
  { rewrite !bv_wrap_small in CONT by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2 ^ 64); unfold NS in *; lia). exact CONT. }
  assert (M8' : (Bs + S12) mod 8 = 0) by (rewrite ES12, Z.add_mod, AL8, M8 by lia; reflexivity).
  set (pad := (- (A + NS)) mod 8).
  pose proof (pad_room (A + NS) (Bs + S12) CONT' M8') as PADR. fold pad in PADR.
  pose proof (Z.mod_pos_bound (- (A + NS)) 8 ltac:(lia)) as PB8. fold pad in PB8.
  set (o := A + NS - Bs).
  set (slack := map (fun i => nth (Z.to_nat o + i)%nat (eb E CtrA.STRS_ID) (Z_to_bv 8 0)) (seq 0 (Z.to_nat pad))).
  assert (LSL : length slack = Z.to_nat pad) by (unfold slack; rewrite length_map, length_seq; reflexivity).
  exists slack. split; [| rewrite LSL, Z2Nat.id by lia; replace (A + Z.of_nat (length sstr) + 1) with (A + NS) by (unfold NS; lia); fold pad; lia].
  change (sstr ++ Z_to_bv 8 0 :: slack) with (sstr ++ ([Z_to_bv 8 0] ++ slack)). rewrite app_assoc.
  set (s0 := sstr ++ [Z_to_bv 8 0]) in *.
  assert (LS0 : Z.of_nat (length s0) = NS) by (unfold s0, NS; rewrite length_app; cbn [length]; lia).
  destruct BYT as (BY0 & BY1 & BY).
  apply bytes_at_of_rbA; [exact BY0 | rewrite length_app, LSL; lia |].
  intros q Hq. rewrite length_app, LSL in Hq.
  destruct (Z_lt_le_dec q NS) as [Q|Q].
  - rewrite app_nth1 by lia. rewrite (GlueA.TwinB.rb_mrdA bsegs). replace (A + q) with (A + Z.of_nat (Z.to_nat q)) by lia.
    rewrite (BY (Z.to_nat q)) by lia. apply nth_error_nth'. lia.
  - rewrite app_nth2 by lia.
    pose proof (ro_bg _ _ _ _ _ _ RO12 (o + (q - NS)) ltac:(intros _; rewrite LZ12, HI12z; unfold o; lia) ltac:(intros K; vm_compute in K; discriminate K)) as BG.
    assert (UNC : uncovered r12 (o + (q - NS))) by (intros g gr _ F; rewrite C12 in F; discriminate F).
    specialize (BG UNC). unfold bg_byte in BG. rewrite B12 in BG. change (to_Z 0%uint63) with 0 in BG. rewrite Z.sub_0_r in BG.
    fold Bs in BG. replace (Bs + (o + (q - NS))) with (A + q) in BG by (unfold o; lia). rewrite BG. f_equal.
    unfold slack. rewrite nth_map_seq by lia. f_equal. lia.
Qed.

Definition astrnlen_leaf : Prop :=
  forall st (K : TSet) E ms mo r hargs wnl st1 ks m rs j (sstr slack : list byte) (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word),
  st_ok bsegs OPS E st ms mo -> PB (eb E) ->
  (forall st', In st' [strnlen_post st1 r j (rg_hi rs) m] -> forall E' ms' mo', env_ext (s_next st) E E' -> MP mo' -> st_ok bsegs OPS E' st' ms' mo' ->
               realizes bsegs (mkCfg ms' mo') K) ->
  acall_pre ASTACK None st = Some (r, hargs, wnl, st1) ->
  getr st X10 = VP ks wzero -> getr st X11 = VL m -> IMap.find ks (s_regs st) = Some rs ->
  eb E j = sstr ++ [Z_to_bv 8 0] -> hiZ E rs = Z.of_nat (length sstr) + 1 -> ~ In (Z_to_bv 8 0) sstr ->
  call_pre st = Some r -> forget_stack_below_sp_g st = Some st1 ->
  CtrPre.TwinB.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw ->
  AHEAP AI L RNG sta LBa (ms_mem ms) -> ALib.Mem.mem_inv bsegs (ms_mem ms) ->
  let R := ms_regs ms in
  ATOP + 4096 <= CtrPre.TwinB.sp_lo E st -> CtrPre.TwinB.sp_lo E st <= bv_unsigned (AP.getr R 2) - 4096 ->
  CtrPre.TwinB.sp_lo E st <= bv_unsigned (AP.getr R 2) - 4384 -> bv_unsigned (AP.getr R 2) < 2 ^ 47 ->
  bv_unsigned (AP.getr R 11) = w2Z m -> Z.of_nat (length sstr) + 1 <= w2Z m ->
  forall ms' mo',
  IS.strnlen_i_post (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
     (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
     (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) (bv_unsigned (AP.getr R 10)) (bv_unsigned (AP.getr R 11))
     (sstr ++ Z_to_bv 8 0 :: slack) (CtrPre.TwinB.sp_lo E st) (ms_mem ms) ms' ->
  MP mo' -> op_minv OPS mo' -> OTHER mo mo' -> ACCT aw L RNG sta LBa mo' ->
  realizes bsegs (mkCfg ms' mo') K.

Theorem astrnlen_sound_of_leaf : astrnlen_leaf ->
  forall pc, to_Z pc = STRNLEN_SYM -> contract_sound bsegs OPS MP PB (astrnlen_c pc).
Proof.
  intros LEAF pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply c_pc astrnlen_c] in Happ, Hspc.
  assert (HPC : to_Z (s_pc st) = STRNLEN_SYM) by (rewrite Hspc; exact Hpc).
  destruct (astrnlen_apply_shape st sts Happ) as (r & hargs & wnl & st1 & ks & os & m & rs & r12 & j & sh & js & PRE & G10 & G11 & Hks & H12 & BS & C12 & B12
                                                  & LEG & SOK & HI12 & LO12 & LEm & LOW & CONT & AL & ->).
  destruct (CtrPre.TwinB.acall_pre_facts0 AI ACCT UNIV Cw OPS AI_fake OPS_holds1 ACCT_rng ASTACK None st r hargs wnl st1 E ms mo HS ltac:(vm_compute; split; congruence) PRE)
    as (L & RNG & sta & LBa & aw & Ems & AH & AC & UIN & MI & ST & BOT & LO & LOR & TP & RA & RR & SPT & SP16 & RSTK & CP & FS & CF).
  change (to_Z ASTACK) with 8192 in LOR.
  pose proof (AI_rtcells AI _ _ _ _ _ AH) as RT.
  set (R := ms_regs ms) in *.
  pose proof atop_range as ATR.

  destruct (str_ok_facts_at AI ACCT UNIV Cw OPS OPS_holds_zarg PB PB_str ACCT_rng ACCT_rng_stk_sh X10 E st ms mo r hargs wnl L RNG sta LBa aw j js HS HPB LEG CF AC BOT LO SPT SOK)
    as (k & rr & sstr & RLO & RHI & (GX & Hk & SRG & KN0 & Bj & HIZ & SAE) & BYT & NOZ & SPA & APB & SPOS & UNP & NSB & HULL & WRH & RNGS & RNGH).
  rewrite G10 in GX. injection GX as -> ->. rewrite Hks in Hk. injection Hk as <-.
  fold R in SAE, BYT, SPA, APB, SPOS, UNP, HULL, RNGS.
  rewrite SAE in BYT, SPA, APB, SPOS, UNP, HULL, RNGS.
  set (A := bv_unsigned (ev E k)) in *. set (NS := Z.of_nat (length sstr) + 1) in *.
  assert (EA0' : bv_unsigned (AP.getr R 10) = A) by exact SAE.
  assert (EA1' : bv_unsigned (AP.getr R 11) = w2Z m).
  { change (AP.getr R 11) with (AP.getr R (reg_of_r5 X11)). unfold R. rewrite (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X11), G11. apply unsigned_VL. }
  pose proof (so_facts _ _ _ _ _ _ HS) as Hfs.
  apply (HeapCtr.TwinB.known_leu_sound E _ _ _ Hfs) in LEm. rewrite unsigned_VL in LEm. change (bv_unsigned (den E (rg_hi rs))) with (hiZ E rs) in LEm. rewrite HIZ in LEm.
  assert (NONUL : ~ In (Z_to_bv 8 0) sstr).
  { intros IN. apply (proj1 (Forall_forall _ _) NOZ _ IN). rewrite Z_to_bv_unsigned. reflexivity. }
  destruct (slack_bytes E st ms mo k rs r12 sstr HS HPB Hks H12 C12 B12 HI12 LO12 LOW CONT AL HIZ
              ltac:(fold A NS; destruct APB as [_ [[_ Q]|[_ Q]]]; unfold Shadow.KLOW, Shadow.KEND in Q; lia) BYT) as (slack & BUF & PAD & SL8).
  fold A in BUF, PAD. set (buf := sstr ++ Z_to_bv 8 0 :: slack) in *.
  assert (LBUF : Z.of_nat (length buf) = NS + Z.of_nat (length slack)) by (unfold buf, NS; rewrite length_app; cbn [length]; lia).
  assert (HITL : IS.hitlen 0 (bv_unsigned (AP.getr R 11)) buf = NS).
  { unfold IS.hitlen, buf. rewrite (find_byte_cstr A _ sstr slack NONUL) by (rewrite EA1'; unfold NS in LEm; lia). reflexivity. }
  assert (MOK : memchr_ok A 0 (bv_unsigned (AP.getr R 11)) buf) by (apply (memchr_ok_cstr A _ sstr slack NONUL PAD)).
  assert (RNGB : rng RNG A (Z.of_nat (length buf))).
  { apply (rng_sub _ _ _ _ _ (ACCT_rng _ _ _ _ _ _ AC)); [lia|]. rewrite LBUF. destruct APB as [_ [[_ Q]|[_ Q]]]; unfold Shadow.KLOW, Shadow.KEND in Q; lia. }
  idtac "SN-1".
  destruct (ACCT_silent aw L RNG sta LBa mo AC HMP) as (AL0 & moc & MR & MINV & HH & TW).
  pose proof (ACCT_rng_aimg _ _ _ _ _ _ AC) as RIMG.
  assert (EV : evtF bsegs RNG
            (IS.strnlen_i_post (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
               (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
               (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) (bv_unsigned (AP.getr R 10)) (bv_unsigned (AP.getr R 11)) buf
               (CtrPre.TwinB.sp_lo E st) (ms_mem ms))
            (MS (mkR (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 5) (AP.getr R 6) (AP.getr R 7) (AP.getr R 8)
                (AP.getr R 9) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16)
                (AP.getr R 17) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
                (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (AP.getr R 28) (AP.getr R 29) (AP.getr R 30) (AP.getr R 31))
                (ms_fregs ms) (Z_to_bv 64 STRNLEN_SYM) (ms_fcsr ms) None (ms_mem ms) (seg_rom bsegs))).
  { unfold artcells in RT. decompose [and] RT. clear RT.
    pose proof (IS.strnlen_i_spec RNG (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 5) (AP.getr R 6) (AP.getr R 7) (AP.getr R 8)
                (AP.getr R 9) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16)
                (AP.getr R 17) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
                (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (AP.getr R 28) (AP.getr R 29) (AP.getr R 30) (AP.getr R 31)
                (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) (CtrPre.TwinB.sp_lo E st) buf RLO RHI) as W.
    cbv zeta in W. apply W.
    all: rewrite ?HITL, ?EA0'.
    all: try lazymatch goal with
         | |- ALib.Mem.mem_inv _ _ => exact MI
         | |- stk _ _ _ _ => exact ST
         | |- ALib.Step.rw_cells _ _ _ _ => assumption
         | |- ALib.Mem.bytes_at _ _ _ _ => exact BUF
         | |- memchr_ok _ _ _ _ => exact MOK
         | |- Shadow.app_blk _ _ => exact APB
         | |- Shadow.unpoisoned _ _ _ => exact UNP
         | |- ALib.Mem.wr_at _ _ _ _ => exact WRH
         | |- rng_aimg _ => exact RIMG
         | |- rng _ (shad _) _ => exact RNGH
         | |- rng _ _ _ => first [exact RSTK | exact RNGB | exact RIMG]
         | |- _ <= _ /\ _ => exact HULL
         | |- _ \/ _ => right; exact SPA
         end.
    all: try (unfold Shadow.KHIGH in *; lia).
    all: match goal with |- ?G => idtac "REMW" G end. }
  rewrite Ems, HPC. apply (GlueA.TwinB.realizes_to_mkRA bsegs).
  eapply (implS_twfS_realizes_silent bsegs NMAXt (Ret (Exc.Ok tt)) RNG AL0
            (fun (_ : unit) (RNGq : footprint) ms' => RNGq = RNG /\ IS.strnlen_i_post (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
               (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
               (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) (bv_unsigned (AP.getr R 10)) (bv_unsigned (AP.getr R 11)) buf
               (CtrPre.TwinB.sp_lo E st) (ms_mem ms) ms')
            _ _ moc mo K).
  - cbn [implF epostF]. eapply evtF_mono; [exact EV|]. intros ms' PO. split; [reflexivity| exact PO].
  - exact TW.
  - exact HH.
  - exact MINV.
  - exact MR.
  - intros rr RNG' A' ms' moc' mo' HQ HP' ACC' HH' MINV' MR'.
    destruct (HP' mo' MR') as (HMP' & HMI' & OTH & ACP). destruct HQ as [-> HQ].
    exact (LEAF st K E ms mo r hargs wnl st1 k m rs j sstr slack L RNG sta LBa aw HS HPB HK PRE G10 G11 Hks Bj HIZ NONUL CP FS CF AH MI BOT LO
             ltac:(fold R; lia) SPT EA1' LEm ms' mo' HQ HMP' HMI' OTH ACP).
Qed.
End Sound.
End TwinB.
