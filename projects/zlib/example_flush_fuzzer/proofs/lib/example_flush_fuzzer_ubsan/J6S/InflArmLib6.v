(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require SymExec.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac AllocSim.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Prog ZIface InflateState InflateFast InflateArms Inflate InflateInv InflateInvDec.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Import Segs6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import ISLayout IS6 InflMem InflRod6 InflCtx6.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.


Section ArmFor.
  Variables (iv : ivariant) (flush : Z).
  Definition arm_for (m : Z) : AM unit :=
    if m =? HEAD then arm_HEAD iv
    else if m =? FLAGS then arm_FLAGS
    else if m =? TIME then arm_TIME
    else if m =? OS then arm_OS
    else if m =? EXLEN then arm_EXLEN
    else if m =? EXTRA then arm_EXTRA
    else if m =? NAME then arm_NAME
    else if m =? COMMENT then arm_COMMENT
    else if m =? HCRC then arm_HCRC
    else if m =? DICTID then arm_DICTID iv flush
    else if m =? DICT then arm_DICT iv flush
    else if m =? TYPE then arm_TYPE iv flush
    else if m =? TYPEDO then arm_TYPEDO iv flush
    else if m =? STORED then arm_STORED iv flush
    else if m =? COPY_ then arm_COPY_
    else if m =? COPY then arm_COPY
    else if m =? TABLE then arm_TABLE iv flush
    else if m =? LENLENS then arm_LENLENS iv flush
    else if m =? CODELENS then arm_CODELENS iv flush
    else if m =? LEN_ then arm_LEN_ iv
    else if m =? LEN then arm_LEN iv
    else if m =? LENEXT then arm_LENEXT iv
    else if m =? DIST then arm_DIST iv
    else if m =? DISTEXT then arm_DISTEXT iv
    else if m =? MATCH then arm_MATCH iv
    else if m =? LIT then arm_LIT
    else if m =? CHECK then arm_CHECK
    else if m =? LENGTH then arm_LENGTH
    else if m =? DONE then arm_DONE
    else if m =? BAD then arm_BAD
    else if m =? MEM then arm_MEM
    else arm_SYNC.

  Lemma dispatch_eq : forall w, dispatch iv flush w = arm_for (is_mode (w_s w)) w.
  Proof. intros w. unfold dispatch, arm_for, abind, gs. reflexivity. Qed.
End ArmFor.


Lemma gr_eq : forall {A} (f : iregs -> A) s c r, gr f (mkW s c r) = ARun (f r) (mkW s c r).
Proof. reflexivity. Qed.
Lemma gs_eq : forall {A} (f : inflate_state -> A) s c r, gs f (mkW s c r) = ARun (f s) (mkW s c r).
Proof. reflexivity. Qed.
Lemma us_eq : forall f s c r, us f (mkW s c r) = ARun tt (mkW (f s) c r).
Proof. reflexivity. Qed.
Lemma uc_eq : forall f s c r, uc f (mkW s c r) = ARun tt (mkW s (f c) r).
Proof. reflexivity. Qed.
Lemma ur_eq : forall f s c r, ur f (mkW s c r) = ARun tt (mkW s c (f r)).
Proof. reflexivity. Qed.
Lemma aret_eq : forall {A} (a : A) w, aret a w = ARun a w.
Proof. reflexivity. Qed.
Lemma aleave_eq : forall {A} w, @aleave A w = ALeave w.
Proof. reflexivity. Qed.
Lemma BITS_eq : forall n s c r, BITS n (mkW s c r) = ARun (BITSv (ir_hold r) n) (mkW s c r).
Proof. reflexivity. Qed.
Lemma HOLD_eq : forall s c r, HOLD (mkW s c r) = ARun (ir_hold r) (mkW s c r).
Proof. reflexivity. Qed.
Lemma DROPBITS_eq : forall n s c r,
  DROPBITS n (mkW s c r) = ARun tt (mkW s c (irset_bits (irset_hold r (Z.shiftr (ir_hold r) n)) (wrap32 (ir_bits r - n)))).
Proof. reflexivity. Qed.
Lemma INITBITS_eq : forall s c r, INITBITS (mkW s c r) = ARun tt (mkW s c (irset_bits (irset_hold r 0) 0)).
Proof. reflexivity. Qed.
Lemma BYTEBITS_eq : forall s c r,
  BYTEBITS (mkW s c r) = ARun tt (mkW s c (irset_bits (irset_hold r (Z.shiftr (ir_hold r) (Z.land (ir_bits r) 7))) (wrap32 (ir_bits r - Z.land (ir_bits r) 7)))).
Proof. reflexivity. Qed.
Lemma set_mode_eq : forall m s c r, set_mode m (mkW s c r) = ARun tt (mkW (iset_mode s m) c r).
Proof. reflexivity. Qed.
Lemma go_bad_eq : forall m s c r, go_bad m (mkW s c r) = ARun tt (mkW (iset_mode s BAD) (icset_msg c m) r).
Proof. reflexivity. Qed.
Lemma set_adler_check_eq : forall v s c r, set_adler_check v (mkW s c r) = ARun tt (mkW (iset_check s v) (icset_adler c v) r).
Proof. reflexivity. Qed.

End FXG.
Ltac mstep1 lem := rewrite abind_run; rewrite lem; cbv beta iota.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.
End FXG.
Ltac irnorm := cbv beta iota delta [irset_next irset_have irset_put irset_left irset_hold irset_bits irset_in irset_out irset_ret
                                   w_s w_c w_r wset_s wset_c wset_r];
               cbn [ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Definition pullr (c : icall) (r : iregs) : iregs :=
  mkIR (ir_next r + 1) (wrap32 (ir_have r - 1)) (ir_put r) (ir_left r)
       (wrap64 (ir_hold r + shl64 (arr_get (ic_input c) (ir_next r)) (ir_bits r))) (wrap32 (ir_bits r + 8))
       (ir_in r) (ir_out r) (ir_ret r).

Lemma PULLBYTE_eq : forall s c r,
  PULLBYTE (mkW s c r) = if ir_have r =? 0 then ALeave (mkW s c r) else ARun tt (mkW s c (pullr c r)).
Proof. intros. reflexivity. Qed.

Lemma NEEDBITS_k_S : forall k n s c r,
  NEEDBITS_k (S k) n (mkW s c r)
  = if ir_bits r <? n then
      (if ir_have r =? 0 then ALeave (mkW s c r) else NEEDBITS_k k n (mkW s c (pullr c r)))
    else ARun tt (mkW s c r).
Proof.
  intros. cbn [NEEDBITS_k]. unfold abind, gr. cbn [w_r]. destruct (ir_bits r <? n); [|reflexivity].
  rewrite PULLBYTE_eq. destruct (ir_have r =? 0); reflexivity.
Qed.
Lemma NEEDBITS_k_done : forall k n s c r, n <= ir_bits r -> NEEDBITS_k k n (mkW s c r) = ARun tt (mkW s c r).
Proof.
  intros k n s c r H. destruct k; [reflexivity|]. rewrite NEEDBITS_k_S.
  replace (ir_bits r <? n) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma pull_hold_lt : forall ho b bi, 0 <= ho < 2 ^ bi -> 0 <= bi -> 0 <= b < 256 -> 0 <= ho + b * 2 ^ bi < 2 ^ (bi + 8).
Proof.
  intros ho b bi Hho Hbi Hb. rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256.
  pose proof (Z.pow_pos_nonneg 2 bi ltac:(lia) Hbi). nia.
Qed.

Lemma pullr_small : forall c nx hv pt lf ho bi i o rt,
  0 < hv < 2 ^ 32 -> 0 <= bi <= 56 -> 0 <= ho < 2 ^ bi -> 0 <= arr_get (ic_input c) nx < 256 ->
  pullr c (mkIR nx hv pt lf ho bi i o rt)
  = mkIR (nx + 1) (hv - 1) pt lf (ho + arr_get (ic_input c) nx * 2 ^ bi) (bi + 8) i o rt.
Proof.
  intros c nx hv pt lf ho bi i o rt Hhv Hbi Hho Hb. unfold pullr. cbn [ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret].
  f_equal.
  - apply wrap32_id. lia.
  - pose proof (pull_hold_lt ho (arr_get (ic_input c) nx) bi Hho ltac:(lia) Hb) as HL.
    assert (2 ^ (bi + 8) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
    pose proof (Z.pow_pos_nonneg 2 bi ltac:(lia) ltac:(lia)).
    assert (0 <= arr_get (ic_input c) nx * 2 ^ bi) by nia.
    unfold shl64. rewrite Z.shiftl_mul_pow2 by lia.
    rewrite (wrap64_id (arr_get _ _ * _)) by lia. apply wrap64_id. lia.
  - apply wrap32_id. lia.
Qed.


Lemma pullr_small' : forall c r,
  0 < ir_have r < 2 ^ 32 -> 0 <= ir_bits r <= 56 -> 0 <= ir_hold r < 2 ^ ir_bits r -> 0 <= arr_get (ic_input c) (ir_next r) < 256 ->
  pullr c r
  = mkIR (ir_next r + 1) (ir_have r - 1) (ir_put r) (ir_left r) (ir_hold r + arr_get (ic_input c) (ir_next r) * 2 ^ ir_bits r)
         (ir_bits r + 8) (ir_in r) (ir_out r) (ir_ret r).
Proof. intros c r. destruct r. cbn. intros. apply pullr_small; assumption. Qed.

Lemma BITSv_land : forall h n, 0 <= h -> 0 <= n <= 32 -> BITSv h n = Z.land h (Z.ones n).
Proof. intros h n Hh Hn. rewrite Z.land_ones by lia. apply BITSv_mod; lia. Qed.

Lemma land_ones_mod : forall h n, 0 <= n -> Z.land h (Z.ones n) = h mod 2 ^ n.
Proof. intros. apply Z.land_ones. lia. Qed.


Lemma icset_outbuf_facts : forall c a,
  ic_next_in (icset_outbuf c a) = ic_next_in c /\ ic_avail_in (icset_outbuf c a) = ic_avail_in c
  /\ ic_next_out (icset_outbuf c a) = ic_next_out c /\ ic_avail_out (icset_outbuf c a) = ic_avail_out c
  /\ ic_input (icset_outbuf c a) = ic_input c /\ ic_outbuf (icset_outbuf c a) = a
  /\ ic_total_in (icset_outbuf c a) = ic_total_in c /\ ic_total_out (icset_outbuf c a) = ic_total_out c
  /\ ic_adler (icset_outbuf c a) = ic_adler c /\ ic_data_type (icset_outbuf c a) = ic_data_type c
  /\ ic_msg (icset_outbuf c a) = ic_msg c.
Proof. intros c a. destruct c. repeat split; reflexivity. Qed.

Lemma icset_msg_facts : forall c m,
  ic_next_in (icset_msg c m) = ic_next_in c /\ ic_avail_in (icset_msg c m) = ic_avail_in c
  /\ ic_next_out (icset_msg c m) = ic_next_out c /\ ic_avail_out (icset_msg c m) = ic_avail_out c
  /\ ic_input (icset_msg c m) = ic_input c /\ ic_outbuf (icset_msg c m) = ic_outbuf c
  /\ ic_total_in (icset_msg c m) = ic_total_in c /\ ic_total_out (icset_msg c m) = ic_total_out c
  /\ ic_adler (icset_msg c m) = ic_adler c /\ ic_data_type (icset_msg c m) = ic_data_type c
  /\ ic_msg (icset_msg c m) = m.
Proof. intros c m. destruct c. repeat split; reflexivity. Qed.

Lemma wrap8_range : forall x, 0 <= wrap8 x < 256.
Proof. intros x. unfold wrap8. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. Qed.
Lemma le1_wrap8 : forall x, Z_to_le_bytes 1 x = Z_to_le_bytes 1 (wrap8 x).
Proof.
  intros x. unfold wrap8. cbn. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma wrap8_mod : forall x, wrap8 x = x mod 256.
Proof. intros x. unfold wrap8. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma wrap32_pred : forall x, 0 < x < 2 ^ 32 -> wrap32 (x - 1) = x - 1.
Proof. intros x Hx. apply wrap32_id. lia. Qed.


End FXG.
Ltac open_ictx C :=
  pose proof (ic_ret _ C) as Cret; pose proof (ic_sp _ C) as Csp; pose proof (ic_ZP _ C) as CZP; pose proof (ic_S _ C) as CS;
  pose proof (ic_I0 _ C) as CI0; pose proof (ic_P0 _ C) as CP0; pose proof (ic_WB _ C) as CWB; pose proof (ic_flush _ C) as Cflush;
  pose proof (ic_TOT0 _ C) as CTOT0; pose proof (ic_hooks _ C) as Chooks; pose proof (ic_nofast _ C) as Cnofast;
  pose proof (ic_o_Z _ C) as CoZ; pose proof (ic_o_S _ C) as CoS; pose proof (ic_o_I _ C) as CoI; pose proof (ic_o_P _ C) as CoP; pose proof (ic_o_W _ C) as CoW;
  pose proof (ic_d_fZ _ C) as CfZ; pose proof (ic_d_fS _ C) as CfS; pose proof (ic_d_fI _ C) as CfI; pose proof (ic_d_fP _ C) as CfP; pose proof (ic_d_fW _ C) as CfW;
  pose proof (ic_d_ZS _ C) as CZS; pose proof (ic_d_ZI _ C) as CZI; pose proof (ic_d_ZO _ C) as CZO; pose proof (ic_d_ZW _ C) as CZW;
  pose proof (ic_d_SI _ C) as CSI; pose proof (ic_d_SP _ C) as CSP; pose proof (ic_d_SW _ C) as CSW;
  pose proof (ic_d_IP _ C) as CIP; pose proof (ic_d_IW _ C) as CIW; pose proof (ic_d_PW _ C) as CPW;
  pose proof (ic_sp47 _ C) as Csp47; pose proof (ic_Sbelow _ C) as CSb;
  unfold INF_FRAME, INF_SCRATCH, IMG6_TOP in Csp, CfZ, CfS, CfI, CfP, CfW, CSb.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

End FXG.
Ltac open_lmem HM :=
  pose proof (lm_rod _ _ _ HM) as Mrod; pose proof (lm_sc _ _ _ HM) as Msc; pose proof (lm_lens _ _ _ HM) as Mlens;
  pose proof (lm_work _ _ _ HM) as Mwork; pose proof (lm_codes _ _ _ HM) as Mcodes; pose proof (lm_win _ _ _ HM) as Mwin;
  pose proof (lm_in _ _ _ HM) as Minp; pose proof (lm_out _ _ _ HM) as Mout; pose proof (lm_zs _ _ _ HM) as Mzs;
  pose proof (lm_fr _ _ _ HM) as Mfr; pose proof (lm_outc _ _ _ HM) as Moutc;
  pose proof (lm_map_f _ _ _ HM) as Mmap_f; pose proof (lm_map_Z _ _ _ HM) as Mmap_Z; pose proof (lm_map_S _ _ _ HM) as Mmap_S;
  pose proof (lm_map_P _ _ _ HM) as Mmap_P; pose proof (lm_map_W _ _ _ HM) as Mmap_W;
  cbn [w_s w_c w_r] in Mrod, Msc, Mlens, Mwork, Mcodes, Mwin, Minp, Mout, Mzs, Mfr, Moutc, Mmap_f, Mmap_Z, Mmap_S, Mmap_P, Mmap_W;
  unfold INF_FRAME, INF_SCRATCH in Mfr, Moutc, Mmap_f.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

End FXG.
Ltac open_retc HRC := pose proof HRC as Mret; unfold RETC, INF_FRAME in Mret; cbn [w_r] in Mret.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

End FXG.
Ltac open_frame Mfr :=
  let X := fresh in pose proof Mfr as X; unfold iframe6, INF_FRAME in X;
  destruct X as (Fsv & F104 & F96 & F88 & F72 & F56 & F48 & F40 & F32 & F24 & F16 & F8 & Fd0);
  rewrite ?Z.add_0_r in Fd0.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

End FXG.
Ltac open_zs Mzs :=
  let X := fresh in pose proof Mzs as X; unfold izs6 in X;
  destruct X as (Z0 & Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72 & Z80 & Z96).
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

End FXG.
Ltac open_lx HX :=
  let X := fresh in pose proof HX as X; unfold LX in X; cbn [w_s w_c w_r] in X;
  destruct X as (Xwrap & Xwbits & Xlive & Xflags & Xin & Xret & Xmsg & Xhd);
  repeat match goal with
         | Xw0 : ?w = 5 \/ ?w = 1 |- _ =>
             let Rg := fresh "Xwrap_rng" in
             assert (Rg : 1 <= w <= 5) by (clear - Xw0; destruct Xw0 as [Xw1 | Xw1]; rewrite Xw1; clear; lia);
             change (@id Prop (w = 5 \/ w = 1)) in Xw0
         end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

End FXG.
Ltac open_fix HF :=
  let X := fresh in pose proof HF as X; unfold LFIX, INF_FRAME in X;
  destruct X as (G2 & G25 & G10 & G11 & G21 & G31 & G29 & G24 & G19 & G3 & G4).
Ltac open_vars HV :=
  let X := fresh in pose proof HV as X; unfold LVARS in X; cbn [w_r] in X;
  destruct X as (G9 & G18 & G1 & G22 & G23 & G26).
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

End FXG.
Ltac open_pinv HP :=
  let X := fresh in pose proof HP as X; unfold pinv in X;
  destruct X as ((PNI & PNO) & PL & PS & PX & PB & PC);
  cbn [w_s w_c w_r] in PS, PX, PB, PC;
  let Y := fresh in pose proof (proj1 (LRNGq_iff _ _ _ _ _ _ _) PL) as Y;
  destruct Y as (SR & CI & RI & WI & CR).
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

End FXG.
Ltac open_rinv RI :=
  let X := fresh in pose proof RI as X; unfold RINV in X;
  destruct X as (Rnx0 & Rhv0 & Rnh & Rpt0 & Rlf0 & Rpl & Rin & Rout & Routp & Rbits & Rhold);
  lazymatch type of Rhold with 0 <= ?ho < 2 ^ ?bi =>
    assert (Rhold64 : 0 <= ho < 2 ^ 64)
      by (clear - Rhold Rbits; pose proof (Z.pow_lt_mono_r 2 bi 64 ltac:(lia) ltac:(lia)); lia)
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

End FXG.
Ltac open_cinv CI :=
  let X := fresh in pose proof CI as X; unfold CINV in X;
  destruct X as (Cil & Col & Cni0 & Cai0 & Cnai & Cno0 & Cao0 & Cnao & Cinb & Coutb & Cti & Cto & Cad & Cdt).
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.


Definition arm_stops : list Z :=
  [pc6_ret; pc6_leave; pc6_mem; pc6_need_dict;
   0x1f188; 0x1f8c0; 0x1a3d4; 0x27800; 0x1ed04;
   0x1d154; 0x1e5d8; 0x1d5c4; 0x1d710; 0x1df98] ++ arm6_pcs.
Definition arm_rets : list expr := map ELit arm6_pcs.
Definition ilS : cfg := CFG [] [] arm_rets arm_stops [].
Definition ilSx (extra : list Z) (av : list aview) : cfg := CFG [(0%nat, 256); (1%nat, 65536); (2%nat, 2 ^ 32)] [] arm_rets (extra ++ arm_stops) av.

Definition arm_pins_core : list (Z * expr) :=
  [(2, EVar 32%nat); (8, EVar 33%nat); (10, EVar 34%nat); (11, EVar 35%nat); (22, EAdd (EVar 33%nat) (ELit 168));
   (31, ELit (-16180)); (29, ELit 30); (25, ELit 0x12510); (20, ELit 16209);
   (18, EVar 36%nat); (19, EAdd (EVar 37%nat) (EVar 38%nat)); (1, EVar 39%nat); (23, EVar 40%nat); (24, EVar 41%nat)].
Definition arm_pins : list (Z * expr) := arm_pins_core ++ [(27, EAdd (EVar 43%nat) (EVar 44%nat))].
Definition j11_pins : list (Z * expr) := arm_pins_core ++ [(26, EAdd (EVar 43%nat) (EVar 44%nat))].
Definition j1011_pins : list (Z * expr) := arm_pins_core ++ [(27, EAdd (EVar 43%nat) (EVar 44%nat)); (26, EAdd (EVar 43%nat) (EVar 44%nat))].
Definition arm_vb : list (nat * Z) :=
  [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 5); (36%nat, 2 ^ 31); (37%nat, 2 ^ 63); (38%nat, 2 ^ 31);
   (39%nat, 2 ^ 31); (40%nat, 2 ^ 64); (41%nat, 64); (42%nat, 2 ^ 31); (43%nat, 2 ^ 63); (44%nat, 2 ^ 31)].
Definition arm_pvals (v : icv) (r : iregs) : list Z :=
  [cv_sp v - 224; cv_S v; cv_ZP v; cv_flush v; ir_have r; cv_P0 v; ir_put r; ir_left r; ir_hold r; ir_bits r; ir_out r;
   cv_I0 v; ir_next r].
Definition arm_var0 : nat := 45.

End FXG.
Ltac arm_symexP P C fuel dirs rds xpins xvb v r xvals rvals Fam ms R HR Hfr Hms :=
  let pins := eval vm_compute in (P ++ xpins) in
  let vb := eval vm_compute in (arm_vb ++ xvb) in
  let pv := eval cbn [arm_pvals app] in (arm_pvals v r ++ xvals) in
  symex s6_segs C fuel dirs rds pins vb NoRegions pv rvals Fam F0' ms R HR Hfr Hms.
Ltac arm_symex C fuel dirs rds xpins xvb v r xvals rvals Fam ms R HR Hfr Hms :=
  arm_symexP arm_pins C fuel dirs rds xpins xvb v r xvals rvals Fam ms R HR Hfr Hms.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.
End FXG.
Ltac j11_symex C fuel dirs rds xpins xvb v r xvals rvals Fam ms R HR Hfr Hms :=
  arm_symexP j11_pins C fuel dirs rds xpins xvb v r xvals rvals Fam ms R HR Hfr Hms.
Ltac j1011_symex C fuel dirs rds xpins xvb v r xvals rvals Fam ms R HR Hfr Hms :=
  arm_symexP j1011_pins C fuel dirs rds xpins xvb v r xvals rvals Fam ms R HR Hfr Hms.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Definition bmod (f : Z -> Z) (i : Z) : Z := f i mod 256.
Definition hmod (f : Z -> Z) (i : Z) : Z := f i mod 65536.
Definition wmod (f : Z -> Z) (i : Z) : Z := f i mod 4294967296.
Lemma bmod_range : forall f i, 0 <= bmod f i < 256.
Proof. intros. unfold bmod. apply Z.mod_pos_bound. lia. Qed.
Lemma hmod_range : forall f i, 0 <= hmod f i < 65536.
Proof. intros. unfold hmod. apply Z.mod_pos_bound. lia. Qed.
Lemma wmod_range : forall f i, 0 <= wmod f i < 4294967296.
Proof. intros. unfold wmod. apply Z.mod_pos_bound. lia. Qed.
Lemma bmod_get : forall f i, 0 <= f i < 256 -> bmod f i = f i.
Proof. intros. unfold bmod. apply Z.mod_small. lia. Qed.
Lemma hmod_get : forall f i, 0 <= f i < 65536 -> hmod f i = f i.
Proof. intros. unfold hmod. apply Z.mod_small. lia. Qed.
Lemma wmod_get : forall f i, 0 <= f i < 2 ^ 32 -> wmod f i = f i.
Proof. intros. unfold wmod. apply Z.mod_small. lia. Qed.
Lemma cells_bmod : forall M P n f, cells s6_segs M P 1 1 n f -> (forall i, 0 <= i < n -> 0 <= f i < 256) -> cells s6_segs M P 1 1 n (bmod f).
Proof. intros M P n f Hc Hr i Hi. rewrite bmod_get by (apply Hr; lia). exact (Hc i Hi). Qed.
Lemma cells_hmod : forall M P n f, cells s6_segs M P 2 2 n f -> (forall i, 0 <= i < n -> 0 <= f i < 65536) -> cells s6_segs M P 2 2 n (hmod f).
Proof. intros M P n f Hc Hr i Hi. rewrite hmod_get by (apply Hr; lia). exact (Hc i Hi). Qed.
Lemma cells_wmod : forall M P n f, cells s6_segs M P 4 4 n f -> (forall i, 0 <= i < n -> 0 <= f i < 2 ^ 32) -> cells s6_segs M P 4 4 n (wmod f).
Proof. intros M P n f Hc Hr i Hi. rewrite wmod_get by (apply Hr; lia). exact (Hc i Hi). Qed.
Definition famA (c : icall) (s : inflate_state) (k : nat) : Z -> Z :=
  match k with
  | 0%nat => bmod (arr_get (ic_input c))
  | 1%nat => hmod (arr_get (is_lens s))
  | _ => wmod (arr_get (is_codes s))
  end.
End FXG.
Ltac fam_side :=
  intros; cbn [famA];
  first [ apply bmod_range | apply hmod_range | apply wmod_range
        | lazymatch goal with |- 0 <= F0 _ _ < _ => unfold F0; lia end ].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Lemma pins_of_regs : forall v s c r R,
  LFIX v R -> LVARS v (mkW s c r) R ->
  getr R 2 = zw (cv_sp v - 224) /\ getr R 8 = zw (cv_S v) /\ getr R 10 = zw (cv_ZP v) /\ getr R 11 = zw (cv_flush v)
  /\ getr R 22 = zw (cv_S v + 168) /\ getr R 31 = zw (-16180) /\ getr R 29 = zw 30 /\ getr R 25 = zw 0x12510 /\ getr R 20 = zw 16209
  /\ getr R 18 = zw (ir_have r) /\ getr R 19 = zw (cv_P0 v + ir_put r) /\ getr R 1 = zw (ir_left r)
  /\ getr R 23 = zw (ir_hold r) /\ getr R 24 = zw (ir_bits r) /\ getr R 27 = zw (cv_I0 v + ir_next r).
Proof.
  intros v s c r R HF HV. unfold LFIX, LVARS, INF_FRAME, A6_JTAB in *. cbn [w_r] in HV.
  destruct HF as (G2 & G25 & G10 & G11 & G21 & G31 & G29 & G24 & G19 & G3 & G4).
  destruct HV as (G9 & G18 & G1 & G22 & G23 & G26).
  repeat split; assumption.
Qed.

End FXG.
Ltac arm_begin C HM HRC HX HF HV HP :=
  open_ictx C; open_lmem HM; open_retc HRC; open_lx HX; open_fix HF; open_vars HV; open_pinv HP;
  lazymatch goal with
  | RI : RINV _ _ _, CI : CINV _ _ _ |- _ =>
      open_rinv RI; open_cinv CI;
      pose proof (pins_of_regs _ _ _ _ _ HF HV) as (P2 & P25 & P10 & P11 & P21 & P31 & P29 & P24 & P19 & P9 & P18 & P1 & P22 & P23 & P26);
      unfold mapped in *
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.


Lemma arm6_pc_jt : forall m, HEAD <= m < SYNC -> arm6_pc m = jt6_entry (m - HEAD).
Proof. intros m Hm. reflexivity. Qed.

Lemma jt6_off_eq : forall k, jt6_off k = jt6_entry k - A6_JTAB.
Proof. reflexivity. Qed.

Definition JT (m : Z) : Z := jt6_off (m - HEAD).

Lemma jt6_read_lit : forall mem (a : Z) k e,
  rod6_clear mem -> 0 <= k < 31 -> a = A6_JTAB + 4 * k -> e = jt6_off k ->
  exists bs, rdn s6_segs mem (zw a) 4 = Some bs /\ bytes_le_to_Z bs = e.
Proof. intros mem a k e HM Hk -> ->. exact (jt6_read mem k HM Hk). Qed.

End FXG.
Ltac jt_read_close Hrod :=
  lazymatch goal with
  | |- exists bs, rdn s6_segs ?m (zw ?a) 4 = Some bs /\ bytes_le_to_Z bs = ?e =>
      let k := eval vm_compute in ((a - 0x12510) / 4) in
      apply (jt6_read_lit m a k e Hrod); [lia | reflexivity | vm_compute; reflexivity]
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.


Lemma MFRAME_refl : forall v p M, MFRAME v p p M M.
Proof. intros v p M. split; [lia|]. split; [intros x Hx; exact Hx | intros; reflexivity]. Qed.

Lemma MFRAME_trans : forall v p0 p1 p2 M M' M'',
  MFRAME v p0 p1 M M' -> MFRAME v p1 p2 M' M'' -> MFRAME v p0 p2 M M''.
Proof.
  intros v p0 p1 p2 M M' M'' (A1 & A2 & A3) (B1 & B2 & B3). split; [lia|]. split; [intros x Hx; apply B2, A2, Hx|].
  intros x N1 N2 N3 N4. rewrite B3; [apply A3; try assumption; lia | assumption | assumption | assumption | lia].
Qed.

Lemma MFRAME_store : forall v p0 p1 p1' M M' (a : Z) bs,
  MFRAME v p0 p1 M M' -> p1 <= p1' -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  (  (cv_sp v - INF_FRAME - INF_SCRATCH <= a /\ a + Z.of_nat (length bs) <= cv_sp v)
  \/ (cv_S v <= a /\ a + Z.of_nat (length bs) <= cv_S v + 7176)
  \/ (cv_ZP v <= a /\ a + Z.of_nat (length bs) <= cv_ZP v + 112)
  \/ (cv_P0 v + p0 <= a /\ a + Z.of_nat (length bs) <= cv_P0 v + p1')) ->
  MFRAME v p0 p1' M (wbytes M' (zw a) bs).
Proof.
  intros v p0 p1 p1' M M' a bs (Hp & Hg & HE) Hp1 Ha0 Ha1 Hz.
  split; [lia|]. split; [intros x Hx; apply wbytes_grows; exact (Hg x Hx)|].
  intros x N1 N2 N3 N4. rewrite wbytes_inside; [| exact Ha0 | exact Ha1 |].
  - apply HE; [exact N1 | exact N2 | exact N3 | lia].
  - pose proof (u64_range x). lia.
Qed.

Lemma MFRAME_mono : forall v p0 p1 p1' M M', MFRAME v p0 p1 M M' -> p1 <= p1' -> MFRAME v p0 p1' M M'.
Proof.
  intros v p0 p1 p1' M M' (Hp & Hg & HE) H. split; [lia|]. split; [exact Hg|].
  intros x N1 N2 N3 N4. apply HE; try assumption. lia.
Qed.


Section Stores.
  Variable v : icv.
  Hypothesis C : ictx v.

  Lemma izs6_outbuf : forall M c a, izs6 v M c -> izs6 v M (icset_outbuf c a).
  Proof. intros M c a H. destruct c. exact H. Qed.

  Lemma izs6_other : forall M c (b : Z) bs,
    izs6 v M c -> 0 <= b -> b + Z.of_nat (length bs) <= 2 ^ 64 ->
    (cv_ZP v + 112 <= b \/ b + Z.of_nat (length bs) <= cv_ZP v) ->
    izs6 v (wbytes M (zw b) bs) c.
  Proof.
    intros M c b bs H Hb0 Hb1 Hd. pose proof (ic_ZP _ C) as CZP. unfold izs6 in *.
    destruct H as (Z0 & Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72 & Z80 & Z96).
    repeat match goal with |- _ /\ _ => split end;
      (eapply cell_write_other; [eassumption | lia | cbn; lia | lia | lia | cbn; lia]).
  Qed.

  Definition iframe6_ok (a k : Z) : Prop :=
    a + k <= cv_sp v - INF_FRAME \/ cv_sp v <= a \/
    (cv_sp v - INF_FRAME + 64 <= a /\ a + k <= cv_sp v - INF_FRAME + 72) \/
    (cv_sp v - INF_FRAME + 80 <= a /\ a + k <= cv_sp v - INF_FRAME + 88) \/
    (cv_sp v - INF_FRAME + 112 <= a /\ a + k <= cv_sp v - INF_FRAME + 120).

  Lemma iframe6_other : forall M (b : Z) bs,
    iframe6 v M -> 0 <= b -> b + Z.of_nat (length bs) <= 2 ^ 64 -> iframe6_ok b (Z.of_nat (length bs)) ->
    iframe6 v (wbytes M (zw b) bs).
  Proof.
    intros M b bs H Hb0 Hb1 Hok. pose proof (ic_sp _ C) as Csp. unfold iframe6, iframe6_ok, INF_FRAME, INF_SCRATCH, IMG6_TOP in *.
    destruct H as (Fsv & F104 & F96 & F88 & F72 & F56 & F48 & F40 & F32 & F24 & F16 & F8 & Fd0).
    split.
    { intros rg o Hro. pose proof (Fsv rg o Hro) as X. cbn in Hro.
      assert (Ho : 120 <= o /\ o + 8 <= 224)
        by (clear -Hro; destruct Hro as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]]; injection E as <- <-; lia). clear Hro.
      apply (cell_write_other _ _ _ _ _ _ _ X); [lia | cbn; lia | lia | lia | cbn; lia]. }
    repeat match goal with |- _ /\ _ => split end;
      (eapply cell_write_other; [eassumption | lia | cbn; lia | lia | lia | cbn; lia]).
  Qed.

  Lemma LMEM_store_scalar : forall s c r s' M off bs,
    LMEM v (mkW s c r) M ->
    0 <= off -> (off + Z.of_nat (length bs) <= 168 \/ 7160 <= off /\ off + Z.of_nat (length bs) <= 7176) -> 0 <= ir_put r <= cv_NO v ->  (* 1.4 layout *)
    is6_scalars (wbytes M (zw (cv_S v + off)) bs) (cv_S v) (ISP (cv_ZP v) (cv_WB v)) s' ->
    is_lens s' = is_lens s -> is_work s' = is_work s -> is_codes s' = is_codes s -> is_window s' = is_window s ->
    LMEM v (mkW s' c r) (wbytes M (zw (cv_S v + off)) bs).
  Proof.
    intros s c r s' M off bs HM Ho0 Ho1 Hput Hsc' E1 E2 E3 E4.
    open_ictx C. open_lmem HM.
    constructor; cbn [w_s w_c w_r]; rewrite ?E1, ?E2, ?E3, ?E4.
    - intros x Hx. rewrite wbytes_inside; [exact (Mrod x Hx) | lia | lia |]. unfold offimg, IMG6_TOP in CoS. unfold ROD6_LO, ROD6_HI in Hx. clear - Hx CoS Ho0 Ho1 CS. lia.
    - exact Hsc'.
    - apply (cells_write_other _ _ _ _ _ _ _ _ _ Mlens); cbn; lia.
    - apply (cells_write_other _ _ _ _ _ _ _ _ _ Mwork); cbn; lia.
    - apply (cells_write_other _ _ _ _ _ _ _ _ _ Mcodes); cbn; lia.
    - intros Hwn. apply (cells_write_other _ _ _ _ _ _ _ _ _ (Mwin Hwn)); [cbn; lia | lia | lia | lia | lia |]. unfold sep in CSW. lia.
    - destruct (Z.eq_dec (cv_NI v) 0) as [E0|E0]; [rewrite E0; apply cells_nil|].
      apply (cells_write_other _ _ _ _ _ _ _ _ _ Minp); [cbn; lia | lia | lia | lia | lia |]. specialize (CSI ltac:(lia)). unfold sep in CSI. lia.
    - destruct (Z.eq_dec (ir_put r) 0) as [E0|E0]; [rewrite E0; apply cells_nil|].
      apply (cells_write_other _ _ _ _ _ _ _ _ _ Mout); [cbn; lia | lia | lia | lia | lia |]. specialize (CSP ltac:(lia)). unfold sep in CSP. lia.
    - apply izs6_other; [exact Mzs | lia | lia | unfold sep in CZS; lia].
    - apply iframe6_other; [exact Mfr | lia | lia | unfold iframe6_ok, INF_FRAME; unfold sep in CfS; lia].
    - pose proof (ic_sp _ C) as Csp_o; unfold INF_FRAME, INF_SCRATCH, IMG6_TOP in Csp_o, Moutc |- *; apply (cell_write_other _ _ _ _ _ _ _ Moutc); [lia | cbn; lia | lia | lia | unfold sep in CfS; lia].
    - apply mapped_wbytes. exact Mmap_f.
    - apply mapped_wbytes. exact Mmap_Z.
    - apply mapped_wbytes. exact Mmap_S.
    - apply mapped_wbytes. exact Mmap_P.
    - intros Hwn. apply mapped_wbytes. exact (Mmap_W Hwn).
  Qed.

  Lemma LMEM_store_out : forall s c r r' M val b,
    LMEM v (mkW s c r) M ->
    0 <= ir_put r < cv_NO v -> arr_len (ic_outbuf c) = cv_NO v ->
    ir_put r' = ir_put r + 1 -> Z_to_le_bytes 1 val = Z_to_le_bytes 1 b ->
    ir_out r' = ir_out r ->
    LMEM v (mkW s (icset_outbuf c (arr_set (ic_outbuf c) (ir_put r) b)) r') (wbytes M (zw (cv_P0 v + ir_put r)) (Z_to_le_bytes 1 val)).
  Proof.
    intros s c r r' M val b HM Hput Hlen Hput' Hvb Hout'.
    open_ictx C. open_lmem HM.
    pose proof (icset_outbuf_facts c (arr_set (ic_outbuf c) (ir_put r) b)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & _).
    assert (HNO : 0 < cv_NO v) by lia.
    specialize (CoP HNO). specialize (CfP HNO). specialize (CSP HNO). specialize (CPW HNO).
    constructor; cbn [w_s w_c w_r]; rewrite ?F1, ?F2, ?F3, ?F4, ?F5, ?F6, ?F7, ?Hput', ?Hvb.
    - intros x Hx. rewrite wbytes_inside; [exact (Mrod x Hx) | lia | cbn; lia |]. unfold offimg, IMG6_TOP in CoP. unfold ROD6_LO, ROD6_HI in Hx. clear - Hx CoP Hput CP0. cbn. lia.
    - unfold is6_scalars in *. apply (fields_write_other s6_segs _ _ is6_layout _ is6_SIZE _ _ Msc is6_layout_within); [lia | unfold is6_SIZE; lia | lia | cbn; lia |].
      unfold sep in CSP. unfold is6_SIZE. clear - CSP Hput CP0 CS. cbn. lia.
    - apply (cells_write_other _ _ _ _ _ _ _ _ _ Mlens); [cbn; lia | lia | lia | lia | cbn; lia | unfold sep in CSP; cbn; lia].
    - apply (cells_write_other _ _ _ _ _ _ _ _ _ Mwork); [cbn; lia | lia | lia | lia | cbn; lia | unfold sep in CSP; cbn; lia].
    - apply (cells_write_other _ _ _ _ _ _ _ _ _ Mcodes); [cbn; lia | lia | lia | lia | cbn; lia | unfold sep in CSP; cbn; lia].
    - intros Hwn. apply (cells_write_other _ _ _ _ _ _ _ _ _ (Mwin Hwn)); [cbn; lia | lia | lia | lia | cbn; lia |]. unfold sep in CPW. cbn. lia.
    - destruct (Z.eq_dec (cv_NI v) 0) as [E0|E0]; [rewrite E0; apply cells_nil|].
      apply (cells_write_other _ _ _ _ _ _ _ _ _ Minp); [cbn; lia | lia | lia | lia | cbn; lia |]. unfold sep in CIP. cbn. lia.
    - apply cells_snoc; [| lia |].
      + intros i Hi. rewrite arr_get_set_other by lia.
        apply (cell_write_other _ _ _ _ _ _ _ (Mout i Hi)); [lia | cbn; lia | lia | cbn; lia | cbn; lia].
      + rewrite arr_get_set_same by lia. rewrite Z.mul_1_l. apply cell_write_same; [lia | cbn; lia].
    - apply izs6_outbuf. apply izs6_other; [exact Mzs | lia | cbn; lia | unfold sep in CZO; cbn; lia].
    - apply iframe6_other; [exact Mfr | lia | cbn; lia | unfold iframe6_ok, INF_FRAME; unfold sep in CfP; cbn; lia].
    - rewrite Hout'. pose proof (ic_sp _ C) as Csp_o; unfold INF_FRAME, INF_SCRATCH, IMG6_TOP in Csp_o, Moutc |- *; apply (cell_write_other _ _ _ _ _ _ _ Moutc); [lia | cbn; lia | lia | cbn; lia | unfold sep in CfP; cbn; lia].
    - apply mapped_wbytes. exact Mmap_f.
    - apply mapped_wbytes. exact Mmap_Z.
    - apply mapped_wbytes. exact Mmap_S.
    - apply mapped_wbytes. exact Mmap_P.
    - intros Hwn. apply mapped_wbytes. exact (Mmap_W Hwn).
  Qed.

  Lemma LMEM_store_msg : forall s c r M m,
    LMEM v (mkW s c r) M -> 0 <= ir_put r <= cv_NO v ->
    LMEM v (mkW s (icset_msg c m) r) (wbytes M (zw (cv_ZP v + 48)) (Z_to_le_bytes 8 (msg6_addr m))).
  Proof.
    intros s c r M m HM Hput.
    open_ictx C. open_lmem HM.
    pose proof (icset_msg_facts c m) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
    constructor; cbn [w_s w_c w_r]; rewrite ?F1, ?F2, ?F3, ?F4, ?F5, ?F6.
    - intros x Hx. rewrite wbytes_inside; [exact (Mrod x Hx) | lia | cbn; lia |]. unfold offimg, IMG6_TOP in CoZ. unfold ROD6_LO, ROD6_HI in Hx. clear - Hx CoZ CZP. cbn. lia.
    - unfold is6_scalars in *. apply (fields_write_other s6_segs _ _ is6_layout _ is6_SIZE _ _ Msc is6_layout_within); [lia | unfold is6_SIZE; lia | lia | cbn; lia |].
      unfold sep in CZS. unfold is6_SIZE. clear - CZS CZP CS. cbn. lia.
    - apply (cells_write_other _ _ _ _ _ _ _ _ _ Mlens); [cbn; lia | lia | lia | lia | cbn; lia | unfold sep in CZS; cbn; lia].
    - apply (cells_write_other _ _ _ _ _ _ _ _ _ Mwork); [cbn; lia | lia | lia | lia | cbn; lia | unfold sep in CZS; cbn; lia].
    - apply (cells_write_other _ _ _ _ _ _ _ _ _ Mcodes); [cbn; lia | lia | lia | lia | cbn; lia | unfold sep in CZS; cbn; lia].
    - intros Hwn. apply (cells_write_other _ _ _ _ _ _ _ _ _ (Mwin Hwn)); [cbn; lia | lia | lia | lia | cbn; lia |]. unfold sep in CZW. cbn. lia.
    - destruct (Z.eq_dec (cv_NI v) 0) as [E0|E0]; [rewrite E0; apply cells_nil|].
      apply (cells_write_other _ _ _ _ _ _ _ _ _ Minp); [cbn; lia | lia | lia | lia | cbn; lia |]. unfold sep in CZI. cbn. lia.
    - destruct (Z.eq_dec (ir_put r) 0) as [E0|E0]; [rewrite E0; apply cells_nil|].
      apply (cells_write_other _ _ _ _ _ _ _ _ _ Mout); [cbn; lia | lia | lia | lia | cbn; lia |]. unfold sep in CZO. cbn. lia.
    - unfold izs6 in *. rewrite F7, F8, F9, ?F10, F11.
      destruct Mzs as (Z0 & Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72 & Z80 & Z96).
      repeat match goal with |- _ /\ _ => split end;
        try (eapply cell_write_other; [eassumption | lia | cbn; lia | lia | cbn; lia | cbn; lia]).
      apply cell_write_same; [lia | cbn; lia].
    - apply iframe6_other; [exact Mfr | lia | cbn; lia | unfold iframe6_ok, INF_FRAME; unfold sep in CfZ; cbn; lia].
    - pose proof (ic_sp _ C) as Csp_o; unfold INF_FRAME, INF_SCRATCH, IMG6_TOP in Csp_o, Moutc |- *; apply (cell_write_other _ _ _ _ _ _ _ Moutc); [lia | cbn; lia | lia | cbn; lia | unfold sep in CfZ; cbn; lia].
    - apply mapped_wbytes. exact Mmap_f.
    - apply mapped_wbytes. exact Mmap_Z.
    - apply mapped_wbytes. exact Mmap_S.
    - apply mapped_wbytes. exact Mmap_P.
    - intros Hwn. apply mapped_wbytes. exact (Mmap_W Hwn).
  Qed.

  Lemma LMEM_store_fscratch : forall s c r M (o : Z) bs,
    LMEM v (mkW s c r) M -> 0 <= ir_put r <= cv_NO v ->
    ((o = 64 \/ o = 112) /\ length bs = 8%nat) ->
    LMEM v (mkW s c r) (wbytes M (zw (cv_sp v - 224 + o)) bs).
  Proof.
    intros s c r M o bs HM Hput [Ho Hl].
    open_ictx C. open_lmem HM.
    assert (Hl' : Z.of_nat (length bs) = 8) by (rewrite Hl; reflexivity).
    constructor; cbn [w_s w_c w_r].
    - intros x Hx. rewrite wbytes_inside; [exact (Mrod x Hx) | lia | lia |]. unfold ROD6_LO, ROD6_HI in Hx. clear - Hx Csp Ho Hl'. lia.
    - unfold is6_scalars in *. apply (fields_write_other s6_segs _ _ is6_layout _ is6_SIZE _ _ Msc is6_layout_within); [lia | unfold is6_SIZE; lia | lia | lia |].
      unfold sep in CfS. unfold is6_SIZE. clear - CfS Csp CS Ho Hl'. lia.
    - apply (cells_write_other _ _ _ _ _ _ _ _ _ Mlens); [cbn; lia | lia | lia | lia | lia | unfold sep in CfS; lia].
    - apply (cells_write_other _ _ _ _ _ _ _ _ _ Mwork); [cbn; lia | lia | lia | lia | lia | unfold sep in CfS; lia].
    - apply (cells_write_other _ _ _ _ _ _ _ _ _ Mcodes); [cbn; lia | lia | lia | lia | lia | unfold sep in CfS; lia].
    - intros Hwn. apply (cells_write_other _ _ _ _ _ _ _ _ _ (Mwin Hwn)); [cbn; lia | lia | lia | lia | lia |]. unfold sep in CfW. lia.
    - destruct (Z.eq_dec (cv_NI v) 0) as [E0|E0]; [rewrite E0; apply cells_nil|].
      apply (cells_write_other _ _ _ _ _ _ _ _ _ Minp); [cbn; lia | lia | lia | lia | lia |]. specialize (CfI ltac:(lia)). unfold sep in CfI. lia.
    - destruct (Z.eq_dec (ir_put r) 0) as [E0|E0]; [rewrite E0; apply cells_nil|].
      apply (cells_write_other _ _ _ _ _ _ _ _ _ Mout); [cbn; lia | lia | lia | lia | lia |]. specialize (CfP ltac:(lia)). unfold sep in CfP. lia.
    - apply izs6_other; [exact Mzs | lia | lia | unfold sep in CfZ; lia].
    - apply iframe6_other; [exact Mfr | lia | lia | unfold iframe6_ok, INF_FRAME; lia].
    - pose proof (ic_sp _ C) as Csp_o; unfold INF_FRAME, INF_SCRATCH, IMG6_TOP in Csp_o, Moutc |- *; apply (cell_write_other _ _ _ _ _ _ _ Moutc); [lia | cbn; lia | lia | lia | lia].
    - apply mapped_wbytes. exact Mmap_f.
    - apply mapped_wbytes. exact Mmap_Z.
    - apply mapped_wbytes. exact Mmap_S.
    - apply mapped_wbytes. exact Mmap_P.
    - intros Hwn. apply mapped_wbytes. exact (Mmap_W Hwn).
  Qed.

  Lemma LMEM_store_outc : forall s c r r' M,
    LMEM v (mkW s c r) M -> 0 <= ir_put r <= cv_NO v -> ir_put r' = ir_put r -> 0 <= ir_out r' < 2 ^ 64 ->
    LMEM v (mkW s c r') (wbytes M (zw (cv_sp v - 224 + 80)) (Z_to_le_bytes 8 (ir_out r'))).
  Proof.
    intros s c r r' M HM Hput Hput' Hout'.
    open_ictx C. open_lmem HM.
    assert (Hl' : Z.of_nat (length (Z_to_le_bytes 8 (ir_out r'))) = 8) by (rewrite length_Z_to_le_bytes; reflexivity).
    constructor; cbn [w_s w_c w_r]; rewrite ?Hput'.
    - intros x Hx. rewrite wbytes_inside; [exact (Mrod x Hx) | lia | lia |]. unfold ROD6_LO, ROD6_HI in Hx. clear - Hx Csp Hl'. lia.
    - unfold is6_scalars in *. apply (fields_write_other s6_segs _ _ is6_layout _ is6_SIZE _ _ Msc is6_layout_within); [lia | unfold is6_SIZE; lia | lia | lia |].
      unfold sep in CfS. unfold is6_SIZE. clear - CfS Csp CS Hl'. lia.
    - apply (cells_write_other _ _ _ _ _ _ _ _ _ Mlens); [cbn; lia | lia | lia | lia | lia | unfold sep in CfS; lia].
    - apply (cells_write_other _ _ _ _ _ _ _ _ _ Mwork); [cbn; lia | lia | lia | lia | lia | unfold sep in CfS; lia].
    - apply (cells_write_other _ _ _ _ _ _ _ _ _ Mcodes); [cbn; lia | lia | lia | lia | lia | unfold sep in CfS; lia].
    - intros Hwn. apply (cells_write_other _ _ _ _ _ _ _ _ _ (Mwin Hwn)); [cbn; lia | lia | lia | lia | lia |]. unfold sep in CfW. lia.
    - destruct (Z.eq_dec (cv_NI v) 0) as [E0|E0]; [rewrite E0; apply cells_nil|].
      apply (cells_write_other _ _ _ _ _ _ _ _ _ Minp); [cbn; lia | lia | lia | lia | lia |]. specialize (CfI ltac:(lia)). unfold sep in CfI. lia.
    - destruct (Z.eq_dec (ir_put r) 0) as [E0|E0]; [rewrite E0; apply cells_nil|].
      apply (cells_write_other _ _ _ _ _ _ _ _ _ Mout); [cbn; lia | lia | lia | lia | lia |]. specialize (CfP ltac:(lia)). unfold sep in CfP. lia.
    - apply izs6_other; [exact Mzs | lia | lia | unfold sep in CfZ; lia].
    - apply iframe6_other; [exact Mfr | lia | lia | unfold iframe6_ok, INF_FRAME; lia].
    - unfold INF_FRAME. apply cell_write_same; [lia | cbn; lia].
    - apply mapped_wbytes. exact Mmap_f.
    - apply mapped_wbytes. exact Mmap_Z.
    - apply mapped_wbytes. exact Mmap_S.
    - apply mapped_wbytes. exact Mmap_P.
    - intros Hwn. apply mapped_wbytes. exact (Mmap_W Hwn).
  Qed.

  Lemma RETC_store : forall s c r M,
    RETC v (mkW s c r) (wbytes M (zw (cv_sp v - 224 + 64)) (Z_to_le_bytes 8 (ir_ret r))).
  Proof.
    intros s c r M. pose proof (ic_sp _ C) as Csp. unfold RETC, INF_FRAME, INF_SCRATCH, IMG6_TOP in *. cbn [w_r].
    apply cell_write_same; [lia | cbn; lia].
  Qed.

  Lemma RETC_other : forall w M (b : Z) bs,
    RETC v w M -> 0 <= b -> b + Z.of_nat (length bs) <= 2 ^ 64 ->
    (cv_sp v - 224 + 72 <= b \/ b + Z.of_nat (length bs) <= cv_sp v - 224 + 64) ->
    RETC v w (wbytes M (zw b) bs).
  Proof.
    intros w M b bs H Hb0 Hb1 Hd. pose proof (ic_sp _ C) as Csp. unfold RETC, INF_FRAME, INF_SCRATCH, IMG6_TOP in *.
    apply (cell_write_other _ _ _ _ _ _ _ H); [lia | cbn; lia | lia | lia | cbn; lia].
  Qed.

  Lemma RETC_regs : forall w w' M, RETC v w M -> ir_ret (w_r w') = ir_ret (w_r w) -> RETC v w' M.
  Proof. intros w w' M H E. unfold RETC in *. rewrite E. exact H. Qed.

  Lemma LMEM_regs : forall s c r c' r' M,
    LMEM v (mkW s c r) M -> ir_put r' = ir_put r -> ir_out r' = ir_out r ->
    ic_input c' = ic_input c -> ic_outbuf c' = ic_outbuf c ->
    ic_next_in c' = ic_next_in c -> ic_avail_in c' = ic_avail_in c -> ic_next_out c' = ic_next_out c -> ic_avail_out c' = ic_avail_out c ->
    ic_total_in c' = ic_total_in c -> ic_total_out c' = ic_total_out c -> ic_msg c' = ic_msg c -> ic_adler c' = ic_adler c ->
    LMEM v (mkW s c' r') M.
  Proof.
    intros s c r c' r' M HM E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12. open_lmem HM.
    constructor; cbn [w_s w_c w_r]; rewrite ?E1, ?E2, ?E3, ?E4; try assumption.
    unfold izs6 in *. rewrite E5, E6, E7, E8, E9, E10, E11, E12. exact Mzs.
  Qed.
End Stores.


Definition fix_regs : list reg := [2; 8; 10; 11; 22; 31; 29; 25; 20; 3; 4]%bv.
Definition keeps_regs (K L : list reg) : bool := forallb (fun x => negb (reg_in x L)) K.

Lemma keeps_regs_in : forall K L x, keeps_regs K L = true -> In x K -> reg_in x L = false.
Proof.
  intros K L x H Hin. unfold keeps_regs in H. rewrite forallb_forall in H.
  specialize (H x Hin). destruct (reg_in x L); [discriminate H | reflexivity].
Qed.

Lemma LFIX_frame : forall v R R' L,
  LFIX v R -> (forall rg, reg_in rg L = false -> getr R' rg = getr R rg) -> keeps_regs fix_regs L = true -> LFIX v R'.
Proof.
  intros v R R' L HF Hfr HL. unfold LFIX in *.
  destruct HF as (G2 & G25 & G10 & G11 & G21 & G31 & G29 & G24 & G19 & G3 & G4).
  assert (K : forall x, In x fix_regs -> getr R' x = getr R x)
    by (intros x Hx; apply Hfr; exact (keeps_regs_in _ _ _ HL Hx)).
  rewrite !K by (cbn; tauto). repeat split; assumption.
Qed.

Lemma lazy34 : forall (R0 R R' : bvmap 5 word) L,
  (forall rg, reg_in rg L = false -> getr R' rg = getr R rg) -> keeps_regs [3; 4]%bv L = true ->
  getr R 3 = getr R0 3 -> getr R 4 = getr R0 4 -> getr R' 3 = getr R0 3 /\ getr R' 4 = getr R0 4.
Proof.
  intros R0 R R' L Hfr HL G3 G4.
  split.
  - rewrite (Hfr 3%bv (keeps_regs_in _ _ 3%bv HL ltac:(cbn; tauto))). exact G3.
  - rewrite (Hfr 4%bv (keeps_regs_in _ _ 4%bv HL ltac:(cbn; tauto))). exact G4.
Qed.


Lemma same_blocks_refl : forall s, same_blocks s s.
Proof. intros s. repeat split; reflexivity. Qed.
Lemma same_blocks_trans : forall s1 s2 s3, same_blocks s1 s2 -> same_blocks s2 s3 -> same_blocks s1 s3.
Proof. intros s1 s2 s3 (A1 & A2 & A3) (B1 & B2 & B3). unfold same_blocks. rewrite B1, B2, B3. repeat split; assumption. Qed.


Lemma mod64_lo : forall x, 0 <= x mod 2 ^ 64.
Proof. intros x. apply Z.mod_pos_bound. lia. Qed.
Lemma mod64_hi : forall x, x mod 2 ^ 64 < 18446744073709551616.
Proof. intros x. apply Z.mod_pos_bound. lia. Qed.
Lemma mod64_hi' : forall x, x mod 2 ^ 64 < 2 ^ 64.
Proof. intros x. apply Z.mod_pos_bound. lia. Qed.

Lemma off_lit : forall b n a c x y, offimg b n -> 0x10000 <= c -> a <= IMG6_TOP -> b <= x -> y <= b + n -> (a <= x \/ y <= c).
Proof. intros b n a c x y Ho H1 H2 H3 H4. unfold offimg in Ho. lia. Qed.
Lemma off_lit' : forall (k : Z) b n a c x y, (0 < k -> offimg b n) -> 0 < k -> 0x10000 <= c -> a <= IMG6_TOP -> b <= x -> y <= b + n -> (a <= x \/ y <= c).
Proof. intros k b n a c x y Ho Hk H1 H2 H3 H4. specialize (Ho Hk). unfold offimg in Ho. lia. Qed.

End FXG.
Ltac off_side :=
  lazymatch goal with
  | |- ?a <= ?x \/ ?y <= ?c =>
      match goal with
      | Ho : offimg ?b ?n |- _ => apply (off_lit b n a c x y Ho); [cbv [IMG6_TOP]; lia | cbv [IMG6_TOP]; lia | lia | lia]
      | Ho : 0 < ?k -> offimg ?b ?n |- _ => apply (off_lit' k b n a c x y Ho); [lia | cbv [IMG6_TOP]; lia | cbv [IMG6_TOP]; lia | lia | lia]
      end
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

End FXG.
Ltac mod_side :=
  match goal with
  | |- 0 <= _ mod ?m => apply (proj1 (Z.mod_pos_bound _ m ltac:(lia)))
  | |- _ mod ?m < _ => eapply Z.lt_le_trans; [apply (proj2 (Z.mod_pos_bound _ m ltac:(lia))) | lia]
  | |- 0 <= _ mod ?m < _ => split; [apply (proj1 (Z.mod_pos_bound _ m ltac:(lia))) | eapply Z.lt_le_trans; [apply (proj2 (Z.mod_pos_bound _ m ltac:(lia))) | lia]]
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

End FXG.
Ltac sep_side :=
  lazymatch goal with
  | |- _ <= _ \/ _ <= _ =>
      match goal with
      | H : sep _ _ _ _ |- _ =>
          solve [ generalize H;
                  repeat match goal with
                         | K : 0 < ?b /\ _ |- _ => generalize K; clear K
                         | K : 0 <= ?b /\ _ |- _ => generalize K; clear K
                         | K : _ + _ + _ <= cv_sp _ /\ _ |- _ => generalize K; clear K
                         | K : 0 <= ?x |- _ => generalize K; clear K
                         | K : ?x + ?y = _ |- _ => generalize K; clear K
                         | K : ?x <= ?y <= _ |- _ => generalize K; clear K
                         end;
                  clear; intros; unfold sep, INF_FRAME, INF_SCRATCH, IMG6_TOP in *;
                  cbn [length Z_to_le_bytes Z.of_nat Pos.of_succ_nat Pos.succ] in *; lia ]
      | H : 0 < ?k -> sep _ _ _ _ |- _ =>
          solve [ let H' := fresh in assert (H' := H ltac:(lia)); generalize H';
                  repeat match goal with
                         | K : 0 < ?b /\ _ |- _ => generalize K; clear K
                         | K : 0 <= ?b /\ _ |- _ => generalize K; clear K
                         | K : _ + _ + _ <= cv_sp _ /\ _ |- _ => generalize K; clear K
                         | K : 0 <= ?x |- _ => generalize K; clear K
                         | K : ?x + ?y = _ |- _ => generalize K; clear K
                         | K : ?x <= ?y <= _ |- _ => generalize K; clear K
                         end;
                  clear; intros; unfold sep, INF_FRAME, INF_SCRATCH, IMG6_TOP in *;
                  cbn [length Z_to_le_bytes Z.of_nat Pos.of_succ_nat Pos.succ] in *; lia ]
      end
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

End FXG.
Ltac arm_side :=
  lazymatch goal with
  | |- exists _, _ =>
      first [ assumption
            | symex_read_auto
            | match goal with H : rod6_clear ?m |- exists bs, rdn s6_segs ?m' (zw _) 4 = Some bs /\ _ => constr_eq m m'; jt_read_close H end ]
  | |- _ =>
  first [ assumption
        | reflexivity
        | lia
        | apply mod64_lo | apply mod64_hi | apply mod64_hi'
        | mod_side
        | fam_side
        | symex_auto; fail
        | off_side
        | sep_side
        | match goal with H : rod6_clear ?m |- exists bs, rdn s6_segs ?m' (zw _) 4 = Some bs /\ _ => constr_eq m m'; jt_read_close H end
        | rewrite ?szwrap32_small by lia; rewrite ?Z.mod_small by lia; lia ]
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.


End FXG.
Ltac by_run Hms :=
  try (lazymatch goal with |- msteps _ (mkst _ (Z_to_bv 64 ?p0) _ _) _ => let q0 := eval vm_compute in p0 in change p0 with q0 end);
  try (lazymatch goal with |- msteps _ _ (mkst _ (Z_to_bv 64 ?p1) _ _) => let q1 := eval vm_compute in p1 in change p1 with q1 end);
  change (Z_to_bv 64) with zw; symex_pc_lit; change (Z_to_bv 64) with zw in Hms;
  repeat match type of Hms with
         | context [mkst _ (zw ?z) _ _] =>
             lazymatch z with
             | Zpos _ => fail
             | Z0 => fail
             | _ => let q := eval vm_compute in z in change z with q in Hms
             end
         end;
  symex_pc_lit_in Hms; exact Hms.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.


Lemma Z_to_le_bytes_add : forall n k z, Z_to_le_bytes (n + k) z = Z_to_le_bytes n z ++ Z_to_le_bytes k (Z.shiftr z (8 * Z.of_nat n)).
Proof.
  induction n as [|n IH]; intros k z.
  - cbn [Nat.add app Z.of_nat Z.mul]. rewrite Z.shiftr_0_r. reflexivity.
  - cbn [Nat.add Z_to_le_bytes app]. f_equal. rewrite IH. f_equal. f_equal.
    rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.
Lemma wbytes_sd_split : forall m a v,
  wbytes m (zw a) (Z_to_le_bytes 8 v) = wbytes (wbytes m (zw a) (Z_to_le_bytes 4 v)) (zw (a + 4)) (Z_to_le_bytes 4 (Z.shiftr v 32)).
Proof.
  intros m a v. change 8%nat with (4 + 4)%nat. rewrite Z_to_le_bytes_add, (AllocSim.wbytes_app m (zw a)).
  rewrite length_Z_to_le_bytes. change 4%nat with (Z.to_nat 4) at 3. rewrite <- (zw_add_nat a 4). reflexivity.
Qed.

Lemma le4_eqm : forall a b, a mod 2 ^ 32 = b mod 2 ^ 32 -> Z_to_le_bytes 4 a = Z_to_le_bytes 4 b.
Proof.
  intros a b H. rewrite <- (SymExec.Z_to_le_bytes_mod 4 a), <- (SymExec.Z_to_le_bytes_mod 4 b). change (8 * Z.of_nat 4) with 32. rewrite H. reflexivity.
Qed.
Lemma le4_szwrap : forall a, Z_to_le_bytes 4 (szwrap 32 a) = Z_to_le_bytes 4 a.
Proof. intros a. apply le4_eqm. apply szwrap_eqm. lia. Qed.
Lemma le4_wrap32 : forall a, Z_to_le_bytes 4 (wrap32 a) = Z_to_le_bytes 4 a.
Proof. intros a. apply le4_eqm. rewrite wrap32_mod. apply Z.mod_mod. lia. Qed.
Lemma le8_wrap64 : forall a, Z_to_le_bytes 8 (wrap64 a) = Z_to_le_bytes 8 a.
Proof.
  intros a. rewrite <- (SymExec.Z_to_le_bytes_mod 8 (wrap64 a)), <- (SymExec.Z_to_le_bytes_mod 8 a). change (8 * Z.of_nat 8) with 64.
  rewrite wrap64_mod. rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma le8_mod64 : forall a, Z_to_le_bytes 8 (a mod 2 ^ 64) = Z_to_le_bytes 8 a.
Proof. intros a. rewrite <- (SymExec.Z_to_le_bytes_mod 8 (a mod 2 ^ 64)), <- (SymExec.Z_to_le_bytes_mod 8 a). change (8 * Z.of_nat 8) with 64. rewrite Z.mod_mod by lia. reflexivity. Qed.

Lemma hold_drop : forall h b n, 0 <= n <= b -> 0 <= h < 2 ^ b -> 0 <= h / 2 ^ n < 2 ^ (b - n).
Proof.
  intros h b n Hn Hh. pose proof (Z.pow_pos_nonneg 2 n ltac:(lia) ltac:(lia)).
  split; [apply Z.div_pos; lia|].
  apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia. replace (n + (b - n)) with b by lia. lia.
Qed.
Lemma shiftr_div : forall h n, 0 <= n -> Z.shiftr h n = h / 2 ^ n.
Proof. intros. apply Z.shiftr_div_pow2. lia. Qed.


Lemma LX_step : forall v s c r s' c' r',
  LX v (mkW s c r) ->
  is_wrap s' = is_wrap s -> is_wbits s' = is_wbits s -> live_mode (is_mode s') ->
  (is_flags s' = 0 \/ (is_flags s' = -1 /\ (is_mode s' = HEAD \/ is_mode s' = BAD) /\ ir_out r' = ir_left r')) ->
  ir_in r' = ir_in r -> - 2 ^ 31 <= ir_ret r' < 2 ^ 31 -> -1 <= ic_msg c' <= 27 -> is_havedict s' = is_havedict s ->
  LX v (mkW s' c' r').
Proof.
  intros v s c r s' c' r' HX E1 E2 Hl Hf E3 Hr Hm E4. unfold LX in *. cbn [w_s w_c w_r] in *.
  destruct HX as (Xwrap & Xwbits & Xlive & Xflags & Xin & Xret & Xmsg & Xhd).
  rewrite E1, E2, E3, E4. repeat (split; [assumption|]). exact Xhd.
Qed.

Lemma LX_step0 : forall v s c r s' c' r',
  LX v (mkW s c r) -> is_mode s <> HEAD -> is_mode s <> BAD ->
  is_wrap s' = is_wrap s -> is_wbits s' = is_wbits s -> is_flags s' = is_flags s -> live_mode (is_mode s') ->
  ir_in r' = ir_in r -> - 2 ^ 31 <= ir_ret r' < 2 ^ 31 -> -1 <= ic_msg c' <= 27 -> is_havedict s' = is_havedict s ->
  LX v (mkW s' c' r').
Proof.
  intros v s c r s' c' r' HX N1 N2 E1 E2 Ef Hl E3 Hr Hm E4.
  apply (LX_step v s c r s' c' r' HX E1 E2 Hl); [| exact E3 | exact Hr | exact Hm | exact E4].
  left. rewrite Ef. unfold LX in HX. cbn [w_s w_c w_r] in HX.
  destruct HX as (_ & _ & _ & [X0 | (X1 & XM & _)] & _); [exact X0 | exfalso; destruct XM; contradiction].
Qed.

End FXG.
Ltac live_mode_tac := cbn; unfold live_mode; cbv [FLAGS HCRC SYNC HEAD TIME OS EXLEN EXTRA NAME COMMENT DICTID DICT TYPE TYPEDO STORED COPY_ COPY TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM]; lia.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.


End FXG.
Ltac fr_weak Hfr :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; apply Hfr; eapply reg_in_sub; [| exact Hr]; reflexivity.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

End FXG.
Ltac regs_via Hfr :=
  repeat match goal with |- _ /\ _ => split end;
  try (lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr n eq_refl); assumption end).
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.


End FXG.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.
Lemma szwrap32_of_mod32 : forall x, - 2 ^ 31 <= x < 2 ^ 31 -> szwrap 32 (x mod 2 ^ 32) = x.
Proof.
  intros x Hx. unfold szwrap. change (2 ^ (32 - 1)) with 2147483648 in *. change (2 ^ 31) with 2147483648 in Hx. change (2 ^ 32) with 4294967296.
  Z.to_euclidean_division_equations. lia.
Qed.
Lemma mod64_nz : forall x, x <> 0 -> - 2 ^ 64 < x < 2 ^ 64 -> x mod 2 ^ 64 <> 0.
Proof. intros x Hx Hr. change (2 ^ 64) with 18446744073709551616 in *. Z.to_euclidean_division_equations. lia. Qed.
Lemma mod64_z : forall x, x = 0 -> x mod 2 ^ 64 = 0.
Proof. intros x ->. reflexivity. Qed.
Lemma land7_mod : forall b, Z.land b 7 = b mod 8.
Proof. intros b. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land_m8 : forall b, 0 <= b -> Z.land b (-8) = b - Z.land b 7.
Proof.
  intros b Hb. rewrite land7_mod.
  change (-8) with (Z.lnot 7).
  rewrite <- Z.ldiff_land. change 7 with (Z.ones 3). rewrite Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. Z.to_euclidean_division_equations. lia.
Qed.
Lemma lor8_small : forall b, 0 <= b < 8 -> Z.lor b 8 = b + 8.
Proof.
  intros b Hb.
  assert (D : Z.land b 8 = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    change 8 with (2 ^ 3). rewrite Z.pow2_bits_eqb by lia.
    destruct (Z.eqb_spec 3 n) as [<-|]; [| apply andb_false_r].
    replace (Z.testbit b 3) with false; [reflexivity|]. symmetry. apply Z.testbit_false; [lia|].
    change (2 ^ 3) with 8. Z.to_euclidean_division_equations. lia. }
  rewrite <- Z.lxor_lor by exact D. symmetry. apply Z.add_nocarry_lxor. exact D.
Qed.
End FXG.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.


End FXG.
Ltac retc_disj :=
  cbn [length Z_to_le_bytes Z.of_nat Pos.of_succ_nat Pos.succ];
  lazymatch goal with
  | |- _ <= cv_S ?v + _ \/ cv_S ?v + _ + _ <= _ =>
      match goal with CfS : sep _ _ (cv_S v) 7176, CS : 0 < cv_S v /\ _ |- _ => clear - CfS CS; unfold sep in CfS; lia end
  | |- _ <= cv_ZP ?v + _ \/ cv_ZP ?v + _ + _ <= _ =>
      match goal with CfZ : sep _ _ (cv_ZP v) 112, CZP : 0 < cv_ZP v /\ _ |- _ => clear - CfZ CZP; unfold sep in CfZ; lia end
  | |- _ <= cv_P0 ?v + _ \/ cv_P0 ?v + _ + _ <= _ =>
      match goal with CfP : 0 < cv_NO v -> sep _ _ (cv_P0 v) (cv_NO v), CP0 : 0 < cv_P0 v /\ _,
                      R1 : 0 <= ?pt, R2 : ?pt + ?lf = cv_NO v, R3 : 0 <= ?lf |- _ =>
        clear - CfP CP0 R1 R2 R3; unfold sep in CfP; lia end
  | |- _ <= cv_sp ?v - _ + _ \/ cv_sp ?v - _ + _ + _ <= _ => clear; lia
  | |- _ => clear; lia
  end.
Ltac retc_tower C HRC :=
  repeat (apply (RETC_other _ C); [| solve [cbn; lia] | solve [cbn [length Z_to_le_bytes Z.of_nat Pos.of_succ_nat Pos.succ]; lia] | solve [retc_disj] ]);
  eapply RETC_regs; [exact HRC | reflexivity].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.


Lemma arm_post_rebase : forall v s c0 r0 c1 r1 M res R' M' pc',
  ir_put r0 = ir_put r1 ->
  arm_post v (mkW s c1 r1) M res R' M' pc' -> arm_post v (mkW s c0 r0) M res R' M' pc'.
Proof.
  intros v s c0 r0 c1 r1 M res R' M' pc' Hp H. destruct res as [u w'|w'|rc w']; cbn [arm_post w_s w_r] in *; rewrite ?Hp; exact H.
Qed.


Section Scratch.
  Variable v : icv.
  Hypothesis C : ictx v.

  Definition SCR : franges := [(cv_sp v - INF_FRAME - INF_SCRATCH, INF_SCRATCH)].

  Lemma izs6_agree : forall F M M' c,
    izs6 v M c -> agree_out F M M' -> disj_franges F (cv_ZP v) 112 -> izs6 v M' c.
  Proof.
    intros F M M' c H Hag Hd. pose proof (ic_ZP _ C) as CZP. unfold izs6 in *.
    destruct H as (Z0 & Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72 & Z80 & Z96).
    repeat match goal with |- _ /\ _ => split end;
      (eapply (cell_agree_out _ F M M'); [exact Hag | intros x Hx; apply Hd; cbn in Hx; lia | lia | cbn; lia | assumption]).
  Qed.

  Lemma LMEM_agree_scratch : forall s c r M M',
    LMEM v (mkW s c r) M -> 0 <= ir_put r <= cv_NO v ->
    agree_out SCR M M' -> (forall x, M x <> None -> M' x <> None) ->
    LMEM v (mkW s c r) M'.
  Proof.
    intros s c r M M' HM Hput Hag Hg.
    open_ictx C. open_lmem HM. unfold SCR, INF_FRAME, INF_SCRATCH in Hag.
    assert (DJ : forall a n, (cv_sp v - 224 <= a \/ a + n <= cv_sp v - 224 - 192) -> disj_franges [(cv_sp v - 224 - 192, 192)] a n).
    { intros a n Ha x Hx [Hin|Hin]; [cbn in Hin; lia | exact Hin]. }
    constructor; cbn [w_s w_c w_r].
    - intros x Hx. rewrite (Hag x); [exact (Mrod x Hx)|]. intros [Hin|Hin]; [| exact Hin]. unfold ROD6_LO, ROD6_HI in Hx. clear - Hx Hin Csp. lia.
    - unfold is6_scalars in *. eapply (fields_agree_out s6_segs _ M M' _ is6_layout _ is6_SIZE Msc is6_layout_within Hag); [| lia | unfold is6_SIZE; lia].
      apply DJ. unfold sep in CfS. unfold is6_SIZE. clear - CfS CS. lia.
    - eapply (cells_agree_out _ _ M M'); [exact Hag | apply DJ; unfold sep in CfS; clear - CfS CS; lia | cbn; lia | lia | lia | exact Mlens].
    - eapply (cells_agree_out _ _ M M'); [exact Hag | apply DJ; unfold sep in CfS; clear - CfS CS; lia | cbn; lia | lia | lia | exact Mwork].
    - eapply (cells_agree_out _ _ M M'); [exact Hag | apply DJ; unfold sep in CfS; clear - CfS CS; lia | cbn; lia | lia | lia | exact Mcodes].
    - intros Hwn. eapply (cells_agree_out _ _ M M'); [exact Hag | apply DJ; unfold sep in CfW; clear - CfW CWB Hwn; lia | cbn; lia | lia | lia | exact (Mwin Hwn)].
    - destruct (Z.eq_dec (cv_NI v) 0) as [E0|E0]; [rewrite E0; apply cells_nil|].
      eapply (cells_agree_out _ _ M M'); [exact Hag | apply DJ; specialize (CfI ltac:(lia)); unfold sep in CfI; clear - CfI CI0; lia | cbn; lia | lia | lia | exact Minp].
    - destruct (Z.eq_dec (ir_put r) 0) as [E0|E0]; [rewrite E0; apply cells_nil|].
      eapply (cells_agree_out _ _ M M'); [exact Hag | apply DJ; specialize (CfP ltac:(lia)); unfold sep in CfP; clear - CfP CP0 Hput; lia | cbn; lia | lia | lia | exact Mout].
    - eapply izs6_agree; [exact Mzs | exact Hag | apply DJ; unfold sep in CfZ; clear - CfZ CZP; lia].
    - unfold iframe6 in *. unfold INF_FRAME in *.
      destruct Mfr as (Fsv & F104 & F96 & F88 & F72 & F56 & F48 & F40 & F32 & F24 & F16 & F8 & Fd0).
      split.
      { intros rg o Hro. pose proof (Fsv rg o Hro) as X. cbn in Hro.
        assert (Ho : 120 <= o /\ o + 8 <= 224)
          by (clear -Hro; destruct Hro as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]]; injection E as <- <-; lia). clear Hro.
        eapply (cell_agree_out _ _ M M'); [exact Hag | apply DJ; lia | lia | cbn; lia | exact X]. }
      repeat match goal with |- _ /\ _ => split end;
        (eapply (cell_agree_out _ _ M M'); [exact Hag | apply DJ; lia | lia | cbn; lia | assumption]).
    - unfold INF_FRAME in *. eapply (cell_agree_out _ _ M M'); [exact Hag | apply DJ; lia | lia | cbn; lia | exact Moutc].
    - intros x Hx. apply Hg. apply Mmap_f. exact Hx.
    - intros x Hx. apply Hg. apply Mmap_Z. exact Hx.
    - intros x Hx. apply Hg. apply Mmap_S. exact Hx.
    - intros x Hx. apply Hg. apply Mmap_P. exact Hx.
    - intros Hwn x Hx. apply Hg. apply (Mmap_W Hwn). exact Hx.
  Qed.

  Lemma RETC_agree_scratch : forall w M M', RETC v w M -> agree_out SCR M M' -> RETC v w M'.
  Proof.
    intros w M M' H Hag. pose proof (ic_sp _ C) as Csp. unfold RETC, SCR, INF_FRAME, INF_SCRATCH, IMG6_TOP in *.
    eapply (cell_agree_out _ _ M M'); [exact Hag | | lia | cbn; lia | exact H].
    intros x Hx [Hin|Hin]; [cbn in Hin; lia | exact Hin].
  Qed.

  Lemma agree_scratch_store : forall M M' (b : Z) bs,
    agree_out SCR M M' -> cv_sp v - INF_FRAME - INF_SCRATCH <= b -> b + Z.of_nat (length bs) <= cv_sp v - INF_FRAME ->
    agree_out SCR M (wbytes M' (zw b) bs).
  Proof.
    intros M M' b bs Hag H1 H2. pose proof (ic_sp _ C) as Csp. unfold SCR, INF_FRAME, INF_SCRATCH, IMG6_TOP in *.
    apply agree_out_wbytes; [exact Hag | lia | lia |]. apply sub_franges_here; lia.
  Qed.
End Scratch.


Lemma word_le_Z : forall (n : nat) (w : word), word_to_le_bytes n w = Z_to_le_bytes n (bv_unsigned w).
Proof. reflexivity. Qed.

End FXG.
Ltac tower_cell :=
  rewrite ?word_le_Z;
  first [ apply cell_write_same; [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia]
        | eapply cell_write_other;
          [ tower_cell
          | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia
          | cbn [length Z_to_le_bytes Z.of_nat Pos.of_succ_nat Pos.succ]; lia
          | cbn [length Z_to_le_bytes Z.of_nat Pos.of_succ_nat Pos.succ]; lia ] ].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.


Lemma is6_scalars_win_contents : forall M S p s w,
  is6_scalars M S p (iset_window s w) = is6_scalars M S p s.
Proof. intros M S p s w. unfold is6_scalars, is6_vals, isl_vals. destruct s; reflexivity. Qed.
Lemma is6_scalars_win_blk : forall M S p s b,
  is6_scalars M S p (iset_window_blk s b) = is6_scalars M S p s.
Proof. intros M S p s b. unfold is6_scalars, is6_vals, isl_vals. destruct s; reflexivity. Qed.

Section Win.
  Variable v : icv.
  Hypothesis C : ictx v.

  Lemma LMEM_blit_win : forall s c r (n : nat) (d so : Z) M,
    LMEM v (mkW s c r) M -> cv_WN v = 32768 -> arr_len (is_window s) = 32768 ->
    0 <= d -> d + Z.of_nat n <= 32768 -> 0 <= so -> so + Z.of_nat n <= ir_put r -> ir_put r <= cv_NO v ->
    (forall i, 0 <= i < cv_NO v -> 0 <= arr_get (ic_outbuf c) i < 256) ->
    LMEM v (mkW (iset_window s (arr_blit (is_window s) d (ic_outbuf c) so (Z.of_nat n))) c r)
           (wbytes M (zw (cv_WB v + d)) (cbytes (arr_get (ic_outbuf c)) so n)).
  Proof.
    intros s c r n d so M HM HWN Hwl Hd0 Hdn Hso0 Hson Hput Houtb.
    open_ictx C. open_lmem HM.
    set (bs := cbytes (arr_get (ic_outbuf c)) so n).
    assert (Hlen : length bs = n) by (subst bs; apply cbytes_length).
    destruct n as [|n'].
    { cbn [cbytes] in bs. subst bs. cbn [wbytes].
      replace (arr_blit (is_window s) d (ic_outbuf c) so (Z.of_nat 0)) with (is_window s) by reflexivity.
      replace (iset_window s (is_window s)) with s by (destruct s; reflexivity). exact HM. }
    assert (HW : cv_WN v = 32768 /\ 0 < cv_WB v /\ cv_WB v mod 16 = 0) by (clear - CWB HWN; lia). destruct HW as (_ & HWB0 & _).
    assert (HNO : 0 < cv_NO v) by lia.
    specialize (CPW HNO). specialize (CfW). specialize (CSW). specialize (CZW).
    constructor; cbn [w_s w_c w_r].
    - intros x Hx. rewrite wbytes_inside; [exact (Mrod x Hx) | lia | rewrite Hlen; lia |]. unfold offimg, IMG6_TOP in CoW. unfold ROD6_LO, ROD6_HI in Hx. rewrite Hlen. clear - Hx CoW CWB HWN Hd0 Hdn. lia.
    - rewrite is6_scalars_win_contents. unfold is6_scalars in *.
      apply (fields_write_other s6_segs _ _ is6_layout _ is6_SIZE _ _ Msc is6_layout_within); [lia | unfold is6_SIZE; lia | lia | rewrite Hlen; lia |].
      unfold sep in CSW. unfold is6_SIZE. rewrite Hlen. clear - CSW CS CWB HWN Hd0 Hdn. lia.
    - replace (is_lens (iset_window s _)) with (is_lens s) by (destruct s; reflexivity).
      apply (cells_write_other _ _ _ _ _ _ _ _ _ Mlens); [cbn; lia | lia | lia | lia | rewrite Hlen; lia | unfold sep in CSW; rewrite Hlen; clear - CSW CS CWB HWN Hd0 Hdn; lia].
    - replace (is_work (iset_window s _)) with (is_work s) by (destruct s; reflexivity).
      apply (cells_write_other _ _ _ _ _ _ _ _ _ Mwork); [cbn; lia | lia | lia | lia | rewrite Hlen; lia | unfold sep in CSW; rewrite Hlen; clear - CSW CS CWB HWN Hd0 Hdn; lia].
    - replace (is_codes (iset_window s _)) with (is_codes s) by (destruct s; reflexivity).
      apply (cells_write_other _ _ _ _ _ _ _ _ _ Mcodes); [cbn; lia | lia | lia | lia | rewrite Hlen; lia | unfold sep in CSW; rewrite Hlen; clear - CSW CS CWB HWN Hd0 Hdn; lia].
    - intros _.
      match goal with |- context [is_window (iset_window s ?w)] => replace (is_window (iset_window s w)) with w by (destruct s; reflexivity) end.
      rewrite HWN. specialize (Mwin ltac:(lia)). rewrite HWN in Mwin.
      intros i Hi. rewrite arr_get_blit.
      destruct (Z_lt_le_dec i d) as [Hlo|Hge]; [| destruct (Z_lt_le_dec i (d + Z.of_nat (S n'))) as [Hin|Hhi]].
      + replace ((d <=? i) && (i <? d + Z.max 0 (Z.of_nat (S n'))) && arr_inb (is_window s) i) with false
          by (destruct (Z.leb_spec d i); [exfalso; lia | reflexivity]).
        apply cell_write_other; [exact (Mwin i Hi) | lia | cbn; lia | lia | rewrite Hlen; lia | rewrite Hlen; cbn; lia].
      + replace ((d <=? i) && (i <? d + Z.max 0 (Z.of_nat (S n'))) && arr_inb (is_window s) i) with true.
        2:{ symmetry. unfold arr_inb. rewrite Hwl. destruct (Z.leb_spec d i); [| exfalso; lia]. destruct (Z.ltb_spec i (d + Z.max 0 (Z.of_nat (S n')))); [| exfalso; lia].
            destruct (Z.leb_spec 0 i); [| exfalso; lia]. destruct (Z.ltb_spec i 32768); [reflexivity | exfalso; lia]. }
        pose proof (memcpy_dst_cells s6_segs M (cv_WB v + d) bs ltac:(lia) ltac:(rewrite Hlen; lia) (i - d) ltac:(rewrite Hlen; lia)) as Hnew.
        replace (cv_WB v + d + 1 * (i - d)) with (cv_WB v + 1 * i) in Hnew by lia.
        replace (bv_unsigned (nth (Z.to_nat (i - d)) bs (Z_to_bv 8 0))) with (arr_get (ic_outbuf c) (so + (i - d))) in Hnew; [exact Hnew|].
        subst bs. rewrite (cbytes_nth (arr_get (ic_outbuf c)) (S n') (Z.to_nat (i - d)) so) by lia.
        rewrite Z2Nat.id by lia. rewrite Z_to_bv_small; [reflexivity|]. unfold bv_modulus. cbn. pose proof (Houtb (so + (i - d)) ltac:(lia)). lia.
      + replace ((d <=? i) && (i <? d + Z.max 0 (Z.of_nat (S n'))) && arr_inb (is_window s) i) with false
          by (destruct (Z.leb_spec d i); [destruct (Z.ltb_spec i (d + Z.max 0 (Z.of_nat (S n')))); [exfalso; lia | reflexivity] | reflexivity]).
        apply cell_write_other; [exact (Mwin i Hi) | lia | cbn; lia | lia | rewrite Hlen; lia | rewrite Hlen; cbn; lia].
    - destruct (Z.eq_dec (cv_NI v) 0) as [E0|E0]; [rewrite E0; apply cells_nil|].
      apply (cells_write_other _ _ _ _ _ _ _ _ _ Minp); [cbn; lia | lia | lia | lia | rewrite Hlen; lia |]. specialize (CIW ltac:(lia)). unfold sep in CIW. rewrite Hlen. clear - CIW CI0 CWB HWN Hd0 Hdn E0; lia.
    - destruct (Z.eq_dec (ir_put r) 0) as [E0|E0]; [rewrite E0; apply cells_nil|].
      apply (cells_write_other _ _ _ _ _ _ _ _ _ Mout); [cbn; lia | lia | lia | lia | rewrite Hlen; lia |]. unfold sep in CPW. rewrite Hlen. clear - CPW CP0 CWB HWN Hd0 Hdn Hput; lia.
    - apply (izs6_other v C); [exact Mzs | lia | rewrite Hlen; lia | unfold sep in CZW; rewrite Hlen; clear - CZW CZP CWB HWN Hd0 Hdn; lia].
    - apply (iframe6_other v C); [exact Mfr | lia | rewrite Hlen; lia | unfold iframe6_ok, INF_FRAME; unfold sep in CfW; rewrite Hlen; clear - CfW Csp CWB HWN Hd0 Hdn; lia].
    - pose proof (ic_sp _ C) as Csp_o; unfold INF_FRAME, INF_SCRATCH, IMG6_TOP in Csp_o, Moutc |- *; apply (cell_write_other _ _ _ _ _ _ _ Moutc); [lia | cbn; lia | lia | rewrite Hlen; lia | unfold sep in CfW; rewrite Hlen; clear - CfW Csp CWB HWN Hd0 Hdn; lia].
    - apply mapped_wbytes. exact Mmap_f.
    - apply mapped_wbytes. exact Mmap_Z.
    - apply mapped_wbytes. exact Mmap_S.
    - apply mapped_wbytes. exact Mmap_P.
    - intros _. apply mapped_wbytes. apply Mmap_W. lia.
  Qed.
End Win.

Lemma ret_ok_lit : forall z, 0 <= z < 2 ^ 64 -> z mod 2 = 0 -> ret_ok (zw z).
Proof. intros z Hz H2. apply ret_ok_even. rewrite u_zw_small by lia. exact H2. Qed.
End FXG.
