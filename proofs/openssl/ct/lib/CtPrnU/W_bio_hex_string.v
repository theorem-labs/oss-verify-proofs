(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Monad PrintfModel PrintfModelX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Printf_ctfmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit Printf_lib F_pop_arg F_printf_iface F_vsnprintf.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApWalkTac W_bio_push W_bio_write W_bio_printf.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtPrnU Require Import PrnFmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition BIO_HEX_STRING : Z := 0x10ddf8.
Definition HX_LOOP : Z := 0x10de88.
Definition HX_TAIL : Z := 0x10def4.
Definition HX_LAST : Z := 0x10df18.
(* [comment removed for export] *)
Definition HX_STACK : Z := 6656.

(* [comment removed for export] *)
Lemma wz_mod64 : forall z, Z_to_bv 64 (z mod 2^64) = Z_to_bv 64 z.
Proof.
  intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
  apply Z.mod_mod. lia.
Qed.
Lemma bio_null_cells_mod : forall meth pv nw, bio_null_cells meth pv (nw mod 2^64) = bio_null_cells meth pv nw.
Proof. intros. unfold bio_null_cells, bio_cells, MallocRep.wz. rewrite wz_mod64. reflexivity. Qed.

(* [comment removed for export] *)
Definition hexstring_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (lo out pv : Z) (canary : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (nw' : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctusegs)
    /\ munch [(lo, bv_unsigned sp); (out, out + 128)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
    /\ frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k)
    /\ stk ctusegs m' lo (bv_unsigned sp) /\ ssp_cells m' canary
    /\ rw_cells ctusegs m' out (bio_null_cells NULL_METHOD pv nw') /\ 0 <= nw' < 2^64.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section HX. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Variables (sp gp tp : word) (F : bvmap 5 word) (m0 : mem) (lo out pv S len : Z) (canary : word) (bs : list byte).
(* [comment removed for export] *)
Variables (vra v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 : word).

Hypothesis GLO : 3493888 <= lo.                   (* [comment removed for export] *)
Hypothesis LO : lo <= bv_unsigned sp - 6656.      (* [comment removed for export] *)
Hypothesis SP63 : bv_unsigned sp < 2^63.
Hypothesis OB : 0 < out /\ out + 128 <= lo /\ (out + 128 <= 65536 \/ 3493888 <= out).
Hypothesis HLEN : 0 < len < 2^31.
Hypothesis LEN : Z.of_nat (length bs) = len.
Hypothesis S0 : 0 < S.
Hypothesis SLO : S + len <= lo.
Hypothesis SEP : S + len <= out \/ out + 128 <= S.
Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
Hypothesis OAL : out mod 8 = 0.

(* [comment removed for export] *)
Definition W0 : list (Z * Z) := [(lo, bv_unsigned sp); (out, out + 128)].
(* [comment removed for export] *)
Definition hx_hi : list cell := [C8 v27; C8 v26; C8 v25; C8 v24; C8 v23; C8 v22; C8 v21; C8 v20; C8 v19; C8 v18; C8 v9; C8 v8; C8 vra].
(* [comment removed for export] *)
Definition hx_inv (clo : list cell) (m : mem) : Prop :=
  mem_inv ctusegs m /\ stk ctusegs m lo (bv_unsigned sp + -128) /\ ssp_cells m canary /\ null_meth_cells m /\ bytes_at ctusegs m S bs
  /\ munch W0 m0 m /\ wmono ctusegs m0 m /\ rw_cells ctusegs m (bv_unsigned sp + -104) hx_hi
  /\ rw_cells ctusegs m (bv_unsigned sp + -128) clo /\ cells_size clo = 24%nat.
Definition hx_bio (m : mem) (nw : Z) : Prop := 0 <= nw < 2^64 /\ rw_cells ctusegs m out (bio_null_cells NULL_METHOD pv nw).
Definition hx_F (Fc : bvmap 5 word) : Prop := forall k : reg, bv_unsigned k <> 10 -> reg_get Fc k = reg_get F k.

Local Ltac open_inv H :=
  destruct H as (MI & ST & [SSP1 SSP2] & [NMa NMb] & HS & MU & WM & FRH & FRL & SZ); unfold got_ssp, ssp_guard in SSP1, SSP2; unfold NULL_METHOD in NMa, NMb.

Local Ltac facts :=
  pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR;
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -128)) = bv_unsigned sp + -128) by (apply unsigned_lit; lia);
  assert (SEPB : out + 128 <= lo \/ bv_unsigned sp <= out) by lia;
  assert (SEPS : S + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= S) by lia;
  assert (SEPM : 2978032 + 72 <= lo \/ bv_unsigned sp <= 2978032) by lia;
  assert (SEPG : 3271976 + 8 <= lo \/ bv_unsigned sp <= 3271976) by lia;
  assert (SEPC : 3486312 + 8 <= lo \/ bv_unsigned sp <= 3486312) by lia.

(* [comment removed for export] *)
Lemma hx_data_read : forall m t a, bytes_at ctusegs m S bs -> 0 <= t < len -> a = wa (S + t) ->
  exists b : byte, nth_error bs (Z.to_nat t) = Some b /\ ov_read_bytes ctusegs m a 1 = Some [b].
Proof using HLEN LEN.
  clear SP16 OAL. intros m t a HS Ht ->.
  destruct (nth_error bs (Z.to_nat t)) as [b|] eqn:E; [| exfalso; apply nth_error_None in E; lia].
  exists b. split; [reflexivity|]. exact (u8ro_read ctusegs m S bs t b _ HS E ltac:(lia) eq_refl).
Qed.
Lemma hx_byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof using bs. clear SP16 OAL. intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia. Qed.

(* [comment removed for export] *)
Lemma hx_call : forall (x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
    (Fc : bvmap 5 word) (fc : bv 32) (m : mem) (nw : Z) (clo : list cell) (A : Z) (fmt : list Z) (args : list parg) (o : list Z) (retpc : Z)
    (P : machine_state -> Prop),
  hx_inv clo m -> hx_bio m nw -> frm0 fc -> hx_F Fc ->
  printf_call_ok m lo (bv_unsigned sp + -128) A fmt [a2; a3; a4; a5; a6; a7] args o ->
  a0 = Z_to_bv 64 out -> a1 = Z_to_bv 64 A -> x1 = Z_to_bv 64 retpc -> 0 <= retpc < 2^64 -> retpc mod 2 = 0 ->
  (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (Fc' : bvmap 5 word) (fc' : bv 32) (m' : mem),
     hx_inv clo m' -> hx_bio m' ((nw + zlength o) mod 2^64) -> frm0 fc' -> hx_F Fc' ->
     evt ctusegs P (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' x8 x9 (Z_to_bv 64 (zlength o)) a1' a2' a3' a4' a5' a6' a7'
                             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6')
                        Fc' (Z_to_bv 64 retpc) fc' None m' (seg_rom ctusegs))) ->
  evt ctusegs P (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                   Fc (Z_to_bv 64 BIO_PRINTF) fc None m (seg_rom ctusegs)).
Proof using GLO HLEN LEN LO OAL OB SEP SLO SP16 SP63.
  intros until P. intros INV [NW HB] FRM HFC PC -> -> -> Hret EVEN K. pose proof INV as INV'. open_inv INV. facts.
  eapply evt_cut.
  { eapply (BIO_printf_null_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fc fc _ out pv nw A lo canary);
      [rewrite ESP; exact ST| exact MI| unfold GLOBALS_TOP; lia| rewrite ESP; unfold BIO_PRINTF_STACK, VSN_DEPTH; lia| rewrite ESP; lia
      | rewrite ESP; clear - SP16; Z.div_mod_to_equations; lia
      | split; [exact SSP1| exact SSP2]| exact FRM
      | exact HB| unfold obj_range, BIO_SIZE, GLOBALS_TOP; lia| exact OAL| exact NW| split; [exact NMa| exact NMb]
      | rewrite ESP; exact PC| reflexivity| reflexivity]. }
  cbv beta. unfold bio_printf_post. intros ms' (u0 & u1 & u2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & F2 & fc2 & m2 & -> & MU2 & WM2 & MI2 & FRM2 & FREG2 & ST2 & SSP2' & HB2).
  rewrite ?ESP in *.
  replace (ret_pc (Z_to_bv 64 retpc)) with (Z_to_bv 64 retpc) by (symmetry; apply ret_pc_even; [lia| exact EVEN]).
  (* [comment removed for export] *)
  clear ST HB. unfold W0 in MU. unfold hx_hi in FRH. transport_after_call ctusegs m m2 MU2 WM2.
  apply K.
  - split; [exact MI2|]. split; [exact ST2|]. split; [exact SSP2'|]. split; [split; [exact NMa| exact NMb]|].
    split; [exact HS|]. split; [exact MU|]. split; [exact WM|]. split; [exact FRH|]. split; [exact FRL| exact SZ].
  - split; [| rewrite bio_null_cells_mod; exact HB2]. apply Z.mod_pos_bound. lia.
  - exact FRM2.
  - intros k Hk. rewrite (FREG2 k Hk). apply HFC. exact Hk.
Qed.

(* [comment removed for export] *)
Definition hx_lo (pad0 : list byte) : list cell := [CB 8 pad0; C8 (Z_to_bv 64 (len + -1)); C8 (Z_to_bv 64 20)].

Local Ltac hx_ref K := exfalso; rewrite ?unsigned_lit in K by lia;
  repeat match type of K with context [Z.ltb ?x ?y] => first [rewrite (proj2 (Z.ltb_lt x y)) in K by lia | rewrite (proj2 (Z.ltb_ge x y)) in K by lia] end;
  cbn in K; rewrite ?unsigned_lit in K by lia; first [discriminate K | lia].

(* [comment removed for export] *)
Lemma hx_last : forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
    (Fc : bvmap 5 word) (fc : bv 32) (m : mem) (nw : Z) (clo : list cell),
  hx_inv clo m -> hx_bio m nw -> frm0 fc -> hx_F Fc ->
  evt ctusegs (hexstring_post vra sp gp tp v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 F lo out pv canary m0)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp (Z_to_bv 64 out) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 S) (Z_to_bv 64 (len + -1)) x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
        Fc (Z_to_bv 64 HX_LAST) fc None m (seg_rom ctusegs)).
Proof using GLO HLEN LEN LO OAL OB S0 SEP SLO SP16 SP63.
  intros until clo. intros INV BIO FRM HFC. pose proof INV as INV'. open_inv INV. facts. unfold HX_LAST.
  (* [comment removed for export] *)
  zstep. zstep. if_cases K; zify_cond K; [hx_ref K|]. clear K.
  zstep. zstep. zstep. zstep. if_cases K; zify_cond K; [hx_ref K|]. clear K.
  zstep. if_cases K; zify_cond K; [hx_ref K|]. clear K.
  destruct (hx_data_read m (len + -1) (wa (S + (len + -1))) HS ltac:(lia) ltac:(reflexivity)) as (b & NTH & RD).
  pose proof (hx_byte_range b) as BR.
  zstep. clear RD.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.
  eapply (hx_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fc fc m nw clo A_C15 FMT_C15 [PA_u (bv_unsigned b)] (hex2 (bv_unsigned b)) 0x10df48);
    [exact INV'| exact BIO| exact FRM| exact HFC
    | apply pcok_C15; [exact MI| exact BR| rewrite unsigned_lit by lia; apply Z.mod_small; lia]
    | reflexivity| reflexivity| reflexivity| lia| reflexivity| ].
  clear dependent m. clear SZ. intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Fc' fc' m INV [NW' HB'] FRM' HFC'.
  open_inv INV. clear ESP SEPB SEPS SEPM SEPG SEPC SPR. facts. unfold hx_hi in FRH.
  zstep. (* [comment removed for export] *)
  (* [comment removed for export] *)
  do 13 zstep.
  (* [comment removed for export] *)
  assert (FR : rw_cells ctusegs m (bv_unsigned sp + -128) (clo ++ [C8 v27; C8 v26; C8 v25; C8 v24; C8 v23; C8 v22; C8 v21; C8 v20; C8 v19; C8 v18; C8 v9; C8 v8; C8 vra])).
  { apply rw_cells_app. split; [exact FRL|]. rewrite SZ. replace (bv_unsigned sp + -128 + Z.of_nat 24) with (bv_unsigned sp + -104) by lia. exact FRH. }
  clear FRL FRH.
  zstep. (* [comment removed for export] *)
  eapply stk_release in FR; [| exact ST| lia]. clear ST. rename FR into ST.
  rewrite cells_size_app, SZ in ST. cbn [cells_size csize Nat.add] in ST.
  replace (bv_unsigned sp + -128 + Z.of_nat 128) with (bv_unsigned sp) in ST by lia.
  zstep. (* [comment removed for export] *)
  apply evt_done. unfold hexstring_post.
  do 14 eexists. exists Fc', fc', m, ((nw + zlength (hex2 (bv_unsigned b))) mod 2^64). split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FRM'|]. split; [exact HFC'|].
  split; [exact ST|]. split; [split; [exact SSP1| exact SSP2]|]. split; [exact HB'| exact NW'].
Qed.

(* [comment removed for export] *)
Lemma hx_tail : forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 x23 x24 x26 x27 t3 t4 t5 t6 : word)
    (Fc : bvmap 5 word) (fc : bv 32) (m : mem) (nw : Z) (pad0 : list byte) (j : Z),
  hx_inv (hx_lo pad0) m -> hx_bio m nw -> frm0 fc -> hx_F Fc -> 0 <= j < 16 ->
  evt ctusegs (hexstring_post vra sp gp tp v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 F lo out pv canary m0)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp (Z_to_bv 64 out) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 S) x19 x20 x21 x22 x23 x24 (Z_to_bv 64 j) x26 x27 t3 t4 t5 t6)
        Fc (Z_to_bv 64 HX_TAIL) fc None m (seg_rom ctusegs)).
Proof using GLO HLEN LEN LO OAL OB S0 SEP SLO SP16 SP63.
  intros until j. intros INV BIO FRM HFC HJ. pose proof INV as INV'. open_inv INV. facts. unfold HX_TAIL. unfold hx_lo in FRL.
  (* [comment removed for export] *)
  zstep.
  (* [comment removed for export] *)
  zstep. if_cases K; zify_cond K.
  - (* [comment removed for export] *)
    apply (hx_last _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fc fc m nw (hx_lo pad0) INV' BIO FRM HFC).
  - (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    eapply (hx_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fc fc m nw (hx_lo pad0) A_C12 FMT_C12 [PA_i 20; PA_s []] (zrepeat 32 20) 0x10df18);
      [exact INV'| exact BIO| exact FRM| exact HFC
      | apply pcok_C12; [exact MI| unfold STATIC_SPLIT; lia]
      | reflexivity| reflexivity| reflexivity| lia| reflexivity| ].
    clear dependent m. intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Fc' fc' m INV BIO' FRM' HFC'.
    apply (hx_last _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fc' fc' m _ (hx_lo pad0) INV BIO' FRM' HFC').
Qed.

(* [comment removed for export] *)
Lemma wrapneg : forall i, 0 <= i < 2^63 -> Z.land (- i) 18446744073709551615 = (if i =? 0 then 0 else 2^64 - i).
Proof using bs.
  clear SP16 OAL. intros i Hi. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  destruct (Z.eqb_spec i 0) as [->|NZ]; [reflexivity|].
  replace (- i) with ((2^64 - i) + (- 1) * 2^64) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Local Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => lia end | progress f_equal ].
Local Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].

(* [comment removed for export] *)
Lemma hx_loop : forall (k : nat) (i j nw : Z) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (Fc : bvmap 5 word) (fc : bv 32) (m : mem) (pad0 : list byte),
  Z.of_nat k = len - 1 - i -> 0 <= i < len - 1 -> j = i mod 16 ->
  hx_inv (hx_lo pad0) m -> hx_bio m nw -> frm0 fc -> hx_F Fc ->
  evt ctusegs (hexstring_post vra sp gp tp v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 F lo out pv canary m0)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp (Z_to_bv 64 out) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 S) (Z_to_bv 64 (len + -1)) (Z_to_bv 64 16) (Z_to_bv 64 A_C13) (Z_to_bv 64 0x2a387) (Z_to_bv 64 A_C12) (Z_to_bv 64 A_EMPTY)
             (Z_to_bv 64 j) (Z_to_bv 64 i) (Z_to_bv 64 1) t3 t4 t5 t6)
        Fc (Z_to_bv 64 HX_LOOP) fc None m (seg_rom ctusegs)).
Proof using GLO HLEN LEN LO OAL OB S0 SEP SLO SP16 SP63.
  induction k as [|k IH]; intros until pad0; intros HK HI HJ INV BIO FRM HFC; [lia|].
  assert (HJ' : 0 <= j < 16) by (subst j; split; [apply Z.mod_pos_bound| apply Z.mod_pos_bound]; lia).
  (* [comment removed for export] *)
  assert (MID : forall (x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (Fc' : bvmap 5 word) (fc' : bv 32) (m' : mem) (nw' : Z),
    hx_inv (hx_lo pad0) m' -> hx_bio m' nw' -> frm0 fc' -> hx_F Fc' ->
    evt ctusegs (hexstring_post vra sp gp tp v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 F lo out pv canary m0)
      (MS (mkR x1' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' sp (Z_to_bv 64 out) a0' a1' a2' a3' a4' a5' a6' a7'
               (Z_to_bv 64 S) (Z_to_bv 64 (len + -1)) (Z_to_bv 64 16) (Z_to_bv 64 A_C13) (Z_to_bv 64 0x2a387) (Z_to_bv 64 A_C12) (Z_to_bv 64 A_EMPTY)
               (Z_to_bv 64 j) (Z_to_bv 64 i) (Z_to_bv 64 1) t3' t4' t5' t6')
          Fc' (Z_to_bv 64 0x10dea4) fc' None m' (seg_rom ctusegs))).
  { intros until nw'. intros INV2 BIO2 FRM2 HFC2. pose proof INV2 as INV2'. open_inv INV2. facts.
    (* [comment removed for export] *)
    zstep. zstep. if_cases K; zify_cond K; [hx_ref K|]. clear K.
    zstep. zstep. zstep. if_cases K; zify_cond K; [hx_ref K|]. clear K.
    zstep. if_cases K; zify_cond K; [hx_ref K|]. clear K.
    destruct (hx_data_read m' i (wa (S + i)) HS ltac:(lia) ltac:(reflexivity)) as (b & NTH & RD). pose proof (hx_byte_range b) as BR.
    zstep. clear RD. zstep. zstep. zstep.
    eapply (hx_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fc' fc' m' nw' (hx_lo pad0) A_C13 FMT_C13 [PA_u (bv_unsigned b)] (hex2 (bv_unsigned b) ++ [58]) 0x10decc);
      [exact INV2'| exact BIO2| exact FRM2| exact HFC2
      | apply pcok_C13; [exact MI| exact BR| rewrite unsigned_lit by lia; apply Z.mod_small; lia]
      | reflexivity| reflexivity| reflexivity| lia| reflexivity| ].
    clear MI ST SSP1 SSP2 NMa NMb HS MU WM FRH FRL SZ INV2' BIO2 FRM2 HFC2 ESP SEPB SEPS SEPM SEPG SEPC SPR. clear m'.
    intros t0c t1c t2c a1c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c Fc3 fc3 m3 INV3 BIO3 FRM3 HFC3.
    (* [comment removed for export] *)
    assert (END8 : forall (x1d t0d t1d t2d a0d a1d a2d a3d a4d a5d a6d a7d t3d t4d t5d t6d : word) (Fc4 : bvmap 5 word) (fc4 : bv 32) (m4 : mem) (nw4 j4 : Z),
      j4 = (i + 1) mod 16 ->
      hx_inv (hx_lo pad0) m4 -> hx_bio m4 nw4 -> frm0 fc4 -> hx_F Fc4 ->
      evt ctusegs (hexstring_post vra sp gp tp v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 F lo out pv canary m0)
        (MS (mkR x1d (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0d t1d t2d sp (Z_to_bv 64 out) a0d a1d a2d a3d a4d a5d a6d a7d
                 (Z_to_bv 64 S) (Z_to_bv 64 (len + -1)) (Z_to_bv 64 16) (Z_to_bv 64 A_C13) (Z_to_bv 64 0x2a387) (Z_to_bv 64 A_C12) (Z_to_bv 64 A_EMPTY)
                 (Z_to_bv 64 j4) (Z_to_bv 64 i) (Z_to_bv 64 1) t3d t4d t5d t6d)
            Fc4 (Z_to_bv 64 0x10deec) fc4 None m4 (seg_rom ctusegs))).
    { intros until j4. intros HJ4 INV4 BIO4 FRM4 HFC4. pose proof INV4 as INV4'. open_inv INV4. facts.
      assert (HJ4' : 0 <= j4 < 16) by (subst j4; split; [apply Z.mod_pos_bound| apply Z.mod_pos_bound]; lia).
      (* [comment removed for export] *)
      zstep. zstep. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
      - (* [comment removed for export] *)
        jump (eapply (IH (i + 1) j4 nw4)); [lia| lia| exact HJ4| exact INV4'| exact BIO4| exact FRM4| exact HFC4].
      - (* [comment removed for export] *)
        jump (eapply (hx_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fc4 fc4 m4 nw4 pad0 j4 INV4' BIO4 FRM4 HFC4 HJ4')). }
    pose proof INV3 as INV3'. open_inv INV3. facts.
    (* [comment removed for export] *)
    zstep. rewrite (swrap32_small (j + 1)) by lia. zstep. if_cases K; zify_cond K; [rewrite ?signed_of_Z in K by lia; lia|]. clear K.
    zstep. zstep. if_cases K; zify_cond K; rewrite ?signed_of_Z in K by lia.
    - (* [comment removed for export] *)
      eapply (END8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fc3 fc3 m3 _ (j + 1)); [| exact INV3'| exact BIO3| exact FRM3| exact HFC3].
      subst j. rewrite <- (Z.add_mod_idemp_l i 1 16) by lia. symmetry. apply Z.mod_small. lia.
    - (* [comment removed for export] *)
      zstep. zstep. zstep.
      eapply (hx_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fc3 fc3 m3 _ (hx_lo pad0) A_C14 FMT_C14 [] [10] 0x10dee8);
        [exact INV3'| exact BIO3| exact FRM3| exact HFC3
        | apply pcok_C14; exact MI
        | reflexivity| reflexivity| reflexivity| lia| reflexivity| ].
      clear MI ST SSP1 SSP2 NMa NMb HS MU WM FRH FRL SZ INV3' BIO3 FRM3 HFC3 ESP SEPB SEPS SEPM SEPG SEPC SPR. clear m3.
      intros t0e t1e t2e a1e a2e a3e a4e a5e a6e a7e t3e t4e t5e t6e Fc5 fc5 m5 INV5 BIO5 FRM5 HFC5.
      zstep. (* [comment removed for export] *)
      eapply (END8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fc5 fc5 m5 _ 0); [| exact INV5| exact BIO5| exact FRM5| exact HFC5].
      subst j. rewrite <- (Z.add_mod_idemp_l i 1 16) by lia. replace (i mod 16 + 1) with 16 by lia. reflexivity. }
  (* [comment removed for export] *)
  pose proof INV as INV'. open_inv INV. facts. unfold HX_LOOP. unfold hx_lo in FRL.
  zstep. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  - (* [comment removed for export] *) apply (MID _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fc fc m nw INV' BIO FRM HFC).
  - zstep. if_cases K2; zify_cond K2.
    + (* [comment removed for export] *) apply (MID _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fc fc m nw INV' BIO FRM HFC).
    + (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep.
      eapply (hx_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fc fc m nw (hx_lo pad0) A_C12 FMT_C12 [PA_i 20; PA_s []] (zrepeat 32 20) 0x10dea4);
        [exact INV'| exact BIO| exact FRM| exact HFC
        | apply pcok_C12; [exact MI| unfold STATIC_SPLIT; lia]
        | reflexivity| reflexivity| reflexivity| lia| reflexivity| ].
      intros t0e t1e t2e a1e a2e a3e a4e a5e a6e a7e t3e t4e t5e t6e Fc5 fc5 m5 INV5 BIO5 FRM5 HFC5.
      eapply (MID _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fc5 fc5 m5 _ INV5 BIO5 FRM5 HFC5).
Qed.

Local Ltac split24 FRL FRH :=
  lazymatch goal with FR : rw_cells _ ?mm (bv_unsigned sp + -128) ?cs |- _ =>
    let k := lazymatch cs with
             | ?c0 :: ?r =>
                 lazymatch eval vm_compute in (cells_size [c0]) with
                 | 24%nat => constr:(1%nat)
                 | _ => lazymatch r with ?c1 :: _ =>
                          lazymatch eval vm_compute in (cells_size [c0; c1]) with
                          | 24%nat => constr:(2%nat)
                          | _ => constr:(3%nat) end end
                 end
             end in
    pose proof (proj1 (rw_cells_app mm _ (firstn k cs) (skipn k cs)) ltac:(cbn [firstn skipn app]; exact FR)) as [FRL FRH];
    cbn [firstn skipn] in FRL, FRH; cbn [cells_size csize Nat.add] in FRH;
    replace (bv_unsigned sp + -128 + Z.of_nat 24) with (bv_unsigned sp + -104) in FRH by lia; clear FR
  end.

Lemma hx_zero : forall (t0 t1 t2 a2 a3 a5 a6 a7 t3 t4 t5 t6 : word) (fc : bv 32) (nw : Z),
  stk ctusegs m0 lo (bv_unsigned sp) -> mem_inv ctusegs m0 -> ssp_cells m0 canary -> frm0 fc ->
  rw_cells ctusegs m0 out (bio_null_cells NULL_METHOD pv nw) -> 0 <= nw < 2^64 ->
  evt ctusegs (hexstring_post vra sp gp tp v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 F lo out pv canary m0)
    (MS (mkR vra sp gp tp t0 t1 t2 v8 v9 (Z_to_bv 64 out) (Z_to_bv 64 20) a2 a3 (Z_to_bv 64 0) a5 a6 a7
             v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 t3 t4 t5 t6)
        F (Z_to_bv 64 BIO_HEX_STRING) fc None m0 (seg_rom ctusegs)).
Proof using GLO LO OB SP63.
  clear HLEN LEN S0 SLO SEP SP16 OAL. intros until nw. intros ST MI [SSP1 SSP2] FRM HB NW.
  unfold got_ssp, ssp_guard in SSP1, SSP2. unfold bio_null_cells, bio_cells, NULL_METHOD, MallocRep.wz in HB.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (SEPB : out + 128 <= lo \/ bv_unsigned sp <= out) by lia.
  assert (SEPG : 3271976 + 8 <= lo \/ bv_unsigned sp <= 3271976) by lia.
  assert (SEPC : 3486312 + 8 <= lo \/ bv_unsigned sp <= 3486312) by lia.
  unfold BIO_HEX_STRING.
  pose proof (munch_refl W0 m0) as MU. unfold W0 in MU. pose proof (wmono_refl ctusegs m0) as WM.
  carve_frame 128%nat ST. zstep. do 13 zstep. zstep. zstep.
  zstep. if_cases K; zify_cond K; [| exfalso; rewrite ?unsigned_lit in K by lia; lia]. try clear K.
  zstep. do 13 zstep. zstep.
  release_frame FR ST (bv_unsigned sp). zstep.
  name_mem m1. apply evt_done. unfold hexstring_post.
  do 14 eexists. exists F, fc, m1, nw. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact FRM|]. split; [intros k Hk; reflexivity|].
  split; [exact ST|]. split; [split; eassumption|]. split; [unfold bio_null_cells, bio_cells, NULL_METHOD, MallocRep.wz; eassumption| exact NW].
Qed.

(* [comment removed for export] *)
Lemma hx_main : forall (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word) (fc : bv 32) (nw : Z),
  stk ctusegs m0 lo (bv_unsigned sp) -> mem_inv ctusegs m0 -> ssp_cells m0 canary -> frm0 fc ->
  rw_cells ctusegs m0 out (bio_null_cells NULL_METHOD pv nw) -> 0 <= nw < 2^64 -> null_meth_cells m0 -> bytes_at ctusegs m0 S bs ->
  evt ctusegs (hexstring_post vra sp gp tp v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 F lo out pv canary m0)
    (MS (mkR vra sp gp tp t0 t1 t2 v8 v9 (Z_to_bv 64 out) (Z_to_bv 64 20) (Z_to_bv 64 16) (Z_to_bv 64 S) (Z_to_bv 64 len) a5 a6 a7
             v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 t3 t4 t5 t6)
        F (Z_to_bv 64 BIO_HEX_STRING) fc None m0 (seg_rom ctusegs)).
Proof using GLO HLEN LEN LO OAL OB S0 SEP SLO SP16 SP63.
  intros until nw. intros ST MI [SSP1 SSP2] FRM HB NW [NMa NMb] HS.
  unfold got_ssp, ssp_guard in SSP1, SSP2. unfold NULL_METHOD in NMa, NMb. unfold bio_null_cells, bio_cells, NULL_METHOD, MallocRep.wz in HB.
  facts. unfold BIO_HEX_STRING.
  pose proof (munch_refl W0 m0) as MU. unfold W0 in MU. pose proof (wmono_refl ctusegs m0) as WM.
  assert (HFC : hx_F F) by (intros k Hk; reflexivity).
  (* [comment removed for export] *)
  carve_frame 128%nat ST. zstep. do 13 zstep. zstep. zstep.
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. try clear K.
  (* [comment removed for export] *)
  zstep. zstep. zstep. rewrite (swrap32_small (len + -1)) by lia.
  name_mem m1.
  (* [comment removed for export] *)
  zstep. if_cases K; zify_cond K.
  - (* [comment removed for export] *)
    split24 FRL FRH.
    lazymatch type of FRL with rw_cells _ _ _ ?clo =>
    jump (eapply (hx_last _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 nw clo));
      [ | split; [exact NW| unfold bio_null_cells, bio_cells, NULL_METHOD, MallocRep.wz; exact HB]| exact FRM| exact HFC] end.
    split; [exact MI|]. split; [exact ST|]. split; [split; [exact SSP1| exact SSP2]|]. split; [split; [exact NMa| exact NMb]|].
    split; [exact HS|]. split; [exact MU|]. split; [exact WM|]. split; [exact FRH|]. split; [exact FRL| reflexivity].
  - (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    zstep. (* [comment removed for export] *)
    do 9 zstep.
    zstep. (* [comment removed for export] *)
    name_mem m2.
    split24 FRL FRH.
    replace (Z.land (len + -1) 4294967295) with (len + -1)
      by (change 4294967295 with (Z.ones 32); rewrite Z.land_ones by lia; rewrite Z.mod_small by lia; lia).
    replace (Z.b2z (0 <? S)) with 1 by (rewrite (proj2 (Z.ltb_lt 0 S)) by lia; reflexivity).
    lazymatch type of FRL with rw_cells _ _ _ (CB 8 ?pad :: _) =>
    jump (eapply (hx_loop (Z.to_nat (len - 1)) 0 0 nw _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 pad));
      [lia| lia| reflexivity| | split; [exact NW| unfold bio_null_cells, bio_cells, NULL_METHOD, MallocRep.wz; exact HB]| exact FRM| exact HFC] end.
    split; [exact MI|]. split; [exact ST|]. split; [split; [exact SSP1| exact SSP2]|]. split; [split; [exact NMa| exact NMb]|].
    split; [exact HS|]. split; [exact MU|]. split; [exact WM|]. split; [exact FRH|]. split; [exact FRL| reflexivity].
Qed.

End HX.

(* [comment removed for export] *)
Theorem BIO_hex_string_null_spec {CE__ : Ceiling} {RN__ : RunRnd} :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (out pv nw S len lo : Z) (canary : word) (bs : list byte),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - HX_STACK -> bv_unsigned sp < 2^63 -> bv_unsigned sp mod 16 = 0 ->
  ssp_cells m canary -> frm0 fc ->
  rw_cells ctusegs m out (bio_null_cells NULL_METHOD pv nw) -> obj_range out BIO_SIZE lo -> out mod 8 = 0 -> 0 <= nw < 2^64 -> null_meth_cells m ->
  bytes_at ctusegs m S bs -> Z.of_nat (length bs) = len -> 0 <= len < 2^31 ->
  (0 < len -> 0 < S /\ S + len <= lo /\ (S + len <= out \/ out + 128 <= S)) ->
  a0 = Z_to_bv 64 out -> a1 = Z_to_bv 64 20 -> a2 = Z_to_bv 64 16 -> a3 = Z_to_bv 64 S -> a4 = Z_to_bv 64 len ->
  evt ctusegs (hexstring_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo out pv canary m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BIO_HEX_STRING) fc None m (seg_rom ctusegs)).
Proof.
  intros until bs. intros ST MI GLO LO SP63 SP16 SSP FRM HB OBR OAL NW NM HS LEN HLEN SFACTS -> -> -> -> ->.
  unfold HX_STACK, GLOBALS_TOP in *. pose proof OBR as OB. unfold obj_range, BIO_SIZE, GLOBALS_TOP in OB.
  destruct (Z.eq_dec len 0) as [L0|L0].
  - (* [comment removed for export] *)
    rewrite L0. eapply hx_zero; try eassumption; lia.
  - destruct (SFACTS ltac:(lia)) as (S0 & SLO & SEP).
    eapply hx_main; try eassumption; lia.
Qed.
