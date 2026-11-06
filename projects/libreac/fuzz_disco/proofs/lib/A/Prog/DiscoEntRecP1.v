(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 453 of its 485 lines of code are new or changed and 37 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntHdr.v, with its module names and numbers changed; 348 of its 493 lines of code are new or changed and 340 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame YC81.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC1g YC1h YC4b YC45 YC1i DiscoACjr ACj1 DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv slot_frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoEntSeatStmt DiscoEntSeat DiscoEntBodyStmt DiscoEntBody DiscoEntShChk DiscoEntRecLib DiscoEntRecCut.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require FP.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma rl_val_mem_mod : forall (m : word -> option byte) a v, val_mem SEGS m a 8 (v mod 2 ^ 64) -> val_mem SEGS m a 8 v.
Proof.
intros m a v H k Hk. rewrite (H k Hk). f_equal. f_equal.
first [unfold YO0f.le_byte | unfold YG0f.le_byte]. change (8 * Z.of_nat 8) with 64. rewrite Zmod_mod. reflexivity.
Qed.
Lemma rl_bv_mod : forall x, Z_to_bv 64 x = Z_to_bv 64 (x mod 2 ^ 64).
Proof.
intros x. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
rewrite Zmod_mod. reflexivity.
Qed.
Lemma rl_denot_sll8 : forall E q b, ew E q = Z_to_bv 64 b -> 0 <= b < 256 ->
  sv_denot E (SAlu ALU_SLL (SOff q 0) (SLit 8)) = Z_to_bv 64 (b * 256).
Proof.
intros E q b Hq Hb. rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw].
rewrite U_SLit, (U_atom E q b Hq) by lia. change (Z.land (zcanon 8) 63) with 8.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256. apply zcanon_id. unfold M64. lia.
Qed.
Lemma rl_nth_skipn : forall {A} (l : list A) (s k : nat) (d : A), nth k (skipn s l) d = nth (s + k) l d.
Proof.
intros A l. induction l as [|x l IH]; intros s k d.
- rewrite skipn_nil. destruct k, (s + _)%nat; reflexivity.
- destruct s as [|s]; [reflexivity|]. cbn [skipn Nat.add]. rewrite IH. reflexivity.
Qed.
Lemma rl_nth_map_u : forall (l : list byte) k,
  bv_unsigned (nth k l (Z_to_bv 8 0)) = nth k (map (fun b : byte => bv_unsigned b) l) 0.
Proof. induction l as [|x l IH]; intros [|k]; cbn [nth map]; try reflexivity. apply IH. Qed.
Lemma rec_want_rb : forall cx n, Z.of_nat (length (c_pl cx)) = c_n cx -> 0 <= n <= c_n cx ->
  rec_want (rest_of (c_pl cx) n) = rb cx n 0 + 256 * rb cx n 1.
Proof.
intros cx n Hl Hn. unfold rec_want, rdb, rest_of, rb. rewrite !rl_nth_skipn, !rl_nth_map_u.
replace (length (c_pl cx) - Z.to_nat n + 0)%nat with (Z.to_nat (c_n cx - n + 0)) by lia.
replace (length (c_pl cx) - Z.to_nat n + 1)%nat with (Z.to_nat (c_n cx - n + 1)) by lia.
reflexivity.
Qed.
Lemma rb_out : forall cx n j, Z.of_nat (length (c_pl cx)) = c_n cx -> c_n cx <= c_n cx - n + j -> rb cx n j = 0.
Proof. intros cx n j Hl Hj. unfold rb. apply nth_overflow. rewrite length_map. lia. Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis FFL : frame_flag_lawP SEGS B.

Definition rec_rp (cx : dcx) (n op lo hi : Z) (regs : bvmap 5 word) : Prop :=
  d_rL B cx regs /\ getr regs 11 = w64 lo /\ getr regs 12 = w64 hi /\
  getr regs 16 = w64 (d_cur cx (rec_rem n)) /\ getr regs 23 = w64 (rec_rem n) /\
  getr regs 27 = w64 op /\ getr regs 19 = w64 (op mod 4) /\
  getr regs 14 = w64 (d_obj cx OT) /\ getr regs 22 = w64 (d_obj cx OS) /\ getr regs 26 = w64 (d_obj cx OOUR).

Lemma rec_c1_intro : forall cx h i n now op lo hi W c,
  d_at B MT XM_LIB RLO RHI tfib_K cx REC_J (EV_HEAD i) (ACC_HEAD MT i)
    (fun regs ly3 S3 W3 mem3 md3 =>
      (0 <= i < MAX_OPS /\ 0 <= n /\ 0 <= now < 2 ^ 64 /\ 0 <= op < 256 /\ op mod 4 <> 3 /\
       0 <= lo < 256 /\ 0 <= hi < 65536 /\ hi mod 256 = 0 /\ lo + hi = rec_want (rest_of (c_pl cx) n)) /\
      rec_rp cx n op lo hi regs /\
      val_mem SEGS (rd W3 mem3) (d_A cx + 392) 8 (if op <? 128 then op else op - 256) /\
      d_sp0 cx i now W3 mem3 /\ d_body B cx h n [] dsh_loop ly3 S3 W3 mem3) W c ->
  rec_c1 B MT XM_LIB RLO RHI tfib_K cx h i n now op W c.
Proof.
intros cx h i n now op lo hi W c H. unfold rec_c1. eapply rl_d_at_mono; [exact H|].
intros regs ly S W' mem md ((Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9) & (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10) & V & SP & BD).
refine (conj Q1 (conj Q2 (conj Q3 (conj Q4 (conj Q5 _))))). exists lo, hi.
exact (conj Q6 (conj Q7 (conj Q8 (conj Q9 (conj R1 (conj R2 (conj R3 (conj R4 (conj R5 (conj R6 (conj R7 (conj R8
  (conj R9 (conj R10 (conj V (conj SP BD)))))))))))))))).
Qed.

Lemma rec_land : forall (fq : YK11.FPState) (cx : dcx) (h i n now sv : Z) ly3 S3 (W3 : world SEGS) mem3 md' k acc
  (E : env) (ss : sstate) (ms : machine_state) (P : bvmap 5 word -> Prop) (Q : Prop),
  Q -> lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  d_base B MT XM_LIB RLO RHI tfib_K cx ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W3 (ms_mem ms) md' k ->
  frames S3 = [(DFRAME_CLASS, c_fpos cx)] ->
  0 <= k <= EV_HEAD i -> st_nev S3 <= st_nev (c_S cx) + EV_HEAD i ->
  mo_le MT (c_S cx) S3 acc -> acc <= ACC_HEAD MT i ->
  d_E cx E -> ew E AT_FL = Z_to_bv 64 (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)) ->
  st_ok_pi (fx := fq) SEGS VAL E ss (restrict (w_H W3) ms) -> ss_resv ss = None -> ss_pc ss = REC_J ->
  d_land_chk dsh_loop (ss_mem ss) = true ->
  d_body B cx h n [] dsh_loop ly3 S3 W3 mem3 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx + 392 <= a < d_A cx + 400) ->
     aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) mem3 a) ->
  (forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem ms) a) ->
  d_sp0 cx i now W3 mem3 ->
  val_mem SEGS (rd W3 (ms_mem ms)) (d_A cx + 392) 8 sv ->
  P (ms_regs ms) ->
  d_at B MT XM_LIB RLO RHI tfib_K cx REC_J (EV_HEAD i) (ACC_HEAD MT i)
    (fun regs ly3' S3' W3' mem3' md3' =>
       Q /\ P regs /\ val_mem SEGS (rd W3' mem3') (d_A cx + 392) 8 sv /\
       d_sp0 cx i now W3' mem3' /\ d_body B cx h n [] dsh_loop ly3' S3' W3' mem3')
    W3 (mkCfg ms md').
Proof.
intros fq cx h i n now sv ly3 S3 W3 mem3 md' k acc E ss ms P Q
  HQ Hfrm HB HJ HFR Hk Hev Hmo Hacc HE HFL HS Hrv Hpc Hchk HBD MEQ MPR Hsp0 V392 HP.
pose proof HB as ((HPRE & _) & _). pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR. unfold YG0f.ASAN_CEIL in CR.
assert (HS608 : 608 <= d_S cx) by (unfold d_S, LLVMF_STK in *; lia).
destruct (rl_A_range cx HS608) as [HAr _].
pose proof HBD as (T & G & Lk & H & HFRM & _ & _ & _ & HINP & _).
pose proof HFRM as (E0 & _ & _ & _ & V216 & V152).
pose proof HINP as (Hnr & _).
assert (V216' : val_mem SEGS (rd W3 (ms_mem ms)) (d_A cx + 216) 8 h).
{ apply (rl_val_mem_keep (w_H W3) mem3 (ms_mem ms) (d_A cx + 216) 8 h V216). intros j Hj. apply MEQ; [|lia].
  unfold d_S, LLVMF_STK in *. lia. }
assert (V152' : val_mem SEGS (rd W3 (ms_mem ms)) (d_A cx + 152) 8 (h + 440)).
{ apply (rl_val_mem_keep (w_H W3) mem3 (ms_mem ms) (d_A cx + 152) 8 (h + 440) V152). intros j Hj. apply MEQ; [|lia].
  unfold d_S, LLVMF_STK in *. lia. }
destruct (d_land B MT XM_LIB RLO RHI tfib_K LAWS FFL fq cx h dsh_loop ly3 S3 W3 md' k E ss ms (conj HB (conj HJ HFR)) HE HFL HS Hchk V216' V152')
  as [HFRM' HSHD'].
assert (HBD' : d_body B cx h n [] dsh_loop ly3 S3 W3 (ms_mem ms)).
{ apply (d_body_keep B cx h n n dsh_loop ly3 S3 W3 mem3 (ms_mem ms) (d_A cx + 392) (d_A cx + 400) HBD).
  - unfold d_S, LLVMF_STK in *. lia.
  - lia.
  - exact MEQ.
  - intros a _ Ha. exact (MPR a Ha).
  - exact HFRM'.
  - exact HSHD'.
  - lia. }
assert (SP' : d_sp0 cx i now W3 (ms_mem ms)).
{ destruct Hsp0 as (S1 & S2). split.
  - apply (rl_val_mem_keep (w_H W3) mem3 (ms_mem ms) _ 8 _ S1). intros j Hj. apply MEQ; [unfold d_S, LLVMF_STK in *; lia | lia].
  - apply (rl_val_mem_keep (w_H W3) mem3 (ms_mem ms) _ 8 _ S2). intros j Hj. apply MEQ; [unfold d_S, LLVMF_STK in *; lia | lia]. }
pose proof (st_ok_pi_restrict_mkst (w_H W3) E ss ms HS Hrv) as Hms.
exists fq, ly3, S3, (ms_regs ms), (ms_mem ms), md', k, acc.
split; [unfold cfg_at; rewrite Hms at 1; rewrite Hpc; reflexivity|]. split; [exact Hfrm|].
split; [exact HB|]. split; [exact HJ|]. split; [exact HFR|]. split; [exact Hk|]. split; [exact Hev|].
split; [exact Hmo|]. split; [exact Hacc|].
split; [exact HQ|]. split; [exact HP|]. split; [exact V392|]. split; [exact SP'|]. exact HBD'.
Qed.

Ltac rew := cbn [ew havoc d_env AT_FL AT_X Nat.ltb Nat.leb Nat.sub Nat.add nth rec_vals].
Ltac rU := rew; repeat match goal with H : bv_unsigned (ew ?Ex ?q) = _ |- context [bv_unsigned (ew ?Ex ?q)] => rewrite H end.
Ltac rside := first [ rew; first [ reflexivity | assumption ] | lia | unfold d_cur, dsh_cell_addr, SHADOW_OFF in *; lia ].
Ltac rec_awr cx :=
  cbn [ss_mem];
  repeat first
    [ apply awr_ok_nil
    | apply awr_ok_cons_ro; [cbn; lia|]
    | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat (d_A cx - d_S cx));
      [ reflexivity | rU; unfold w64; rewrite ?unsigned_lit_small by lia; lia
      | cbn [YP09.r_wlo]; unfold LLVMF_STK, MFRAME in *; lia | cbn [YP09.r_whi]; unfold MFRAME in *; lia | ] ].
Ltac rdisj := apply all_disjoint_of_extents; unfold dsh_cell_region, rec_in_r, extent_of_region;
  cbn [ss_mem map YP09.r_base YP09.r_lo YP09.r_hi base_val zall_disjoint]; unfold zdisj; cbn [fst snd];
  rU; unfold w64; rewrite ?unsigned_lit_small by rside;
  unfold dsh_cell_addr, shadow_addr, SHADOW_OFF in *; unfold d_cur in *; repeat split; lia.
Ltac rdrop :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ec ?ss ?ms |- _ =>
    let L := eval vm_compute in (ss_mem ss) in
    lazymatch L with
    | YP09.mkRegion (Some ?q0) 0 1 0 0 _ :: ?rest =>
      lazymatch eval vm_compute in (Nat.leb 560 q0) with
      | true =>
        let HS2 := fresh "HS" in
        pose proof (st_ok_pi_submem Ec ss ms rest HS (submem_drop rest _ rest (submem_refl rest)) ltac:(vm_compute; reflexivity)) as HS2;
        clear HS; rename HS2 into HS; norm_ss HS
      | false => idtac
      end
    | _ => idtac
    end
  end.
Ltac rcell j rd q v cx n :=
  rdrop;
  lazymatch goal with HS : st_ok_pi _ _ _ _ _ |- _ =>
    let EQq := fresh "EQq" in let EQv := fresh "EQv" in
    add_atom HS q (Z_to_bv 64 (dsh_cell_addr (d_cur cx n + j))) EQq;
    add_atom HS v (Z_to_bv 64 (dsh_cell (c_p cx) (c_n cx) (d_cur cx n + j))) EQv; clear EQq
  end;
  lazymatch goal with
  | HS : st_ok_pi _ _ ?Ec ?ss (restrict (w_H ?W) ?ms) |- _ =>
    let R := fresh "R" in
    pose proof (st_ok_pi_restrict_reg (w_H W) Ec ss ms rd HS) as R;
    let e := eval vm_compute in (sr_get (ss_regs ss) rd) in change (sr_get (ss_regs ss) rd) with e in R;
    rewrite (dsh_cell_denot Ec 540 q j (d_cur cx n)) in R by rside
  end;
  lazymatch goal with
  | HS : st_ok_pi _ _ ?Ec ?ss (restrict (w_H ?W) ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    R : getr _ _ = _ |- _ =>
    let HS2 := fresh "HS" in
    unshelve epose proof (dsh_cell_seat Ec ss ms W rd q v (dsh_cell_addr (d_cur cx n + j))
      (dsh_cell (c_p cx) (c_n cx) (d_cur cx n + j)) HS _ (eq_sym R) _ _ _ _ _ _) as HS2;
    [ vm_compute; reflexivity
    | rew; reflexivity
    | unfold d_cur, dsh_cell_addr, SHADOW_OFF in *; lia
    | rew; reflexivity
    | pose proof (dsh_cell_range (c_p cx) (c_n cx) (d_cur cx n + j)); lia
    | let L := rnLAWS in let Bv := rnB in
      eapply (dsh_cell_val Bv L _ _ _ _ _ (c_p cx) (c_n cx) _ (proj1 HJ) ltac:(assumption)); unfold d_cur in *; lia
    | rdisj
    | clear HS R; rename HS2 into HS; norm_ss HS ]
  end.

Ltac rconv cx n :=
  lazymatch goal with
  | Hc : branch_taken BC_EQ (sv_denot ?Ex (SOff 534 0)) (sv_denot ?Ex (SLit 0)) = ?bb |- _ =>
      rewrite (rl_beq_atom Ex 534 n 0 ltac:(rew; reflexivity) ltac:(lia) ltac:(lia)) in Hc;
      lazymatch bb with true => apply Z.eqb_eq in Hc | false => apply Z.eqb_neq in Hc end;
      first [ exfalso; lia | clear Hc ]
  | Hc : branch_taken BC_NE (sv_denot ?Ex (SOff 534 0)) (sv_denot ?Ex (SLit 1)) = ?bb |- _ =>
      rewrite (rl_bne_atom Ex 534 n 1 ltac:(rew; reflexivity) ltac:(lia) ltac:(lia)) in Hc;
      lazymatch bb with true => apply negb_true_iff, Z.eqb_neq in Hc | false => apply negb_false_iff, Z.eqb_eq in Hc end;
      first [ exfalso; lia | clear Hc ]
  | Hc : branch_taken BC_EQ (sv_denot ?Ex (SExt true 8 (SOff ?v 0))) (sv_denot ?Ex (SLit 0)) = ?bb,
    EQ : ew ?Ex ?v = Z_to_bv 64 ?sv |- _ =>
      lazymatch sv with dsh_cell ?P ?N ?X => pose proof (dsh_cell_range P N X) end;
      rewrite (rl_beq_cell Ex v sv EQ ltac:(lia)) in Hc;
      lazymatch bb with
      | true => apply Z.eqb_eq in Hc; let H := fresh "HZ" in rename Hc into H
      | false => apply Z.eqb_neq in Hc; let H := fresh "HNZ" in rename Hc into H
      end
  | Hc : branch_taken BC_GE (sv_denot ?Ex (SAlu ALU_AND (SOff 540 ?c) (SLit 7))) (sv_denot ?Ex (SExt true 8 (SOff ?v 0))) = ?bb,
    EQ : ew ?Ex ?v = Z_to_bv 64 ?sv |- _ =>
      lazymatch sv with dsh_cell ?P ?N ?X => pose proof (dsh_cell_range P N X) end;
      rewrite (rl_bge_cell Ex 540 c (d_cur cx n) v sv ltac:(rew; reflexivity) ltac:(unfold d_cur in *; lia) ltac:(lia)
        ltac:(unfold d_cur in *; lia) EQ ltac:(lia)) in Hc;
      lazymatch bb with
      | true => exfalso; apply negb_true_iff, Z.ltb_ge in Hc;
          lazymatch sv with dsh_cell ?P ?N ?X =>
            lazymatch goal with HNZ : dsh_cell P N X <> 0 |- _ =>
              pose proof (dsh_cell_lt P N X ltac:(assumption) ltac:(lia) ltac:(unfold d_cur in *; lia) HNZ); unfold d_cur in *; lia end end
      | false => clear Hc
      end
  end.
Ltac rwin :=
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
  let Hin := fresh "Hin" in let Ha := fresh "Ha" in
  intros b wlo whi a Hin Ha; vm_compute in Hin;
  repeat (destruct Hin as [Hin|Hin];
    [ injection Hin; intros; subst; cbn [base_val] in Ha; first [ lia | revert Ha; rU; intros Ha; lia ] | ]);
  destruct Hin.
Ltac rupd :=
  lazymatch goal with
  | HFr : frame_of ?Eo ?rs (mrestrict ?Hh ?m1) (mrestrict _ ?m2),
    MEQ : forall a, _ -> ~ (?lo <= a < ?hi) -> aview _ _ ?m1 a = aview _ _ ?m0 a |- _ =>
    let MEQ2 := fresh "MEQ" in
    pose proof (rl_meq_frame Eo rs Hh m0 m1 m2 lo hi HFr ltac:(rwin) MEQ) as MEQ2; clear MEQ; rename MEQ2 into MEQ
  end;
  lazymatch goal with
  | HG : mem_grows (mrestrict ?Hh ?m1) (mrestrict _ ?m2), MPR : forall a, apresent _ ?m0 a -> apresent _ ?m1 a |- _ =>
    let MPR2 := fresh "MPR" in pose proof (rl_pres_grow Hh m0 m1 m2 HG MPR) as MPR2; clear MPR; rename MPR2 into MPR
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac rrun RUNTOP cx :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict (w_H _) _), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    paj_run_to_shc RUNTOP HS HJ 3168; [ rec_awr cx | rupd ] end.
Ltac rbr RUNP BR := lazymatch goal with HS : st_ok_pi _ _ _ _ _ |- _ => psrr_branch_pi RUNP BR HS end.
Ltac rstep RUNTOP RUNP BR cx n :=
  rrun RUNTOP cx;
  lazymatch goal with HS : st_ok_pi _ _ _ ?ss _ |- _ =>
    let pc := eval vm_compute in (ss_pc ss) in
    lazymatch pc with
    | 3168 => idtac
    | 2424 => rcell 0 (10%bv : bv 5) 560%nat 561%nat cx n; rstep RUNTOP RUNP BR cx n
    | 3140 => rcell 1 (12%bv : bv 5) 562%nat 563%nat cx n; rstep RUNTOP RUNP BR cx n
    | _ => rbr RUNP BR; rconv cx n; rstep RUNTOP RUNP BR cx n
    end
  end.


Ltac rhdE := lazymatch goal with HE : d_E ?cx ?E |- d_E ?cx ?Ec =>
  apply (rl_d_E_agree cx E Ec HE); let k0 := fresh "k0" in let Hk0 := fresh "Hk0" in intros k0 Hk0;
  repeat (rewrite ew_havoc_old by (unfold AT_FL in *; lia)); unfold d_env; apply ew_havoc_old; unfold AT_FL; lia end.
Ltac rsv cx n :=
  lazymatch goal with
  | |- sv_denot _ (SLit _) = _ => reflexivity
  | |- sv_denot _ (SOff 516 _) = _ => cbn [sv_denot]; rU; unfold w64, d_obj, dobj_off; reflexivity
  | |- sv_denot _ (SOff ?q 0) = _ => rewrite sv_denot_SOff0; rew; first [ reflexivity | assumption ]
  | |- sv_denot _ (SOff ?q ?c) = _ => rewrite denot_lit_U; unfold w64; f_equal; rewrite U_SOff; rew; unfold w64;
      rewrite unsigned_lit_small by (unfold d_cur in *; lia);
      rewrite zcanon_id by (unfold M64, d_cur, rec_rem, rec_take in *; lia);
      unfold d_cur, rec_rem, rec_take in *; lia
  | |- sv_denot ?Ex (SAlu ALU_SLL (SOff 552 0) (SLit 8)) = _ =>
      rewrite (rl_denot_sll8 Ex 552 (rb cx n 1) ltac:(rew; reflexivity) (rb_range cx n 1)); reflexivity
  end.
Ltac rreg cx n :=
  lazymatch goal with
  | HS : st_ok_pi _ _ ?Ec ?ss (restrict (w_H ?W) ?ms) |- _ =>
    lazymatch goal with
    | |- YG0d.spZ _ = _ =>
      unfold YG0d.spZ;
      let R := fresh "R" in pose proof (st_ok_pi_restrict_reg (w_H W) Ec ss ms 2%bv HS) as R;
      let e := eval vm_compute in (sr_get (ss_regs ss) 2%bv) in change (sr_get (ss_regs ss) 2%bv) with e in R;
      rewrite R, sv_denot_SOff0; rU; reflexivity
    | |- getr _ ?r = _ =>
      let R := fresh "R" in pose proof (st_ok_pi_restrict_reg (w_H W) Ec ss ms r HS) as R;
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in R;
      rewrite R; clear R; rsv cx n
    end
  end.
Ltac rv392 cx :=
  apply rl_val_mem_mod;
  lazymatch goal with HS : st_ok_pi _ _ ?Ec ?ss ?msr |- _ =>
    let rs := eval vm_compute in (ss_mem ss) in
    let i0 := idx_of_base rs 60%nat in let i0 := eval vm_compute in i0 in
    let r := eval vm_compute in (nth i0 rs got_regionP) in
    let RA := fresh "RA" in
    pose proof (st_ok_pi_region_nth Ec ss msr i0 r HS ltac:(vm_compute; reflexivity)) as RA; cbn [ms_mem restrict] in RA;
    refine (DiscoACjr.field_of_region Ec _ 60 (d_A cx) _ _ _ _ _ 392 8 (SOff 541 0) _ RA _ _ _ _ _);
    [ rU; reflexivity
    | cbn [In]; repeat (first [left; reflexivity | right])
    | rewrite sv_denot_SOff0; rew; unfold w64; apply rl_bv_mod
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply Z.mod_pos_bound; lia
    | cbn; lia ]
  end.
Ltac rland_obl cx n :=
  lazymatch goal with
  | |- d_E _ _ => rhdE
  | |- ew _ AT_FL = _ => rew; reflexivity
  | |- d_land_chk _ _ = true => vm_compute; reflexivity
  | |- val_mem _ _ _ 8 _ => rv392 cx
  | |- rec_rp _ _ _ _ _ _ => unfold rec_rp, d_rL; repeat split; rreg cx n
  | |- _ => idtac
  end.


Ltac rlandX fq cx h i n now op ly3 S3 W mem3 acc Hbase Hfrs Hk Hnev Hmo Hacc Hbody Hsp0 LO HI :=
  lazymatch goal with
  | HS : st_ok_pi _ _ ?Ec ?ss (restrict (w_H _) ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?md _,
    MEQ : forall a, _ -> ~ (_ <= a < _) -> aview _ _ _ a = aview _ _ _ a,
    MPR : forall a, apresent _ _ a -> apresent _ _ a |- _ =>
    apply SRr_ret; apply (rec_c1_intro cx h i n now op LO HI);
    refine (rec_land fq cx h i n now (if op <? 128 then op else op - 256) ly3 S3 W mem3 md _ acc Ec ss ms
      (rec_rp cx n op LO HI) _ _ ltac:(assumption) Hbase HJ Hfrs Hk Hnev Hmo Hacc _ _ HS eq_refl eq_refl _ Hbody MEQ MPR Hsp0 _ _)
  end.

Ltac rprep cx h i n now op regs ly3 S3 W mem3 md3 k :=
  lazymatch goal with
  | Hbody : d_body _ cx h n [] dsh_loop ly3 S3 W mem3, Hbase : d_base _ _ _ _ _ _ cx,
    HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, Hfrs : frames S3 = _ |- _ =>
  pose proof Hbody as (T & G & Lk & H & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoff & Hgeo & Hstk & Hwr);
  pose proof Hframe as (E & HE & HRG & HFL & H216 & H152);
  assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]);
  pose proof Hinput as (Hnr & HG & HOIp);
  pose proof Hbase as ((HPRE & Hra & Hp & Hn0' & Hpn & Hlen & Hgarr0 & _) & _);
  pose proof Hblocks as (Hperm & _ & _ & _);
  pose proof Hgeo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8);
  change (fs_frame_bytes DFRAME_CLASS) with 4096 in G2;
  pose proof HE as (EE & E32 & HEI0 & E60 & E516 & E529); unfold AT_A, AT_F, AT_SH in E60, E516, E529;
  pose proof HPRE as (HAR0 & _ & _ & Hgp0 & Htp0 & Hstkw & _);
  pose proof Hstkw as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _);
  pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR; unfold YG0f.ASAN_CEIL in CR;
  assert (HS608 : 608 <= d_S cx) by (unfold d_S, LLVMF_STK in *; lia);
  destruct (rl_A_range cx HS608) as [HAr HA32];
  pose proof (pa_obj_img 1 ltac:(unfold disco_nobj; lia)) as Ho1; pose proof (pa_obj_img 66 ltac:(unfold disco_nobj; lia)) as Ho66;
  pose proof (pa_val_range (A_OBJ 1)) as RV1; pose proof (pa_val_range (A_OBJ 66)) as RV66;
  assert (EO1 : ew E 242 = Z_to_bv 64 (VAL (A_OBJ 1))) by (apply (img_env_atomP E 242%nat HEI0); unfold A_TEXT, A_LIM; lia);
  assert (EO66 : ew E 307 = Z_to_bv 64 (VAL (A_OBJ 66))) by (apply (img_env_atomP E 307%nat HEI0); unfold A_TEXT, A_LIM; lia);
  assert (E2v : ew E 2 = Z_to_bv 64 (d_S cx)) by (rewrite (EE 2%nat 2%bv eq_refl); unfold d_S, YG0d.spZ; symmetry; apply Z_to_bv_bv_unsigned);
  assert (E3 : ew E 3 = w64 (as_gp B)) by (rewrite (EE 3%nat 3%bv eq_refl); exact Hgp0);
  assert (E4 : ew E 4 = w64 (as_tp B)) by (rewrite (EE 4%nat 4%bv eq_refl); exact Htp0);
  assert (UA : bv_unsigned (ew E 60) = d_A cx) by (rewrite E60; apply unsigned_lit_small; unfold d_S, LLVMF_STK in *; lia);
  assert (U2 : bv_unsigned (ew E 2) = d_S cx) by (rewrite E2v; apply unsigned_lit_small; unfold d_S, LLVMF_STK in *; lia);
  assert (UFB : bv_unsigned (ew E 516) = d_FB cx) by (rewrite E516; apply unsigned_lit_small; lia);
  assert (USH : bv_unsigned (ew E 529) = shadow_addr (d_FB cx))
    by (rewrite E529; apply unsigned_lit_small; unfold shadow_addr, SHADOW_OFF;
        pose proof (Z.div_pos (d_FB cx) 8 ltac:(lia)); pose proof (Z.div_le_upper_bound (d_FB cx) 8 (d_FB cx) ltac:(lia) ltac:(lia)); lia);
  assert (UO1 : bv_unsigned (ew E 242) = VAL (A_OBJ 1)) by (rewrite EO1; apply unsigned_lit_small; lia);
  assert (UO66 : bv_unsigned (ew E 307) = VAL (A_OBJ 66)) by (rewrite EO66; apply unsigned_lit_small; lia);
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, off_img, IMG_LO, IMG_TOP in Ho1, Ho66, HOIp;
  destruct Ho1 as (Ho1a & Ho1b); destruct Ho66 as (Ho66a & Ho66b);
  destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS _ _ _ _ _ _ _ HC)
    as (HSmod & HSlo & HShi & HFB1 & HFB2 & HFBapp & HFBimg & HFBmod & HFpres & HSHpres & HWpres & HAR3 & Hin3 & EFB3 & EFL3);
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, off_img, IMG_LO, IMG_TOP in HFBapp, HFBimg;
  unfold LLVMF_STK in HSlo;
  assert (MEQ : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx + 392 <= a < d_A cx + 400) ->
     aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) mem3 a) by (intros; reflexivity);
  assert (MPR : forall a, apresent (w_H W) mem3 a -> apresent (w_H W) mem3 a) by (intros a0 Ha0; exact Ha0)
  end.

Lemma rec_p1_zero : forall (cx : dcx) (h i n now op : Z) (W : world SEGS) (c : config),
  rec_in B MT XM_LIB RLO RHI tfib_K cx h i n now op W c -> n = 0 ->
  SRr SEGS W c (rec_c1 B MT XM_LIB RLO RHI tfib_K cx h i n now op).
Proof.
intros cx h i n now op W c Hin Hn0. subst n.
destruct Hin as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hfrm & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  Hi & Hn & Hnow & Hop & Hop4 & HrD & Hsp0 & Hbody).
rprep cx h i 0 now op regs ly3 S3 W mem3 md3 k.
assert (Rcur : 0 <= d_cur cx 0 < 2 ^ 64).
{ unfold d_cur. destruct Hpn as [[HN HP] | [HN _]].
  - rewrite HN, HP. unfold A_EMPTY. lia.
  - destruct (G8 ltac:(lia)) as (GP0 & GPN & _). lia. }
pose proof (rec_seat B MT XM_LIB RLO RHI tfib_K LAWS TL fq cx i 0 now op ly3 S3 W regs mem3 md3 k E 0 HC HE HRG HFL HrD
  ltac:(lia) ltac:(lia) ltac:(unfold MAX_OPS in *; lia) Hnow Hop ltac:(lia) ltac:(intros Hm; exfalso; lia) Rcur) as HS.
unfold cfg_at. change (w64 (BASE + REC_OFF)) with (Z_to_bv 64 (BASE + REC_OFF)).
pose (RUNTOP := SRr_run_to_pi_AJ (fx := fq) B LAWS).
pose (RUNP := SRr_run_pi_AJ (fx := fq) B LAWS).
pose (BR := paj_branch (fx := fq) (PI := PI)).
assert (HEI : img_env VAL A_LIM (d_env cx E (rec_vals cx i 0 now op regs))) by (apply img_env_havoc_hi; [exact HEI0 | unfold AT_FL, A_LIM; lia]).
unfold rec_ss in HS. norm_ss HS.
rstep RUNTOP RUNP BR cx 0.
all: rlandX fq cx h i 0 now op ly3 S3 W mem3 acc Hbase Hfrs Hk Hnev Hmo Hacc Hbody Hsp0 0 0.
all: rland_obl cx 0.
all: rewrite (rec_want_rb cx 0 G6 ltac:(lia)), (rb_out cx 0 0 G6 ltac:(lia)), (rb_out cx 0 1 G6 ltac:(lia));
  repeat split; lia.
Qed.

Lemma rec_p1_pos : forall (cx : dcx) (h i n now op : Z) (W : world SEGS) (c : config),
  rec_in B MT XM_LIB RLO RHI tfib_K cx h i n now op W c -> n <> 0 ->
  SRr SEGS W c (rec_c1 B MT XM_LIB RLO RHI tfib_K cx h i n now op).
Proof.
intros cx h i n now op W c Hin Hn00.
destruct Hin as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hfrm & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  Hi & Hn & Hnow & Hop & Hop4 & HrD & Hsp0 & Hbody).
rprep cx h i n now op regs ly3 S3 W mem3 md3 k.
assert (HN8 : 8 <= c_n cx) by lia.
assert (HinB0 : In (c_p cx, c_n cx) (ablocks B (c_ly cx) (c_S cx))) by (destruct Hpn as [[? _]|[_ ?]]; [lia | assumption]).
assert (HN26 : c_n cx < 2 ^ 26) by (destruct Hpn as [[? _]|[? _]]; lia).
assert (HinB : In (c_p cx, c_n cx) (ablocks B ly3 S3)) by
  (apply (Permutation_in _ (Permutation_sym Hperm)); cbn [app]; right; exact HinB0).
specialize (G8 ltac:(lia)). destruct G8 as (GP0 & GPN & GPF & GPH).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 HinB) as (Hp16 & Hp4k & Hpc & Hpapp & _).
assert (Hp8 : c_p cx mod 8 = 0) by (pose proof (Z.div_mod (c_p cx) 16 ltac:(lia)); pose proof (Z.div_mod (c_p cx) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (c_p cx) 8 ltac:(lia)); lia).
assert (Hrq : req_size (c_n cx) = c_n cx) by (unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia).
rewrite Hrq in Hpc, Hpapp.
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR3 HinB Hin3) as HBF.
rewrite EFB3 in HBF. unfold zdisjoint in HBF. cbn [fst snd] in HBF. rewrite Hrq in HBF.
change (fs_frame_bytes DFRAME_CLASS) with 4096 in HBF.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, off_img, IMG_LO, IMG_TOP in Hpapp.
unfold cfg_at. change (w64 (BASE + REC_OFF)) with (Z_to_bv 64 (BASE + REC_OFF)).
pose (RUNTOP := SRr_run_to_pi_AJ (fx := fq) B LAWS).
pose (RUNP := SRr_run_pi_AJ (fx := fq) B LAWS).
pose (BR := paj_branch (fx := fq) (PI := PI)).
assert (Hm : n = 1 \/ 2 <= n) by lia.
destruct Hm as [Hn1 | Hn2].
- subst n.
  pose proof (rec_seat B MT XM_LIB RLO RHI tfib_K LAWS TL fq cx i 1 now op ly3 S3 W regs mem3 md3 k E 1 HC HE HRG HFL HrD
    ltac:(lia) ltac:(lia) ltac:(unfold MAX_OPS in *; lia) Hnow Hop ltac:(lia)
    ltac:(intros _; refine (conj HinB (conj _ (conj HN26 (conj HG (conj (HOIp ltac:(lia)) _))))); lia)
    ltac:(unfold d_cur; lia)) as HS.
  assert (HEI : img_env VAL A_LIM (d_env cx E (rec_vals cx i 1 now op regs))) by (apply img_env_havoc_hi; [exact HEI0 | unfold AT_FL, A_LIM; lia]).
  unfold rec_ss in HS. norm_ss HS.
  rstep RUNTOP RUNP BR cx 1.
  all: rlandX fq cx h i 1 now op ly3 S3 W mem3 acc Hbase Hfrs Hk Hnev Hmo Hacc Hbody Hsp0 (rb cx 1 0) 0.
  all: rland_obl cx 1.
  all: pose proof (rb_range cx 1 0); rewrite (rec_want_rb cx 1 G6 ltac:(lia)), (rb_out cx 1 1 G6 ltac:(lia));
    repeat split; lia.
- pose proof (rec_seat B MT XM_LIB RLO RHI tfib_K LAWS TL fq cx i n now op ly3 S3 W regs mem3 md3 k E 2 HC HE HRG HFL HrD
    ltac:(lia) ltac:(lia) ltac:(unfold MAX_OPS in *; lia) Hnow Hop Hn
    ltac:(intros _; refine (conj HinB (conj _ (conj HN26 (conj HG (conj (HOIp ltac:(lia)) _))))); lia)
    ltac:(unfold d_cur; lia)) as HS.
  assert (HEI : img_env VAL A_LIM (d_env cx E (rec_vals cx i n now op regs))) by (apply img_env_havoc_hi; [exact HEI0 | unfold AT_FL, A_LIM; lia]).
  unfold rec_ss in HS. norm_ss HS.
  rstep RUNTOP RUNP BR cx n.
  all: rlandX fq cx h i n now op ly3 S3 W mem3 acc Hbase Hfrs Hk Hnev Hmo Hacc Hbody Hsp0 (rb cx n 0) (rb cx n 1 * 256).
  all: rland_obl cx n.
  all: pose proof (rb_range cx n 0); pose proof (rb_range cx n 1); rewrite (rec_want_rb cx n G6 ltac:(lia));
    repeat split; lia.
Qed.

Theorem rec_p1 : rec_p1_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op W c Hin.
destruct (Z.eq_dec n 0) as [Hn0 | Hn0].
- exact (rec_p1_zero cx h i n now op W c Hin Hn0).
- exact (rec_p1_pos cx h i n now op W c Hin Hn0).
Qed.

Lemma rec_spec_of_parts : rec_p1_stmt B MT XM_LIB RLO RHI tfib_K -> rec_p2_stmt B MT XM_LIB RLO RHI tfib_K ->
  rec_spec B MT XM_LIB RLO RHI tfib_K.
Proof.
intros P1 P2 cx h i n now op W c Hin. eapply SRr_bind; [exact (P1 cx h i n now op W c Hin)|].
intros W2 c2 _ H2. exact (P2 cx h i n now op W2 c2 H2).
Qed.
Theorem rec_spec_of_p2 : rec_p2_stmt B MT XM_LIB RLO RHI tfib_K -> rec_spec B MT XM_LIB RLO RHI tfib_K.
Proof. exact (rec_spec_of_parts rec_p1). Qed.

End h.
End f.
End d.
