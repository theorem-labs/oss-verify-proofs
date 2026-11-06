(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 1088 of its 1116 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/chain_words.v, with its module paths, addresses and numbers changed; 2641 of its 2742 lines of code are new or changed and 1015 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/sup_host_setting.v, with its module paths, module names, addresses and numbers changed; 1538 of its 2663 lines of code are new or changed and 1617 lines of the source are left out. *)
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Arr Bytes ZBridge FP Image.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0 MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import printf_facts_c snprintf_c strlen_c strcat_c
  mix_call_c RecAns.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma hsu_pf_dec : forall v, -2^31 <= v < 2^31 -> pf_bytes (pf_dec v) = dec v.
Proof.
  intros c Hc. unfold pf_dec, dec. unfold pf_bytes.
  assert (P : 10 ^ Z.of_nat (S 9) = 10000000000) by reflexivity.
  destruct (Z.ltb_spec c 0) as [N|N].
  - cbn [map app]. f_equal. replace (Z.abs c) with (- c) by lia.
    exact (pf_digits_digits 9 11 (- c) [] ltac:(rewrite P; lia) ltac:(lia)).
  - cbn [app]. replace (Z.abs c) with c by lia.
    exact (pf_digits_digits 9 11 c [] ltac:(rewrite P; lia) ltac:(lia)).
Qed.

Definition HSU_FMT : list Z := [37; 100].
Definition HSU_PS : list pf_piece := [Pd].

Lemma hsu_parse : pf_parse HSU_FMT = Some HSU_PS.
Proof. reflexivity. Qed.

Lemma hsu_text : forall v, pf_text HSU_PS [AInt v] = Some (pf_dec v).
Proof. intros v. cbn. rewrite app_nil_r. reflexivity. Qed.

Lemma hsu_fmt_at : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x10828 (pf_bytes (HSU_FMT ++ [0])).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | lia | cbn; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma hsu_run0 :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 96 <= bv_unsigned sp -> 2 ^ 21 <= lo ->
  evt rsegs (fun ms' => exists m',
       ms' = MS (mkR (Z_to_bv 64 0x16850) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 a1
                     (Z_to_bv 64 6) a1 a2 a3 a4 a5 a6 a7 a2 a0 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x1612c) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp + -80, bv_unsigned sp)] m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' (bv_unsigned sp + -80)
            [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16810) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ST LO LO2.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp + -80, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 80%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 80%nat junk [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 16 step.
  apply evt_done.
  eexists. split; [reflexivity|].
  repeat (split; [eassumption|]). eassumption.
Qed.

Lemma hsu_mid1 :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x1685c) sp gp tp t0 t1 t2 a0 s1 a0 s3 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 0x16608) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16850) fc None m (seg_rom rsegs)).
Proof. intros. do 3 step. apply evt_done. reflexivity. Qed.

Lemma hsu_run1 : snprintf_contract ->
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo id : Z) (canary : word),
  -2^31 <= id < 2^31 ->
  stk rsegs m lo (bv_unsigned sp + 16) -> lo + SNPRINTF_K <= bv_unsigned sp -> 2 ^ 21 <= lo ->
  bv_unsigned sp + 16 < 2^63 ->
  frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m ->
  bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) -> bytes_at rsegs m GUARD (le8 canary) ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word)
                               (fc' : bv 32) (m' : word -> option byte) (slack : list byte),
       ms' = MS (mkR (Z_to_bv 64 0x16880) sp gp tp t0' t1' t2' s0 s1 s0 sp
                     a2' a3' a4' a5' a6' a7' (Z_to_bv 64 id) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F' (Z_to_bv 64 0x161c4) fc' None m' (seg_rom rsegs)
       /\ munch [(lo, bv_unsigned sp + 16)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
       /\ frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k)
       /\ length slack = (15 - length (dec id))%nat
       /\ bytes_at rsegs m' (bv_unsigned sp) (dec id ++ Z_to_bv 8 0 :: slack))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 id) s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x1685c) fc None m (seg_rom rsegs)).
Proof.
  intros SNP ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo id canary HV ST LO IE S63 FRM MI TM GG GW.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold SNPRINTF_K, IMG_END, GOT_GUARD, GUARD in *.
  pose proof (dec_length id HV) as DL.
  pose proof (hsu_pf_dec id HV) as PD.
  assert (TL : length (pf_dec id) = length (dec id)) by (rewrite <- PD; unfold pf_bytes; rewrite length_map; reflexivity).
  carve_frame 16%nat ST.
  replace (bv_unsigned sp + 0) with (bv_unsigned sp) in * by lia.
  do 6 step.
  pose proof (rw_cells_bound _ _ _ _ FR) as FRB. cbn [cells_size csize Nat.add] in FRB.
  assert (BJ : bytes_at rsegs m (bv_unsigned sp) junk).
  { destruct FR as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  pose proof (bytes_at_bound _ _ _ _ BJ) as BJL.
  eapply evt_cut.
  { eapply (SNP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo canary HSU_FMT HSU_PS
              [AInt id] (pf_dec id) junk).
    - rewrite unsigned_lit by lia. apply hsu_fmt_at. exact MI.
    - rewrite unsigned_lit by lia. unfold RO_LO. lia.
    - rewrite unsigned_lit by lia. unfold RO_END, HSU_FMT. cbn [length]. lia.
    - exact hsu_parse.
    - cbn [pf_args_ok pf_arg_ok]. split; [|exact I]. split; [exact HV | apply lit_mod32].
    - exact (hsu_text id).
    - rewrite !unsigned_lit by lia. exact FR.
    - rewrite unsigned_lit by lia. lia.
    - lia.
    - lia.
    - rewrite !unsigned_lit by lia. right. lia.
    - rewrite !unsigned_lit by lia. apply pf_img_free_hi. lia.
    - exact ST.
    - unfold SNPRINTF_K. lia.
    - unfold IMG_END. lia.
    - lia.
    - exact FRM.
    - exact MI.
    - exact TM.
    - exact GG.
    - exact GW. }
  intros ms' PO. unfold printf_post in PO.
  destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & Ft & fc' & m2
    & -> & MU2 & WM2 & MI2 & TM2 & FRM2 & FK & ST2 & BT).
  rewrite !unsigned_lit in MU2, BT by lia.
  change (Z.to_nat (16 - 1)) with 15%nat in BT, MU2.
  rewrite (firstn_all2 (n := 15%nat)) in MU2, BT by lia.
  replace (ret_pc (Z_to_bv 64 0x16874)) with (Z_to_bv 64 0x16874) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  assert (JL : length junk = 16%nat) by (destruct FR as [[[HJ _] _] _]; exact HJ).
  destruct (bytes_at_firstn_skipn _ _ _ _ (S (length (pf_dec id))) BJ) as [_ BJT].
  rewrite firstn_length_le in BJT by lia.
  assert (BJT2 : bytes_at rsegs m2 (bv_unsigned sp + Z.of_nat (S (length (pf_dec id))))
                   (skipn (S (length (pf_dec id))) junk)).
  { apply (bytes_at_transport rsegs _ m m2 _ _ BJT MU2). cbn [disjoint_from]. rewrite length_skipn.
    split; [lia | split; [lia | exact I]]. }
  assert (PB : pf_bytes (pf_dec id ++ [0]) = dec id ++ [Z_to_bv 8 0]).
  { unfold pf_bytes. rewrite map_app. change (map (Z_to_bv 8) (pf_dec id)) with (pf_bytes (pf_dec id)).
    rewrite PD. reflexivity. }
  rewrite PB in BT.
  assert (BUF : bytes_at rsegs m2 (bv_unsigned sp)
                  (dec id ++ Z_to_bv 8 0 :: skipn (S (length (pf_dec id))) junk)).
  { replace (dec id ++ Z_to_bv 8 0 :: skipn (S (length (pf_dec id))) junk) with
      ((dec id ++ [Z_to_bv 8 0]) ++ skipn (S (length (pf_dec id))) junk)
      by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app. split; [exact BT|]. rewrite length_app, <- TL. cbn [length].
    replace (Z.of_nat (length (pf_dec id) + 1)) with (Z.of_nat (S (length (pf_dec id)))) by lia. exact BJT2. }
  assert (MUc : munch [(lo, bv_unsigned sp + 16)] m m2).
  { eapply munch_weaken; [|exact MU2].
    unfold sub_fp. cbn [outside]. intros x [Hx _]. split; [lia | split; [lia | exact I]]. }
  clear BT BJT BJT2 BJ BJL FR.
  do 3 step.
  apply evt_done.
  do 16 eexists. exists (skipn (S (length (pf_dec id))) junk). split; [reflexivity|].
  split; [exact MUc|]. split; [exact WM2|]. split; [exact MI2|]. split; [exact FRM2|]. split; [exact FK|].
  split; [rewrite length_skipn, JL, TL; lia | exact BUF].
Qed.

Lemma hsu_eqb64 : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = Z.eqb x y.
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma hsu_ltu : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = Z.ltb x y.
Proof. intros x y Hx Hy. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma hsu_ltu_l : forall (x : word) y, 0 <= y < 2 ^ 64 -> bv_ltu x (Z_to_bv 64 y) = Z.ltb (bv_unsigned x) y.
Proof. intros x y Hy. unfold bv_ltu. rewrite unsigned_lit by lia. reflexivity. Qed.

Ltac hsu_br_false :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with false by (vm_compute; reflexivity); cbv iota
  end.

Lemma hsu_signed_lit : forall z, - 2 ^ 63 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z H. unfold bv_signed. rewrite unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 64) with (2 ^ 63). change (bv_modulus 64) with (2 ^ 64).
  rewrite Zplus_mod_idemp_l. rewrite Z.mod_small by lia. lia.
Qed.

Lemma hsu_sltiu : forall (z : Z) (I : Z), 0 < z < 2 ^ 64 -> bv_wrap 64 I = 1 -> v_sltiu (Z_to_bv 64 z) I = Z_to_bv 64 0.
Proof.
  intros z I Hz HI. unfold v_sltiu. rewrite unsigned_lit by lia. rewrite HI.
  replace (z <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Definition hsu_len (toks : list (list byte)) : Z := fold_right (fun w s => Z.of_nat (length w) + 1 + s) 0 toks.

Lemma hsu_len_cons : forall w ws, hsu_len (w :: ws) = Z.of_nat (length w) + 1 + hsu_len ws.
Proof. reflexivity. Qed.

Lemma hsu_len_nn : forall ws, 0 <= hsu_len ws.
Proof. induction ws as [|w ws IH]; [unfold hsu_len; cbn; lia | rewrite hsu_len_cons; lia]. Qed.

Definition tokf (m : word -> option byte) (p : Z) (w : list byte) : Prop :=
  exists slack, bytes_at rsegs m p (w ++ Z_to_bv 8 0 :: slack) /\ no0 w /\
    (- (p + Z.of_nat (length w) + 1)) mod 8 <= Z.of_nat (length slack) /\ 0 <= p.

Lemma tokf_same : forall m m' p w, tokf m p w -> munch [] m m' -> tokf m' p w.
Proof.
  intros m m' p w (slack & HP & NZ & SL & P0) MU. exists slack. split; [|auto].
  eapply bytes_at_transport; [exact HP | exact MU |]. cbn [disjoint_from]. exact I.
Qed.

Lemma length_concat_le8 : forall pl : list Z,
  Z.of_nat (length (concat (map (fun p => le8 (Z_to_bv 64 p)) pl))) = 8 * Z.of_nat (length pl).
Proof.
  induction pl as [|p pl IH]; [reflexivity|]. cbn [map concat length]. rewrite length_app, length_le8.
  rewrite Nat2Z.inj_add, IH. lia.
Qed.

Section E1.
Variables (sp gp tp s0 s2 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (ptok : Z).
Hypothesis STRLEN : strlen_contract.
Hypothesis HP0 : 0 < ptok.

Lemma hsu_len_loop : forall (pl : list Z) (ws : list (list byte)) ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    m acc cur,
  mem_inv rsegs m -> Forall2 (tokf m) pl ws ->
  bytes_at rsegs m cur (concat (map (fun p => le8 (Z_to_bv 64 p)) pl)) ->
  pl <> [] -> ptok <= cur -> 0 <= acc -> acc + hsu_len ws < 2 ^ 63 ->
  evt rsegs (fun ms' => exists ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
       ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 ptok) a0' a1' a2' a3' a4' a5' a6' a7'
                     s2 (Z_to_bv 64 1) (Z_to_bv 64 (acc + hsu_len ws)) (Z_to_bv 64 1) (Z_to_bv 64 0)
                     (Z_to_bv 64 (cur + 8 * Z.of_nat (length pl))) (Z_to_bv 64 (cur + 8 * Z.of_nat (length pl)))
                     s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x168d8) fc None m' (seg_rom rsegs)
       /\ munch [] m m' /\ mem_inv rsegs m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 ptok) a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 1) (Z_to_bv 64 acc)
             (Z_to_bv 64 1) (Z_to_bv 64 (Z.of_nat (length pl))) (Z_to_bv 64 cur) (Z_to_bv 64 cur)
             s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x168a4) fc None m (seg_rom rsegs)).
Proof.
  induction pl as [|p pl IH]; intros ws ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m acc cur
    MI TK PB Hne Hc Ha Hl; [congruence|].
  inversion TK as [|? w ? ws' TP TK' E1 E2]; subst ws.
  destruct TP as (slack & HP & NZ & SL & P0).
  cbn [map concat] in PB. apply bytes_at_app in PB as [PB1 PB2]. rewrite length_le8 in PB2.
  change (Z.of_nat 8) with 8 in PB2.
  pose proof (bytes_at_bound _ _ _ _ HP) as BP. rewrite length_app in BP. cbn [length] in BP.
  pose proof (bytes_at_bound _ _ _ _ PB1) as B1. rewrite length_le8 in B1. change (Z.of_nat 8) with 8 in B1.
  pose proof (bytes_at_bound _ _ _ _ PB2) as B2. rewrite length_concat_le8 in B2.
  assert (RS : ov_read_bytes rsegs m (wa (cur + 0)) 8 = Some (le8 (Z_to_bv 64 p))).
  { rewrite (bytes_at_read rsegs m _ _ 0 8 PB1) by (rewrite ?length_le8; lia).
    change (Z.to_nat 0) with 0%nat. rewrite skipn_O. f_equal; apply firstn_all2; rewrite ?length_le8; lia. }
  assert (HPu : bytes_at rsegs m (bv_unsigned (Z_to_bv 64 p)) (w ++ Z_to_bv 8 0 :: slack))
    by (rewrite unsigned_lit by lia; exact HP).
  assert (SLu : (- (bv_unsigned (Z_to_bv 64 p) + Z.of_nat (length w) + 1)) mod 8 <= Z.of_nat (length slack))
    by (rewrite unsigned_lit by lia; exact SL).
  clear HP PB1.
  pose proof (munch_refl [] m) as MU.
  step.
  rewrite hsu_ltu by lia. rewrite (proj2 (Z.ltb_ge cur ptok)) by lia. cbv iota.
  step. step.
  rewrite (hsu_sltiu cur 1) by first [lia | reflexivity].
  step. hsu_br_false.
  step. if_false.
  step. step.
  eapply evt_cut; [eapply STRLEN with (str := w) (slack := slack); [exact HPu | exact NZ | exact SLu | exact MI] |].
  post_call rsegs m.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  match goal with H : mem_inv rsegs m1 |- _ => rename H into MI1 end.
  assert (TK1 : Forall2 (tokf m1) pl ws')
    by (eapply Forall2_impl; [|exact TK']; intros p0 w0 Hq0; exact (tokf_same m m1 p0 w0 Hq0 MU)).
  step. step. step. step. step.
  step.
  rewrite hsu_eqb64 by (cbn [length] in *; lia).
  destruct pl as [|p2 pl2].
  - inversion TK' as [E3 E4|]; subst ws'.
    rewrite (proj2 (Z.eqb_eq (Z.of_nat (length [p]) + -1) 0)) by (cbn [length]; lia). cbn [negb]. cbv iota.
    apply evt_done. do 16 eexists. exists m1. split; [|split; [exact MU | exact MI1]].
    replace (Z.of_nat (length [p]) + -1) with 0 by (cbn [length]; lia).
    replace (cur + 8 * Z.of_nat (length [p])) with (cur + 8) by (cbn [length]; lia).
    replace (acc + hsu_len [w]) with (acc + Z.of_nat (length w) + 1) by (unfold hsu_len; cbn [fold_right]; lia).
    reflexivity.
  - rewrite (proj2 (Z.eqb_neq (Z.of_nat (length (p :: p2 :: pl2)) + -1) 0)) by (cbn [length]; lia).
    cbn [negb]. cbv iota.
    replace (Z.of_nat (length (p :: p2 :: pl2)) + -1) with (Z.of_nat (length (p2 :: pl2))) by (cbn [length]; lia).
    eapply evt_mono.
    { eapply (IH ws' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 (acc + Z.of_nat (length w) + 1) (cur + 8));
        [exact MI1 | exact TK1 | exact PB2 | discriminate | lia | lia |].
      rewrite hsu_len_cons in Hl. lia. }
    intros ms' (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2
      & -> & MU2 & MI2).
    exists ra', t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m2. split.
    + rewrite hsu_len_cons.
      replace (acc + (Z.of_nat (length w) + 1 + hsu_len ws')) with (acc + Z.of_nat (length w) + 1 + hsu_len ws') by lia.
      replace (cur + 8 * Z.of_nat (length (p :: p2 :: pl2))) with (cur + 8 + 8 * Z.of_nat (length (p2 :: pl2)))
        by (cbn [length]; lia).
      reflexivity.
    + split; [exact (munch_trans _ _ _ _ MU MU2) | exact MI2].
Qed.

End E1.

Lemma hsu_sltu0 : forall z, 0 < z < 2 ^ 64 -> v_sltu (Z_to_bv 64 0) (Z_to_bv 64 z) = Z_to_bv 64 1.
Proof.
  intros z Hz. unfold v_sltu, c_ltu. rewrite hsu_ltu by lia.
  replace (0 <? z) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma hsu_land7 : forall z, 0 <= z < 2 ^ 64 -> z mod 8 = 0 -> Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 z)) 7) = Z_to_bv 64 0.
Proof.
  intros z Hz H8. rewrite unsigned_lit by lia. change 7 with (Z.ones 3). rewrite Z.land_ones by lia.
  change (2 ^ 3) with 8. rewrite H8. reflexivity.
Qed.

Lemma hsu_sltiu0 : v_sltiu (Z_to_bv 64 0) 1 = Z_to_bv 64 1.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma hsu_e1 : strlen_contract ->
  forall sp gp tp s0 s9 s10 s11 (F : bvmap 5 word) (fc : bv 32) (ptok : Z)
    (pl : list Z) ws ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 t3 t4 t5 t6 m,
  0 < ptok -> mem_inv rsegs m -> Forall2 (tokf m) pl ws ->
  bytes_at rsegs m ptok (concat (map (fun p => le8 (Z_to_bv 64 p)) pl)) ->
  (1 <= length pl <= 64)%nat -> ptok mod 8 = 0 -> hsu_len ws <= LMAX + 1 ->
  evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
       ms' = MS (mkR (Z_to_bv 64 0x168e0) sp gp tp t0' t1' t2' s0 (Z_to_bv 64 ptok) (Z_to_bv 64 (hsu_len ws + 1))
                     a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (Z.of_nat (length pl))) (Z_to_bv 64 1)
                     (Z_to_bv 64 (hsu_len ws)) (Z_to_bv 64 1) (Z_to_bv 64 0)
                     (Z_to_bv 64 (ptok + 8 * Z.of_nat (length pl))) (Z_to_bv 64 (ptok + 8 * Z.of_nat (length pl)))
                     s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x15a88) fc None m' (seg_rom rsegs)
       /\ munch [] m m' /\ mem_inv rsegs m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 ptok) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.of_nat (length pl)))
             s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x16880) fc None m (seg_rom rsegs)).
Proof.
  intros SLEN sp gp tp s0 s9 s10 s11 F fc ptok pl ws ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8
    t3 t4 t5 t6 m HP0 MI TK PB NL P8 LW.
  pose proof (bytes_at_bound _ _ _ _ PB) as BB. rewrite length_concat_le8 in BB.
  assert (SS : bv_signed (Z_to_bv 64 (Z.of_nat (length pl))) = Z.of_nat (length pl)) by (apply hsu_signed_lit; lia).
  pose proof (hsu_len_nn ws) as LN. unfold LMAX in LW.
  step. if_false.
  do 8 step.
  rewrite (hsu_sltu0 ptok) by lia. rewrite (hsu_land7 ptok) by lia. rewrite hsu_sltiu0.
  replace (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 1)) (bv_unsigned (Z_to_bv 64 1)))) with (Z_to_bv 64 1)
    by (apply bv_eq; vm_compute; reflexivity).
  eapply evt_cut.
  { eapply (hsu_len_loop sp gp tp s0 (Z_to_bv 64 (Z.of_nat (length pl))) s9 s10 s11 F fc ptok SLEN HP0 pl ws
              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m 0 ptok);
      [exact MI | exact TK | exact PB | destruct pl; [cbn in NL; lia | discriminate] | lia | lia | lia]. }
  intros ms (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1
    & -> & MU1 & MI1).
  step. step.
  replace (0 + hsu_len ws + 1) with (hsu_len ws + 1) by lia. replace (0 + hsu_len ws) with (hsu_len ws) by lia.
  apply evt_done. do 14 eexists. exists m1. split; [reflexivity|]. split; [exact MU1 | exact MI1].
Qed.

Lemma hsu_join_len : forall ws, ws <> [] -> Z.of_nat (length (join_sp ws)) + 1 = hsu_len ws.
Proof.
  induction ws as [|w ws IH]; intros H; [congruence|]. rewrite hsu_len_cons.
  destruct ws as [|w2 ws'].
  - cbn [join_sp]. unfold hsu_len. cbn [fold_right]. lia.
  - change (join_sp (w :: w2 :: ws')) with (w ++ SPACE :: join_sp (w2 :: ws')).
    rewrite length_app. cbn [length]. specialize (IH ltac:(discriminate)). lia.
Qed.

Lemma hsu_join_no0 : forall ws, Forall no0 ws -> no0 (join_sp ws).
Proof.
  intros ws HF. induction HF as [|w ws Hw HF IH]; [intros []|].
  destruct ws as [|w2 ws']; [exact Hw|].
  change (join_sp (w :: w2 :: ws')) with (w ++ SPACE :: join_sp (w2 :: ws')).
  apply no0_app; [exact Hw|]. intros [E|E]; [|exact (IH E)].
  apply (f_equal bv_unsigned) in E. unfold SPACE in E. rewrite !byte_unsigned in E by lia. discriminate.
Qed.

Lemma hsu_join_snoc : forall X w,
  join_sp (X ++ [w]) = match X with [] => w | _ :: _ => join_sp X ++ SPACE :: w end.
Proof.
  induction X as [|x X IH]; intros w; [reflexivity|].
  destruct X as [|y X']; [reflexivity|].
  replace ((x :: y :: X') ++ [w]) with (x :: ((y :: X') ++ [w])) by reflexivity.
  replace (join_sp (x :: ((y :: X') ++ [w]))) with (x ++ SPACE :: join_sp ((y :: X') ++ [w])) by reflexivity.
  rewrite IH. change (join_sp (x :: y :: X')) with (x ++ SPACE :: join_sp (y :: X')).
  rewrite <- app_assoc. reflexivity.
Qed.

Definition hsu_D (X : list (list byte)) : list byte := match X with [] => [] | _ :: _ => join_sp X ++ [SPACE] end.

Lemma hsu_D_snoc : forall X w, join_sp (X ++ [w]) = hsu_D X ++ w.
Proof. intros X w. rewrite hsu_join_snoc. destruct X; [reflexivity|]. cbn [hsu_D]. rewrite <- app_assoc. reflexivity. Qed.

Lemma hsu_len_app : forall X Y, hsu_len (X ++ Y) = hsu_len X + hsu_len Y.
Proof.
  induction X as [|x X IH]; intros Y.
  - cbn [app]. change (hsu_len []) with 0. lia.
  - cbn [app]. rewrite !hsu_len_cons, IH. lia.
Qed.

Lemma hsu_D_len : forall X, Z.of_nat (length (hsu_D X)) = hsu_len X.
Proof.
  intros [|x X]; [reflexivity|]. cbn [hsu_D]. rewrite length_app. cbn [length].
  rewrite <- (hsu_join_len (x :: X)) by discriminate. lia.
Qed.

Lemma hsu_D_no0 : forall X, Forall no0 X -> no0 (hsu_D X).
Proof.
  intros [|x X] HF; [intros []|]. cbn [hsu_D]. apply no0_app; [exact (hsu_join_no0 _ HF)|].
  intros [E|[]]. apply (f_equal bv_unsigned) in E. unfold SPACE in E. rewrite !byte_unsigned in E by lia. discriminate.
Qed.

Lemma hsu_rw_mk : forall m a cs, cells_wf cs -> bytes_at rsegs m a (cells_bytes cs) ->
  wr_at rsegs m a (Z.of_nat (cells_size cs)) -> rw_cells rsegs m a cs.
Proof. intros m a cs H1 H2 H3. split; [split|]; assumption. Qed.

Lemma hsu_wr_sub : forall m a n d k, wr_at rsegs m a n -> 0 <= d -> 0 <= k -> d + k <= n -> wr_at rsegs m (a + d) k.
Proof.
  intros m a n d k (H1 & H2 & H3) Hd Hk Hn. split; [lia|]. split; [lia|]. intros i Hi.
  replace (a + d + i) with (a + (d + i)) by ring. apply H3. lia.
Qed.

Ltac hsu_br_true :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with true by (vm_compute; reflexivity); cbv iota
  end.

Section E2.
Variables (sp gp tp s0 s2 s5 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (buf size Tlen lo ptok : Z) (m0 : word -> option byte).
Hypothesis STRLEN : strlen_contract.
Hypothesis STRCAT : strcat_contract.
Hypothesis HBUF : 4096 <= buf.
Hypothesis HSZ : 0 < size.
Hypothesis HTL : size <= Tlen.
Hypothesis HTA : (buf + Tlen) mod 8 = 0.
Hypothesis HTLO : buf + Tlen <= lo.
Hypothesis HSP : lo + 48 <= bv_unsigned sp.
Hypothesis HP0 : 0 <= ptok.
Hypothesis HS5 : bv_unsigned s5 = 2 ^ 64 - 1 - ptok.

Definition jinvX (m : word -> option byte) (X : list byte) : Prop :=
  mem_inv rsegs m /\ stk rsegs m lo (bv_unsigned sp) /\
  munch [(bv_unsigned sp - 48, bv_unsigned sp); (buf, buf + size)] m0 m /\ wmono rsegs m0 m /\
  wr_at rsegs m buf size /\ bytes_at rsegs m buf X /\ Z.of_nat (length X) = Tlen.

Lemma hsu_jpad : forall J junk, Z.of_nat (length (J ++ Z_to_bv 8 0 :: junk)) = Tlen ->
  (- (buf + Z.of_nat (length J) + 1)) mod 8 <= Z.of_nat (length junk).
Proof.
  intros J junk HL. rewrite length_app in HL. cbn [length] in HL.
  assert (E : (- (buf + Tlen)) mod 8 = 0) by (apply Z_mod_zero_opp_full; exact HTA).
  replace (- (buf + Z.of_nat (length J) + 1)) with (Z.of_nat (length junk) + - (buf + Tlen)) by lia.
  rewrite Zplus_mod, E, Z.add_0_r, Z.mod_mod by lia. apply Z.mod_le; lia.
Qed.

Lemma jinv_store : forall m P x S c, jinvX m (P ++ x :: S) -> Z.of_nat (length P) < size ->
  jinvX (write_to_mem m (wa (buf + Z.of_nat (length P))) [c]) (P ++ c :: S).
Proof.
  intros m P x S c (MI & ST & MU & WM & HW & HB & HL) Hp.
  pose proof (bytes_at_bound _ _ _ _ HB) as BB. rewrite length_app in BB. cbn [length] in BB.
  rewrite length_app in HL. cbn [length] in HL.
  assert (SO : store_ok rsegs m (wa (buf + Z.of_nat (length P))) (length [c]) = true)
    by (apply (wr_at_store_ok rsegs m buf size); [exact HW | lia | cbn [length]; lia]).
  apply bytes_at_app in HB as [HB1 HB2]. replace (x :: S) with ([x] ++ S) in HB2 by reflexivity.
  apply bytes_at_app in HB2 as [_ HB3]. cbn [length] in HB3.
  split; [exact (mem_inv_store rsegs m _ [c] MI SO)|].
  split; [apply stk_write; [exact ST | lia | cbn [length]; lia]|].
  split; [apply munch_write; [exact MU | lia | cbn [length]; lia | cbn [inside length Z.of_nat]; right; left; lia]|].
  split; [apply wmono_write; exact WM|].
  split; [apply wr_at_write; exact HW|].
  split; [|rewrite length_app; cbn [length]; lia].
  apply bytes_at_app. split.
  - apply bytes_at_write_other; [exact HB1 | lia | cbn [length]; lia | cbn [length]; lia].
  - replace (c :: S) with ([c] ++ S) by reflexivity. apply bytes_at_app. split.
    + apply bytes_at_write_same; cbn [length]; lia.
    + apply bytes_at_write_other; [exact HB3 | lia | cbn [length]; lia | cbn [length]; lia].
Qed.

Lemma jinv_strlen : forall m m' X, jinvX m X -> munch [] m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> jinvX m' X.
Proof.
  intros m m' X (MI & ST & MU & WM & HW & HB & HL) MU' WM' MI'.
  split; [exact MI'|].
  split; [apply (stk_transport_disjoint rsegs [] m m' _ _ ST MU' WM'); cbn [disjoint_from]; exact I|].
  split; [apply (munch_trans _ m0 m m' MU); apply (munch_weaken [] _ m m'); [intros x _; exact I | exact MU']|].
  split; [exact (wmono_trans rsegs _ _ _ WM WM')|].
  split; [exact (wr_at_transport rsegs m m' _ _ HW WM')|].
  split; [|exact HL].
  apply (bytes_at_transport rsegs [] m m' _ _ HB MU'). cbn [disjoint_from]. exact I.
Qed.

Lemma jinv_strcat : forall m m' D dslack w, jinvX m (D ++ Z_to_bv 8 0 :: dslack) ->
  munch [(bv_unsigned sp - 48, bv_unsigned sp);
         (buf + Z.of_nat (length D), buf + Z.of_nat (length D) + Z.of_nat (length w) + 1)] m m' ->
  wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp) ->
  bytes_at rsegs m' buf (D ++ w ++ [Z_to_bv 8 0]) ->
  Z.of_nat (length D) + Z.of_nat (length w) + 1 <= size ->
  jinvX m' ((D ++ w) ++ Z_to_bv 8 0 :: skipn (length w) dslack).
Proof.
  intros m m' D dslack w (MI & ST & MU & WM & HW & HB & HL) MU' WM' MI' ST' HB' Hs.
  pose proof (bytes_at_bound _ _ _ _ HB) as BB. rewrite length_app in BB. cbn [length] in BB.
  rewrite length_app in HL. cbn [length] in HL.
  assert (LW : (length w <= length dslack)%nat) by lia.
  split; [exact MI'|]. split; [exact ST'|].
  split.
  { apply (munch_trans _ m0 m m' MU). eapply munch_weaken; [|exact MU'].
    intros x Hx. cbn [outside] in *. lia. }
  split; [exact (wmono_trans rsegs _ _ _ WM WM')|].
  split; [exact (wr_at_transport rsegs m m' _ _ HW WM')|].
  split.
  - assert (E : (D ++ w) ++ Z_to_bv 8 0 :: skipn (length w) dslack = (D ++ w ++ [Z_to_bv 8 0]) ++ skipn (length w) dslack)
      by (rewrite <- !app_assoc; reflexivity).
    rewrite E. apply bytes_at_app. split; [exact HB'|].
    apply bytes_at_app in HB as [_ HB2].
    replace (Z_to_bv 8 0 :: dslack) with ((Z_to_bv 8 0 :: firstn (length w) dslack) ++ skipn (length w) dslack) in HB2
      by (cbn [app]; rewrite firstn_skipn; reflexivity).
    apply bytes_at_app in HB2 as [_ HB3]. cbn [length] in HB3. rewrite length_firstn in HB3.
    rewrite !length_app. cbn [length].
    replace (buf + Z.of_nat (length D + (length w + 1))) with
      (buf + Z.of_nat (length D) + Z.of_nat (S (Nat.min (length w) (length dslack)))) by lia.
    apply (bytes_at_transport rsegs _ m m' _ _ HB3 MU'). cbn [disjoint_from]. rewrite length_skipn. lia.
  - rewrite !length_app. cbn [length]. rewrite length_skipn. lia.
Qed.

Definition tokj (p : Z) (w : list byte) : Prop :=
  exists slack, bytes_at rsegs m0 p (w ++ Z_to_bv 8 0 :: slack) /\ no0 w /\
    (- (p + Z.of_nat (length w) + 1)) mod 8 <= Z.of_nat (length slack) /\ 0 <= p /\
    (p + Z.of_nat (length (w ++ Z_to_bv 8 0 :: slack)) <= lo \/ bv_unsigned sp <= p) /\
    (p + Z.of_nat (length (w ++ Z_to_bv 8 0 :: slack)) <= buf \/ buf + size <= p).

Lemma hsu_join_head : forall dws junk ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m,
  jinvX m (join_sp dws ++ Z_to_bv 8 0 :: junk) -> Forall no0 dws ->
  hsu_len dws + 1 < size -> (length dws <= 64)%nat ->
  evt rsegs (fun ms' => exists ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' dslack,
       ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 ptok) a0' a1' a2' a3' a4' a5' a6' a7' s2 (Z_to_bv 64 buf)
                     (Z_to_bv 64 (8 * Z.of_nat (length dws))) s5 (Z_to_bv 64 32) s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x16914) fc None m' (seg_rom rsegs)
       /\ jinvX m' (hsu_D dws ++ Z_to_bv 8 0 :: dslack))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 ptok) a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 buf)
             (Z_to_bv 64 (8 * Z.of_nat (length dws))) s5 (Z_to_bv 64 32) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x168fc) fc None m (seg_rom rsegs)).
Proof.
  intros dws junk ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m JI NZ HL HN.
  destruct dws as [|w0 dws0].
  - step. hsu_br_true.
    apply evt_done. do 16 eexists. exists m, junk. split; [reflexivity | exact JI].
  - set (J := join_sp (w0 :: dws0)) in *.
    pose proof (hsu_join_len (w0 :: dws0) ltac:(discriminate)) as JL. fold J in JL.
    assert (NZJ : no0 J) by exact (hsu_join_no0 _ NZ).
    pose proof JI as (_ & _ & _ & _ & _ & HB & HLX).
    pose proof (bytes_at_bound _ _ _ _ HB) as BB. rewrite length_app in BB. cbn [length] in BB.
    assert (UB : bv_unsigned (Z_to_bv 64 buf) = buf) by (apply unsigned_lit; lia).
    assert (HBu : bytes_at rsegs m (bv_unsigned (Z_to_bv 64 buf)) (J ++ Z_to_bv 8 0 :: junk)) by (rewrite UB; exact HB).
    assert (SLu : (- (bv_unsigned (Z_to_bv 64 buf) + Z.of_nat (length J) + 1)) mod 8 <= Z.of_nat (length junk))
      by (rewrite UB; exact (hsu_jpad J junk HLX)).
    pose proof JI as (MI & _).
    clear HB.
    pose proof (munch_refl [] m) as MUr. pose proof (wmono_refl rsegs m) as WMr.
    assert (KP : (1 <= length (w0 :: dws0))%nat) by (cbn [length]; lia).
    step. rewrite hsu_eqb64 by lia. rewrite (proj2 (Z.eqb_neq _ 0)) by lia. cbv iota.
    step. step.
    eapply evt_cut; [eapply STRLEN with (str := J) (slack := junk); [exact HBu | exact NZJ | exact SLu | exact MI] |].
    post_call rsegs m.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    match goal with H : mem_inv rsegs m1 |- _ => rename H into MI1 end.
    pose proof (jinv_strlen m m1 _ JI MUr WMr MI1) as JI1.
    step.
    pose proof JI1 as (_ & _ & _ & _ & HW1 & _).
    assert (HS1 : store_ok rsegs m1 (wa (buf + Z.of_nat (length J) + 0)) 1 = true).
    { replace (buf + Z.of_nat (length J) + 0) with (buf + Z.of_nat (length J)) by lia.
      apply (wr_at_store_ok rsegs m1 buf size); [exact HW1 | lia | lia]. }
    step.
    replace (le1 (Z_to_bv 64 32)) with [SPACE] by (vm_compute; reflexivity).
    replace (wa (buf + Z.of_nat (length J) + 0)) with (wa (buf + Z.of_nat (length J))) by (f_equal; lia).
    pose proof (jinv_store m1 J (Z_to_bv 8 0) junk SPACE JI1 ltac:(lia)) as JI2.
    set (m2 := write_to_mem m1 (wa (buf + Z.of_nat (length J))) [SPACE]) in *. clearbody m2.
    destruct junk as [|j0 junk'].
    { exfalso. rewrite length_app in HLX. cbn [length] in HLX. lia. }
    replace (J ++ SPACE :: j0 :: junk') with ((J ++ [SPACE]) ++ j0 :: junk') in JI2 by (rewrite <- app_assoc; reflexivity).
    pose proof JI2 as (_ & _ & _ & _ & HW2 & _).
    assert (HS2 : store_ok rsegs m2 (wa (buf + Z.of_nat (length J) + 1)) 1 = true).
    { rewrite <- Z.add_assoc. apply (wr_at_store_ok rsegs m2 buf size); [exact HW2 | lia | lia]. }
    step.
    match goal with |- context [write_to_mem _ _ (le1 ?v)] => replace (le1 v) with [Z_to_bv 8 0] by (vm_compute; reflexivity) end.
    replace (wa (buf + Z.of_nat (length J) + 1)) with (wa (buf + Z.of_nat (length (J ++ [SPACE]))))
      by (f_equal; rewrite length_app; cbn [length]; lia).
    pose proof (jinv_store m2 (J ++ [SPACE]) j0 junk' (Z_to_bv 8 0) JI2 ltac:(rewrite length_app; cbn [length]; lia)) as JI3.
    assert (JI3' : jinvX (write_to_mem m2 (Z_to_bv 64 (buf + Z.of_nat (length J) + 1)) [Z_to_bv 8 0])
                     (hsu_D (w0 :: dws0) ++ Z_to_bv 8 0 :: junk')).
    { replace (Z_to_bv 64 (buf + Z.of_nat (length J) + 1)) with (wa (buf + Z.of_nat (length (J ++ [SPACE]))))
        by (unfold wa; f_equal; rewrite length_app; cbn [length]; lia). exact JI3. }
    apply evt_done. do 16 eexists. eexists. exists junk'. split; [reflexivity | exact JI3'].
Qed.

Lemma hsu_join_cat : forall dws w p dslack ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m,
  jinvX m (hsu_D dws ++ Z_to_bv 8 0 :: dslack) -> Forall no0 dws -> tokj p w ->
  bytes_at rsegs m0 (ptok + 8 * Z.of_nat (length dws)) (le8 (Z_to_bv 64 p)) ->
  (ptok + 8 * Z.of_nat (length dws) + 8 <= lo \/ bv_unsigned sp <= ptok + 8 * Z.of_nat (length dws)) ->
  (ptok + 8 * Z.of_nat (length dws) + 8 <= buf \/ buf + size <= ptok + 8 * Z.of_nat (length dws)) ->
  hsu_len dws + Z.of_nat (length w) + 1 <= size ->
  evt rsegs (fun ms' => exists ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' dslack',
       ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 ptok) a0' a1' a2' a3' a4' a5' a6' a7' s2 (Z_to_bv 64 buf)
                     (Z_to_bv 64 (8 * Z.of_nat (length dws) + 8)) s5 (Z_to_bv 64 32) s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x1692c) fc None m' (seg_rom rsegs)
       /\ jinvX m' (join_sp (dws ++ [w]) ++ Z_to_bv 8 0 :: dslack'))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 ptok) a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 buf)
             (Z_to_bv 64 (8 * Z.of_nat (length dws))) s5 (Z_to_bv 64 32) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16914) fc None m (seg_rom rsegs)).
Proof.
  intros dws w p dslack ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m JI NZ TK PB HC1 HC2 HS.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  pose proof (hsu_D_len dws) as DL. pose proof (hsu_D_no0 dws NZ) as DN.
  set (cur := ptok + 8 * Z.of_nat (length dws)) in *.
  set (D := hsu_D dws) in *.
  destruct TK as (tsl & TP & TN & TS & TP0 & TW1 & TW2).
  rewrite length_app in TW1, TW2. cbn [length] in TW1, TW2.
  pose proof JI as (MI & ST & MU & WM & HW & HB & HL).
  pose proof (hsu_jpad D dslack HL) as PAD.
  pose proof (bytes_at_bound _ _ _ _ HB) as BB. rewrite length_app in BB, HL. cbn [length] in BB, HL.
  pose proof (bytes_at_bound _ _ _ _ TP) as BT. rewrite length_app in BT. cbn [length] in BT.
  assert (UB : bv_unsigned (Z_to_bv 64 buf) = buf) by (apply unsigned_lit; lia).
  assert (UP : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (PBm : bytes_at rsegs m cur (le8 (Z_to_bv 64 p))).
  { apply (bytes_at_transport rsegs _ m0 m _ _ PB MU). cbn [disjoint_from]. rewrite length_le8.
    change (Z.of_nat 8) with 8. lia. }
  pose proof (bytes_at_bound _ _ _ _ PBm) as BC. rewrite length_le8 in BC. change (Z.of_nat 8) with 8 in BC.
  assert (RS : ov_read_bytes rsegs m (wa (cur + 0)) 8 = Some (le8 (Z_to_bv 64 p))).
  { rewrite (bytes_at_read rsegs m _ _ 0 8 PBm) by (rewrite ?length_le8; lia).
    change (Z.to_nat 0) with 0%nat. rewrite skipn_O. f_equal; apply firstn_all2; rewrite ?length_le8; lia. }
  assert (HPu : bytes_at rsegs m (bv_unsigned (Z_to_bv 64 p)) (w ++ Z_to_bv 8 0 :: tsl)).
  { rewrite UP. apply (bytes_at_transport rsegs _ m0 m _ _ TP MU). cbn [disjoint_from].
    rewrite length_app. cbn [length]. lia. }
  assert (HDu : bytes_at rsegs m (bv_unsigned (Z_to_bv 64 buf)) (D ++ Z_to_bv 8 0 :: dslack)) by (rewrite UB; exact HB).
  assert (LW : (length w <= length dslack)%nat) by lia.
  assert (RW : rw_cells rsegs m (bv_unsigned (Z_to_bv 64 buf) + Z.of_nat (length D))
                 [CB (S (length w)) (Z_to_bv 8 0 :: firstn (length w) dslack)]).
  { rewrite UB. apply hsu_rw_mk.
    - cbn [cells_wf cell_wf length]. rewrite length_firstn, Nat.min_l by exact LW. split; [reflexivity | exact I].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. pose proof HB as HB0. apply bytes_at_app in HB0 as [_ HB2].
      replace (Z_to_bv 8 0 :: dslack) with ((Z_to_bv 8 0 :: firstn (length w) dslack) ++ skipn (length w) dslack) in HB2
        by (cbn [app]; rewrite firstn_skipn; reflexivity).
      apply bytes_at_app in HB2 as [HB2 _]. exact HB2.
    - cbn [cells_size csize]. apply (hsu_wr_sub m buf size); [exact HW | lia | lia | lia]. }
  clear HB PB TP.
  unfold cur in *.
  step.
  rewrite (hsu_ltu_l s5) by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbv iota.
  step. step. step. step.
  eapply evt_cut.
  { eapply STRCAT with (dstr := D) (dslack := dslack) (str := w) (slack := tsl)
      (junk := Z_to_bv 8 0 :: firstn (length w) dslack) (lo := lo);
      [exact HDu | exact DN | rewrite UB; exact PAD | exact RW | exact HPu | exact TN | rewrite UP; exact TS
      | lia | exact ST | exact HSP | lia | lia | lia | exact MI]. }
  intros ms' PO. unfold strcat_post in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  E & MU' & WM' & MI' & ST' & HB' & _ & _).
  subst ms'. rewrite UB in MU', HB'.
  replace (ret_pc (Z_to_bv 64 0x16928)) with (Z_to_bv 64 0x16928) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  pose proof (jinv_strcat m m' D dslack w JI MU' WM' MI' ST' HB' ltac:(lia)) as JI'.
  step.
  apply evt_done. do 16 eexists. exists m', (skipn (length w) dslack). split; [reflexivity|].
  rewrite hsu_D_snoc. exact JI'.
Qed.

Lemma hsu_join_loop : forall (pl : list Z) ws dws (n : Z) junk ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m,
  jinvX m (join_sp dws ++ Z_to_bv 8 0 :: junk) -> Forall no0 dws -> Forall2 tokj pl ws -> pl <> [] ->
  bytes_at rsegs m0 (ptok + 8 * Z.of_nat (length dws)) (concat (map (fun p => le8 (Z_to_bv 64 p)) pl)) ->
  n = Z.of_nat (length dws + length pl) ->
  (ptok + 8 * n <= lo \/ bv_unsigned sp <= ptok + 8 * Z.of_nat (length dws)) ->
  (ptok + 8 * n <= buf \/ buf + size <= ptok + 8 * Z.of_nat (length dws)) ->
  bv_unsigned s2 = 8 * n -> (length dws + length pl <= 64)%nat ->
  hsu_len (dws ++ ws) + 1 <= size ->
  evt rsegs (fun ms' => exists ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' slack,
       ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 ptok) a0' a1' a2' a3' a4' a5' a6' a7' s2 (Z_to_bv 64 buf)
                     (Z_to_bv 64 (8 * n)) s5 (Z_to_bv 64 32) s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x16930) fc None m' (seg_rom rsegs)
       /\ jinvX m' (join_sp (dws ++ ws) ++ Z_to_bv 8 0 :: slack))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 ptok) a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 buf)
             (Z_to_bv 64 (8 * Z.of_nat (length dws))) s5 (Z_to_bv 64 32) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x168fc) fc None m (seg_rom rsegs)).
Proof.
  induction pl as [|p pl IH]; intros ws dws n junk ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m
    JI NZ TK Hne PB Hn HD1 HD2 H2 HN HS; [congruence|].
  inversion TK as [|? w ? ws' TP TK' E1 E2]; subst ws.
  cbn [map concat] in PB. apply bytes_at_app in PB as [PB1 PB2]. rewrite length_le8 in PB2.
  change (Z.of_nat 8) with 8 in PB2.
  cbn [length] in Hn, HN.
  pose proof (bytes_at_bound _ _ _ _ PB1) as B1. rewrite length_le8 in B1. change (Z.of_nat 8) with 8 in B1.
  pose proof HS as HS'. rewrite hsu_len_app, hsu_len_cons in HS'.
  pose proof (hsu_len_nn ws') as LN0. pose proof (hsu_len_nn dws) as LN1.
  pose proof TP as (_ & _ & TN & _).
  eapply evt_cut.
  { eapply (hsu_join_head dws junk); [exact JI | exact NZ | lia | lia]. }
  intros ms (ra1 & t01 & t11 & t21 & a01 & a11 & a21 & a31 & a41 & a51 & a61 & a71 & t31 & t41 & t51 & t61 &
             m1 & dsl1 & -> & JI1).
  eapply evt_cut.
  { eapply (hsu_join_cat dws w p dsl1); [exact JI1 | exact NZ | exact TP | exact PB1 | lia | lia | lia]. }
  intros ms (ra2 & t02 & t12 & t22 & a02 & a12 & a22 & a32 & a42 & a52 & a62 & a72 & t32 & t42 & t52 & t62 &
             m2 & dsl2 & -> & JI2).
  step.
  unfold bv_eqb. rewrite (unsigned_lit (8 * Z.of_nat (length dws) + 8)) by lia. rewrite H2.
  destruct pl as [|p2 pl2].
  - inversion TK' as [E3 E4|]; subst ws'. cbn [length] in Hn.
    rewrite (proj2 (Z.eqb_eq _ _)) by lia. cbn [negb]. cbv iota.
    replace (8 * Z.of_nat (length dws) + 8) with (8 * n) by lia.
    apply evt_done. do 16 eexists. exists m2, dsl2. split; [reflexivity | exact JI2].
  - cbn [length] in Hn, HN.
    rewrite (proj2 (Z.eqb_neq _ _)) by lia. cbn [negb]. cbv iota.
    replace (8 * Z.of_nat (length dws) + 8) with (8 * Z.of_nat (length (dws ++ [w]))) by (rewrite length_app; cbn [length]; lia).
    eapply evt_mono.
    { eapply (IH ws' (dws ++ [w]) n dsl2);
        [exact JI2 | apply Forall_app; split; [exact NZ | constructor; [exact TN | constructor]]
        | exact TK' | discriminate
        | replace (ptok + 8 * Z.of_nat (length (dws ++ [w]))) with (ptok + 8 * Z.of_nat (length dws) + 8)
            by (rewrite length_app; cbn [length]; lia); exact PB2
        | rewrite length_app; cbn [length]; lia | rewrite length_app; cbn [length]; lia
        | rewrite length_app; cbn [length]; lia | exact H2 | rewrite length_app; cbn [length]; lia
        | rewrite <- app_assoc; exact HS]. }
    intros ms' (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' &
                m' & sl & -> & JI').
    do 16 eexists. exists m', sl. split; [reflexivity|].
    rewrite <- app_assoc in JI'. exact JI'.
Qed.

End E2.

Lemma hsu_land_lxor : forall a b c, Z.land (Z.lxor a b) c = Z.lxor (Z.land a c) (Z.land b c).
Proof.
  intros a b c. apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec, !Z.lxor_spec, !Z.land_spec.
  destruct (Z.testbit a n), (Z.testbit b n), (Z.testbit c n); reflexivity.
Qed.

Lemma hsu_not : forall a, 0 <= a < 2 ^ 64 ->
  bv_unsigned (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 a)) 18446744073709551615)) = 2 ^ 64 - 1 - a.
Proof.
  intros a Ha. rewrite (unsigned_lit a) by lia.
  assert (E : Z.lxor a 18446744073709551615 = 2 ^ 64 - 1 - a).
  { change 18446744073709551615 with (Z.ones 64).
    rewrite <- (Z.mod_small a (2 ^ 64)) at 1 by lia.
    rewrite <- Z.land_ones by lia.
    rewrite <- (Z.land_m1_l (Z.ones 64)) at 2.
    rewrite <- hsu_land_lxor.
    rewrite Z.land_ones by lia. rewrite Z.lxor_m1_r, Z.lnot_eq_pred_opp.
    replace (- a - 1) with ((2 ^ 64 - 1 - a) + (-1) * 2 ^ 64) by ring.
    rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
  rewrite E. apply unsigned_lit. lia.
Qed.

Lemma hsu_shift : forall n, 0 <= n < 2 ^ 32 ->
  bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 n)) 32))) 29)) = 8 * n.
Proof.
  intros n Hn. rewrite (unsigned_lit n) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite (unsigned_lit (n * 2 ^ 32)) by lia. rewrite Z.shiftr_div_pow2 by lia.
  replace (n * 2 ^ 32) with ((8 * n) * 2 ^ 29) by ring. rewrite Z.div_mul by lia.
  apply unsigned_lit. lia.
Qed.

Lemma hsu_e2 : strlen_contract -> strcat_contract ->
  forall sp gp tp s0 s7 s8 s9 s10 s11 (F : bvmap 5 word) (fc : bv 32) (buf size Tlen lo ptok : Z)
    (m0 : word -> option byte) (pl : list Z) ws X ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 t3 t4 t5 t6,
  4096 <= buf -> 0 < size -> size <= Tlen -> (buf + Tlen) mod 8 = 0 -> buf + Tlen <= lo -> lo + 48 <= bv_unsigned sp ->
  0 <= ptok ->
  jinvX sp buf size Tlen lo m0 m0 X -> Forall2 (tokj sp buf size lo m0) pl ws ->
  bytes_at rsegs m0 ptok (concat (map (fun p => le8 (Z_to_bv 64 p)) pl)) ->
  (ptok + 8 * Z.of_nat (length pl) <= lo \/ bv_unsigned sp <= ptok) ->
  (ptok + 8 * Z.of_nat (length pl) <= buf \/ buf + size <= ptok) ->
  (1 <= length pl <= 64)%nat -> hsu_len ws + 1 <= size ->
  evt rsegs (fun ms' => exists t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' s2' s5' m' slack,
       ms' = MS (mkR (Z_to_bv 64 0x16950) sp gp tp t0' t1' t2' s0 (Z_to_bv 64 ptok) s0 (Z_to_bv 64 buf)
                     a2' a3' a4' a5' a6' a7' s2' (Z_to_bv 64 buf) (Z_to_bv 64 (8 * Z.of_nat (length pl))) s5'
                     (Z_to_bv 64 32) s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x161c4) fc None m' (seg_rom rsegs)
       /\ jinvX sp buf size Tlen lo m0 m' (join_sp ws ++ Z_to_bv 8 0 :: slack))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 ptok) (Z_to_bv 64 buf) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (Z.of_nat (length pl))) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x168e0) fc None m0 (seg_rom rsegs)).
Proof.
  intros SLEN SCAT sp gp tp s0 s7 s8 s9 s10 s11 F fc buf size Tlen lo ptok m0 pl ws X ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7
    s3 s4 s5 s6 t3 t4 t5 t6 HBUF HSZ HTL HTA HTLO HSP HP0 JI TK PB HD1 HD2 NL HS.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  pose proof JI as (_ & _ & _ & _ & HW & _ & HL).
  destruct X as [|x0 S]; [cbn [length] in HL; lia|].
  assert (HS0 : store_ok rsegs m0 (wa (buf + 0)) 1 = true)
    by (apply (wr_at_store_ok rsegs m0 buf size); [exact HW | lia | lia]).
  assert (JI0 : jinvX sp buf size Tlen lo m0 (write_to_mem m0 (wa (buf + Z.of_nat (length (@nil byte)))) [Z_to_bv 8 0])
                  ([] ++ Z_to_bv 8 0 :: S)).
  { eapply jinv_store; try eassumption; cbn [length]; lia. }
  clear HW.
  step. step. step.
  replace (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0] by (vm_compute; reflexivity).
  replace (wa (buf + 0)) with (wa (buf + Z.of_nat (length (@nil byte)))) by reflexivity.
  set (m1 := write_to_mem m0 (wa (buf + Z.of_nat (length (@nil byte)))) [Z_to_bv 8 0]) in *. clearbody m1.
  do 4 step.
  pose proof (hsu_len_nn ws) as LN.
  pose proof (bytes_at_bound _ _ _ _ PB) as BB. rewrite length_concat_le8 in BB.
  eapply evt_cut.
  { eapply hsu_join_loop with (pl := pl) (ws := ws) (dws := []) (n := Z.of_nat (length pl)) (m := m1) (junk := S);
      try eassumption.
    all: first [ (rewrite hsu_not by lia; reflexivity) | apply Forall_nil
               | (destruct pl; [cbn in NL; lia | discriminate])
               | (cbn [length Z.of_nat]; rewrite Z.mul_0_r, Z.add_0_r; exact PB)
               | reflexivity | (apply hsu_shift; lia) | (cbn [length app Z.of_nat]; lia) ]. }
  intros ms' (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' &
              m' & sl & -> & JI').
  do 4 step.
  apply evt_done. do 15 eexists. exists m', sl. split; [reflexivity | exact JI'].
Qed.

Lemma hsu_free_call :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x16958) sp gp tp t0 t1 t2 s0 s1 s3 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 0x18ad0) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16950) fc None m (seg_rom rsegs)).
Proof. intros. do 2 step. apply evt_done. reflexivity. Qed.

Lemma hsu_tail : mix_call_contract ->
  forall ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo e h : Z) (args : list (word * list byte))
    (sp1 rav q0 q1 q2 q3 q4 q5 q6 q7 q8 : word),
  mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp1) -> lo + 96 <= bv_unsigned sp1 -> 0x343e8 <= lo ->
  rw_cells rsegs m (bv_unsigned sp1 + 16) [C8 q8; C8 q7; C8 q6; C8 q5; C8 q4; C8 q3; C8 q2; C8 q1; C8 q0; C8 rav] ->
  bytes_at rsegs m e (le4 (Z_to_bv 64 6) ++ le4 (Z_to_bv 64 (Z.of_nat (length args)))) ->
  0x33ff0 <= e -> e + 56 <= 0x343e8 -> e mod 8 = 0 -> (length args <= 6)%nat ->
  (forall k p, nth_error args k = Some p -> mc_arg m (bv_unsigned sp1 - 96) (bv_unsigned sp1) e k p) ->
  rw_cells rsegs m 0x343e0 [C8 (Z_to_bv 64 h)] -> 0 <= h < 2 ^ 64 ->
  evt rsegs (fun ms' => exists t0' t1' t2' b1 b2 b3 b4 b5 b6 b7 t3' t4' t5' t6' m',
       ms' = MS (mkR rav (Z_to_bv 64 (bv_unsigned sp1 + 96)) gp tp t0' t1' t2' q0 q1
                     (Z_to_bv 64 (mixcall h 6 (map snd args)))
                     b1 b2 b3 b4 b5 b6 b7 q2 q3 q4 q5 q6 q7 q8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc rav) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp1 - 96, bv_unsigned sp1); (0x343e0, 0x343e8)] m m'
       /\ wmono rsegs m m'
       /\ rw_cells rsegs m' 0x343e0 [C8 (Z_to_bv 64 (mixcall h 6 (map snd args)))])
    (MS (mkR ra sp1 gp tp t0 t1 t2 (Z_to_bv 64 e) s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16958) fc None m (seg_rom rsegs)).
Proof.
  intros MIX ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo e h args sp1 rav q0 q1 q2 q3 q4 q5 q6 q7 q8 MI ST LO LO2 FR EF E0 E1 EA LA HARG ES Hh.
  assert (MIX' := MIX). unfold mix_call_contract, MIX_CALL_FRAME in MIX'.
  pose proof (bv_unsigned_in_range 64 sp1) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (rw_cells_bound _ _ _ _ FR) as FB. cbn [cells_size csize Nat.add] in FB.
  pose proof (munch_refl [(bv_unsigned sp1 - 96, bv_unsigned sp1); (0x343e0, 0x343e8)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 4 step.
  call (MIX' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo 6 args).
  - exact MI.
  - exact ST.
  - lia.
  - lia.
  - exact LA.
  - rewrite unsigned_lit by lia. exact EF.
  - rewrite unsigned_lit by lia. left. lia.
  - rewrite unsigned_lit by lia. lia.
  - rewrite unsigned_lit by lia. exact EA.
  - intros k p Hk. rewrite unsigned_lit by lia. exact (HARG k p Hk).
  - eapply ro_bytes_at; [exact MI | unfold FNV_B0_ADDR; lia | rewrite length_le8; unfold FNV_B0_ADDR; lia |].
    apply ro_bytes_b_sound. vm_compute. reflexivity.
  - unfold FNV_B0_ADDR. left. lia.
  - rewrite (unsigned_lit h) by lia.
    do 13 step.
    apply evt_done. do 15 eexists. split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL01 YO10.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInv RecInvU RecKindB RecSeq RecStep
  RecGlue RecTail RecAnsB RecStubU record_c arg_s_c arg_line_c xmalloc_c sup_host_setting_c.
Local Open Scope Z_scope.

Lemma hsu_pw_in2 : forall {X} (Rl : X -> X -> Prop) l x y, pairwise Rl l -> In x l -> In y l -> x <> y ->
  Rl x y \/ Rl y x.
Proof.
  intros X Rl l. induction l as [|z l IH]; intros x y HP Hx Hy Hne; cbn in *; [destruct Hx|].
  destruct HP as [Hz HP]. destruct Hx as [<-|Hx], Hy as [<-|Hy].
  - congruence.
  - left. apply Hz. exact Hy.
  - right. apply Hz. exact Hx.
  - apply IH; assumption.
Qed.

Lemma hsu_in_rm : forall (b1 b2 : list (Z * Z)) x pn, In pn (b1 ++ x :: b2) -> pn <> x -> In pn (b1 ++ b2).
Proof.
  intros b1 b2 x pn H N. apply in_app_or in H as [H|[H|H]]; apply in_or_app; [left; exact H | congruence | right; exact H].
Qed.

Lemma hsu_assoc_nd : forall {X : Type} (l : list (X * Z)) p k n, List.NoDup (map fst l) -> In (p, k) l -> In (p, n) l ->
  k = n.
Proof.
  intros X. induction l as [|[p0 k0] l IH]; intros p k n ND H1 H2; [destruct H1|].
  cbn in ND. inversion ND as [|? ? NI ND']; subst.
  destruct H1 as [E1|H1], H2 as [E2|H2].
  - congruence.
  - injection E1 as <- <-. exfalso. apply NI. apply in_map_iff. exists (p0, n). split; [reflexivity | exact H2].
  - injection E2 as <- <-. exfalso. apply NI. apply in_map_iff. exists (p0, k). split; [reflexivity | exact H1].
  - exact (IH p k n ND' H1 H2).
Qed.

Section TMP.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GOTG : ms_got_guard B = snprintf_c.GOT_GUARD.
Hypothesis GUARDG : ms_guard B = snprintf_c.GUARD.
Hypothesis GFACT : forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis GOWN : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CTX : ctx_owned B API.

Definition sinvT (T : Z * Z) (K S : Z) (L : layout) (A : astate) (mem : word -> option byte) (md : Model)
    (O : list (Z * Z)) (Lc : layout) (Ac : astate) (mc : word -> option byte) (mdc : Model) (Rc : rstate)
    (Oc : list (Z * Z)) (bc : sbound) : Prop :=
  rjr B (aa_MR API) K S rec_area (fun pn => In pn O) L A mem md Lc Ac mc mdc /\
  g_rec_rep rsegs Lc Ac mc Rc Oc /\ owns_new L A O Oc /\
  (forall pn, In pn (blocks Lc Ac) -> (In pn (blocks L A) /\ ~ In pn O) \/ In pn Oc \/ pn = T) /\
  (forall pn, In pn (blocks L A) -> ~ In pn (blocks Lc Ac) -> In pn O) /\
  ro_agree rsegs mc /\ f18_words rsegs mc /\ res_ok_slots Ac (sb_shift bc A Ac) /\
  In T (blocks Lc Ac) /\ ~ In T Oc /\ (In T (blocks L A) -> In T O) /\ 0 < snd T.

Lemma hsu_blk_disj : forall L A mem md (x y : Z * Z), aa_MR API L A mem md -> In x (blocks L A) -> In y (blocks L A) ->
  x <> y -> ranges_disjoint x y \/ ranges_disjoint y x.
Proof.
  intros L A mem md x y HM Hx Hy N.
  exact (hsu_pw_in2 _ _ x y (mr_blocks_disjoint B _ (aa_laws API) L A mem md HM) Hx Hy N).
Qed.

Lemma hsu_blk_img : forall L A mem md a k i, aa_MR API L A mem md -> In (a, k) (blocks L A) -> 0 <= i < k ->
  ~ in_img B (a + i).
Proof using AX.
  intros L A mem md a k i HM Hin Hi. unfold blocks in Hin. apply in_map_iff in Hin as ([q k'] & E & Hq).
  cbn in E. injection E as <- <-. exact (ax_blocks_img AX L A mem md q k' i HM Hq Hi).
Qed.

Lemma hsu_keep_hi : forall Kc L A regs mem md E L' A' regs' mem' md' a,
  aa_MR API L A mem md ->
  call_post_k B (aa_MR API) Kc L A regs mem md E L' A' regs' mem' md' ->
  alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - Kc <= a < spZ regs) -> ~ E a ->
  mbyte rsegs mem' a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs mem' a).
Proof using SEGS ERRNO_LOW.
  intros Kc L A regs mem md E L' A' regs' mem' md' a HM POST Ha Hs He.
  pose proof (aa_laws API) as LAWS.
  pose proof POST as (PM & _ & _ & _ & _ & _ & _ & PF & _). rewrite SEGS in PF.
  apply PF; [left; exact Ha | intros Ho; pose proof (mr_owned_low B _ LAWS L A mem md a HM Ho); lia
            | intros Ho; pose proof (mr_owned_low B _ LAWS L' A' mem' md' a PM Ho); lia
            | unfold scratch_k; intros [H|H]; [exact (Hs H) | lia] | exact He].
Qed.

Lemma sinvT_munch : forall T K S L A mem md O Lc Ac mc mdc Rc Oc bc m' W,
  sinvT T K S L A mem md O Lc Ac mc mdc Rc Oc bc ->
  munch W mc m' -> wmono rsegs mc m' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ outside W a -> S - K <= a < S \/ fst T <= a < fst T + snd T) ->
  sinvT T K S L A mem md O Lc Ac m' mdc Rc Oc bc.
Proof using SEGS AX GOWN GOTG GUARDG.
  intros T K S L A mem md O Lc Ac mc mdc Rc Oc bc m' W SI MU WM HW.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof SI as (RJ & GR & ON & B1 & B2 & RA & F18 & RS & TI & TO & TA & TP).
  destruct (rjr_bounds B _ K S rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  pose proof RJ as (HM & HWA & HWc & HBd & HL & _).
  destruct T as [t n]. cbn [fst snd] in *.
  assert (TB : forall i, 0 <= i < n -> present mc (t + i) /\ 4096 <= t /\ t + n <= alloc_ceiling /\
                 ~ owned B Lc Ac (t + i) /\ ~ in_img B (t + i)).
  { intros i Hi. destruct (block_facts B _ LAWS Lc Ac mc mdc t n i HM TI Hi) as (P1 & P2 & P3 & P4).
    split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|].
    exact (hsu_blk_img Lc Ac mc mdc t n i HM TI Hi). }
  assert (TBl : 4096 <= t /\ t + n <= alloc_ceiling) by (destruct (TB 0 ltac:(lia)) as (_ & X1 & X2 & _); lia).
  assert (OUT : forall a, 0 <= a < 2 ^ 64 -> ~ (S - K <= a < S) -> ~ (t <= a < t + n) -> outside W a).
  { intros a Ra H1 H2. destruct (outside_dec W a) as [H|H]; [exact H|]. destruct (HW a Ra H); contradiction. }
  assert (BLK : forall q k i, In (q, k) (blocks Lc Ac) -> (q, k) <> (t, n) -> 0 <= i < k ->
            0 <= q + i < 2 ^ 64 /\ outside W (q + i)).
  { intros q k i Hin Hne Hi. destruct (block_facts B _ LAWS Lc Ac mc mdc q k i HM Hin Hi) as (_ & P2 & P3 & _).
    split; [lia|]. apply OUT; [lia | lia |].
    destruct (hsu_blk_disj Lc Ac mc mdc (q, k) (t, n) HM Hin TI Hne) as [D|D]; unfold ranges_disjoint in D;
      cbn [fst snd] in D; lia. }
  split.
  { apply (rjr_munch B (aa_MR API) SEGS LAWS K S rec_area (fun pn => In pn O) L A mem md Lc Ac mc mdc m' W RJ MU);
      [rewrite SEGS; exact WM | | | | |].
    - intros a Ra Hn Hf. destruct (HW a Ra Hn) as [H|H]; [left; exact H|]. exfalso.
      destruct (TB (a - t) ltac:(lia)) as (_ & _ & X3 & _ & X5). replace (t + (a - t)) with a in X5 by ring.
      destruct Hf as [Hf|(Hf & _)]; [lia | exact (X5 Hf)].
    - intros a Ra Hn Ho. destruct (HW a Ra Hn) as [H|H].
      + pose proof (mr_owned_low B _ LAWS Lc Ac mc mdc a HM Ho). lia.
      + destruct (TB (a - t) ltac:(lia)) as (_ & _ & _ & X4 & _). replace (t + (a - t)) with a in X4 by ring.
        exact (X4 Ho).
    - intros a Ha. apply OUT; lia.
    - intros p k i Hin Hg Hi.
      pose proof (rjr_in_cur B _ K S rec_area _ L A mem md Lc Ac mc mdc p k RJ Hin Hg) as Hc.
      pose proof (ptr_addr_stable A L Lc p k HWA Hin HL) as EP.
      assert (Hb : In (ptr_addr Lc p, k) (blocks Lc Ac))
        by (unfold blocks; exact (in_map (fun b => (ptr_addr Lc (fst b), snd b)) (user_blocks Ac) (p, k) Hc)).
      assert (Hne : (ptr_addr Lc p, k) <> (t, n)).
      { intros E. apply Hg. rewrite <- EP. rewrite E. apply TA. rewrite <- E, EP. unfold blocks.
        exact (in_map (fun b => (ptr_addr L (fst b), snd b)) (user_blocks A) (p, k) Hin). }
      rewrite <- EP. exact (proj2 (BLK _ _ i Hb Hne Hi)).
    - intros p k i Hin Hi.
      assert (Hb : In (ptr_addr Lc p, k) (blocks Lc Ac))
        by (unfold blocks; exact (in_map (fun b => (ptr_addr Lc (fst b), snd b)) (user_blocks Ac) (p, k) Hin)).
      destruct (block_facts B _ LAWS Lc Ac mc mdc _ k i HM Hb Hi) as (P1 & P2 & P3 & _).
      destruct (outside_dec W (ptr_addr Lc p + i)) as [Ho|Ho].
      + exact (munch_present W mc m' (ptr_addr Lc p + i) MU ltac:(lia) Ho P1).
      + destruct (HW (ptr_addr Lc p + i) ltac:(lia) Ho) as [H|H]; [lia|].
        apply (present_of_writable_out B SEGS m' (ptr_addr Lc p + i) ltac:(lia)).
        * destruct (TB (ptr_addr Lc p + i - t) ltac:(lia)) as (_ & _ & _ & _ & X5).
          replace (t + (ptr_addr Lc p + i - t)) with (ptr_addr Lc p + i) in X5 by ring. exact X5.
        * apply WM. exact (present_writable rsegs mc _ P1). }
  split.
  { unfold g_rec_rep in *. apply (rec_rep_keep rsegs G_REC REC_SC Lc Ac mc m' Rc Oc GR).
    - intros a Ha. assert (Hg : GLOB_LO <= a < GLOB_LO + Z.of_nat GLOB_N)
        by (unfold G_REC, REC_SC, REC_SIZE, SC_SIZE, GLOB_LO, GLOB_N in *; lia).
      apply (munch_mbyte rsegs W mc m'); [exact MU | unfold GLOB_LO, GLOB_N in Hg; lia|].
      apply OUT; [unfold GLOB_LO, GLOB_N in Hg; lia | unfold GLOB_LO, GLOB_N in Hg; lia |].
      intros Ht. destruct (TB (a - t) ltac:(lia)) as (_ & _ & _ & _ & X5). replace (t + (a - t)) with a in X5 by ring.
      exact (X5 (glob_in_img B SEGS a Hg)).
    - intros a Ha _. apply glob_writable. unfold G_REC, REC_SC, REC_SIZE, SC_SIZE, GLOB_LO, GLOB_N in *. lia.
    - intros p k i Hin Hi. pose proof (rec_rep_O_in _ _ _ _ _ _ _ _ _ GR Hin) as Hb.
      assert (Hne : (p, k) <> (t, n)) by (intros E; apply TO; rewrite <- E; exact Hin).
      destruct (BLK p k i Hb Hne Hi) as [Rr Oo]. exact (munch_mbyte rsegs W mc m' _ MU Rr Oo). }
  split; [exact ON|]. split; [exact B1|]. split; [exact B2|].
  split.
  { apply (ro_out W mc m' RA MU). intros a Ha Hro. apply OUT; [lia | lia |].
    intros Ht. destruct (TB (a - t) ltac:(lia)) as (_ & _ & _ & _ & X5). replace (t + (a - t)) with a in X5 by ring.
    exact (X5 (ro_in_img B SEGS a ltac:(lia) Hro)). }
  split.
  { apply (f18_out W mc m' F18 MU). intros i Hi.
    assert (G1 : static_owned B (snprintf_c.GOT_GUARD + i))
      by (unfold static_owned; rewrite GOTG; right; right; right; right; left; lia).
    assert (G2 : static_owned B (snprintf_c.GUARD + i))
      by (unfold static_owned; rewrite GUARDG; right; right; right; right; right; left; lia).
    unfold snprintf_c.GOT_GUARD, snprintf_c.GUARD in *.
    split; apply OUT; try lia; intros Ht.
    - destruct (TB (0x22d40 + i - t) ltac:(lia)) as (_ & _ & _ & X4 & _).
      replace (t + (0x22d40 + i - t)) with (0x22d40 + i) in X4 by ring. exact (X4 (or_intror G1)).
    - destruct (TB (0x54730 + i - t) ltac:(lia)) as (_ & _ & _ & X4 & _).
      replace (t + (0x54730 + i - t)) with (0x54730 + i) in X4 by ring. exact (X4 (or_intror G2)). }
  split; [exact RS|]. split; [exact TI|]. split; [exact TO|]. split; [exact TA | exact TP].
Qed.

Lemma sinvT_malloc : forall K S L A mem md O Lc Ac mc mdc Rc Oc bc Kc regs_c L' A' regs' m' md' p n,
  sinv B API K S L A mem md O Lc Ac mc mdc Rc Oc bc ->
  S - K <= spZ regs_c - Kc -> spZ regs_c <= S ->
  call_post_k B (aa_MR API) Kc Lc Ac regs_c mc mdc (fun _ => False) L' A' regs' m' md' ->
  0 < n -> fresh_block B p n ->
  (exists b1 b2, blocks L' A' = b1 ++ (p, n) :: b2 /\ blocks Lc Ac = b1 ++ b2) ->
  (forall q k, In (q, k) (user_blocks Ac) -> In (q, k) (user_blocks A')) ->
  blocks_kept B Lc Ac mc m' (fun _ => False) ->
  (length (st_regions Ac) <= length (st_regions A'))%nat ->
  st_init_done A' = true ->
  res_ok_slots A' (sb_malloc (sb_shift bc A Ac) n) ->
  ro_agree rsegs m' -> guard_kept B mc m' ->
  sinvT (p, n) K S L A mem md O L' A' m' md' Rc Oc bc.
Proof using SEGS AX GOWN GFACT ERRNO_LOW GOTG GUARDG.
  intros K S L A mem md O Lc Ac mc mdc Rc Oc bc Kc regs_c L' A' regs' m' md' p n
    SI HLO HHI POST Hn FB (b1 & b2 & EB' & EB) UB BK RGN INI RS' RA' GK.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof SI as (RJ & GR & ON & B1 & B2 & RA & F18 & RS).
  destruct (rjr_bounds B _ K S rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  pose proof RJ as (HM & _).
  pose proof POST as (PM & PW & PB & PL & PA & PR & PV & PF & PK & PS).
  unfold blocks_kept in BK. rewrite SEGS in BK, PF.
  pose proof FB as (FB1 & FB2 & FB3).
  assert (PIN : In (p, n) (blocks L' A')) by (rewrite EB'; apply in_elt).
  assert (PERM : Permutation (blocks L' A') ((b1 ++ b2) ++ [(p, n)])).
  { rewrite EB'. eapply Permutation_trans; [apply Permutation_sym, Permutation_middle | apply Permutation_cons_append]. }
  assert (NOTC : ~ In (p, n) (blocks Lc Ac)).
  { rewrite EB. intros H. exact (perm_not_both _ _ _ (p, n) PERM (mr_blocks_disjoint B _ LAWS L' A' m' md' PM)
                                   Hn H (or_introl eq_refl)). }
  assert (CUR : forall pn, In pn (blocks Lc Ac) -> In pn (blocks L' A')).
  { intros pn Hpn. rewrite EB'. rewrite EB in Hpn. exact (in_mid_inv b1 b2 (p, n) pn Hpn). }
  assert (RJ' : rjr B (aa_MR API) K S rec_area (fun pn => In pn O) L A mem md L' A' m' md').
  { apply (rjr_post B _ SEGS LAWS AX ERRNO_LOW K S rec_area _ L A mem md Lc Ac mc mdc Kc regs_c (fun _ => False)
             (fun _ => False) L' A' regs' m' md' RJ (call_post_k_rec B _ _ _ _ _ _ _ _ _ _ _ _ _ POST) HLO HHI).
    - intros a [].
    - intros p0 n0 _ _ _ [].
    - intros p0 n0 _ Hc Hn0. exfalso. exact (Hn0 (UB p0 n0 Hc)).
    - exact RGN.
    - intros Hf. rewrite INI in Hf. discriminate. }
  assert (GR' : g_rec_rep rsegs L' A' m' Rc Oc).
  { unfold g_rec_rep in *. apply (rec_rep_frame rsegs G_REC REC_SC Lc Ac mc Rc Oc L' A' m' GR).
    - intros a Ha.
      assert (Hg : GLOB_LO <= a < GLOB_LO + Z.of_nat GLOB_N)
        by (unfold G_REC, REC_SC, REC_SIZE, SC_SIZE, GLOB_LO, GLOB_N in *; lia).
      destruct (GFACT a (glob_in a Hg)) as (Gi & _ & _ & Ge).
      assert (NS : ~ scratch_k B Kc regs_c a).
      { unfold scratch_k. intros [H|H]; [unfold GLOB_LO, GLOB_N in Hg; lia | exact (Ge H)]. }
      destruct (PF a (or_intror Gi) (GOWN Lc Ac mc mdc a HM (glob_in a Hg)) (GOWN L' A' m' md' a PM (glob_in a Hg))
                   NS (fun H => H)) as [E1 E2].
      split; [exact E1 | exact (proj1 E2)].
    - intros q k i Hin Hi. exact (BK q k i (rec_rep_O_in _ _ _ _ _ _ _ _ _ GR Hin) (fun H => H) Hi).
    - intros pn Hpn. exact (CUR pn (rec_rep_O_in _ _ _ _ _ _ _ _ _ GR Hpn)). }
  split; [exact RJ'|]. split; [exact GR'|]. split; [exact ON|].
  split.
  { intros pn Hpn. rewrite EB' in Hpn. apply in_app_or in Hpn as [H|[H|H]].
    - destruct (B1 pn ltac:(rewrite EB; apply in_or_app; left; exact H)) as [X|X];
        [left; exact X | right; left; exact X].
    - right. right. symmetry. exact H.
    - destruct (B1 pn ltac:(rewrite EB; apply in_or_app; right; exact H)) as [X|X];
        [left; exact X | right; left; exact X]. }
  split.
  { intros pn H1 H2. apply B2; [exact H1|]. intros Hc. exact (H2 (CUR pn Hc)). }
  split; [exact RA'|].
  split.
  { destruct (ax_statics AX L' A' m' md' PM) as (_ & (g & Hg & HWg) & _).
    rewrite GUARDG, SEGS in HWg.
    apply (f18_words_after mc m' g F18); [|exact Hg | exact HWg].
    intros i Hi. pose proof (GK i Hi) as G. rewrite GOTG, SEGS in G. exact G. }
  split.
  { rewrite <- (sb_shift_trans bc A Ac A'). rewrite <- (sb_shift_add (sb_shift bc A Ac) Lc Ac L' A' b1 b2 p n EB' EB).
    exact RS'. }
  split; [exact PIN|].
  split; [intros Hin; exact (NOTC (rec_rep_O_in _ _ _ _ _ _ _ _ _ GR Hin))|].
  split; [intros Hb; exact (B2 _ Hb NOTC)|].
  exact Hn.
Qed.

Lemma sinvT_free : forall K S L A mem md O Lc Ac mc mdc Rc Oc bc regs_c L' A' regs' m' md' q n,
  sinvT (ptr_addr Lc q, n) K S L A mem md O Lc Ac mc mdc Rc Oc bc ->
  S - K <= spZ regs_c - ALLOC_STACK -> spZ regs_c <= S ->
  In (q, n) (user_blocks Ac) ->
  call_post B (aa_MR API) Lc Ac regs_c mc mdc (fun a => ptr_addr Lc q <= a < ptr_addr Lc q + n) L' A' regs' m' md' ->
  (exists b1 b2, blocks Lc Ac = b1 ++ (ptr_addr Lc q, n) :: b2 /\ blocks L' A' = b1 ++ b2) ->
  blocks_kept B Lc Ac mc m' (fun a => a = ptr_addr Lc q) ->
  ro_agree rsegs m' -> guard_kept B mc m' ->
  (forall q' k, In (q', k) (user_blocks Ac) -> q' <> q -> In (q', k) (user_blocks A')) ->
  st_init_done A' = true ->
  (length (st_regions Ac) <= length (st_regions A'))%nat ->
  res_ok_slots A' (sb_free (sb_shift bc A Ac) n) ->
  sinv B API K S L A mem md O L' A' m' md' Rc Oc bc.
Proof using SEGS AX GOWN GFACT ERRNO_LOW GOTG GUARDG.
  intros K S L A mem md O Lc Ac mc mdc Rc Oc bc regs_c L' A' regs' m' md' q n
    SI HLO HHI QIN POST (b1 & b2 & EB & EB') BK RA' GK UB INI RGN RS'.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof SI as (RJ & GR & ON & B1 & B2 & RA & F18 & RS & TI & TO & TA & TP).
  cbn [fst snd] in TP.
  destruct (rjr_bounds B _ K S rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  pose proof RJ as (HM & HWA & HWc & HBd & HL & _).
  apply (proj1 (call_post_k_alloc B (aa_MR API) _ _ _ _ _ _ _ _ _ _ _)) in POST.
  pose proof POST as (PM & PW & PB & PL & PA & PR & PV & PF & PK & PS).
  unfold blocks_kept in BK. rewrite SEGS in BK, PF.
  set (t := ptr_addr Lc q) in *.
  assert (TB : forall i, 0 <= i < n -> t + i < alloc_ceiling /\ ~ in_img B (t + i)).
  { intros i Hi. destruct (block_facts B _ LAWS Lc Ac mc mdc t n i HM TI Hi) as (_ & _ & P3 & _).
    split; [lia | exact (hsu_blk_img Lc Ac mc mdc t n i HM TI Hi)]. }
  assert (NOT' : ~ In (t, n) (blocks L' A')).
  { rewrite EB'. intros H. pose proof (blocks_mid_disjoint B _ LAWS Lc Ac mc mdc b1 b2 t n t n HM EB H). lia. }
  assert (CUR : forall pn, In pn (blocks Lc Ac) -> pn <> (t, n) -> In pn (blocks L' A')).
  { intros pn Hpn Hne. rewrite EB'. rewrite EB in Hpn. exact (hsu_in_rm b1 b2 _ pn Hpn Hne). }
  assert (BACK : forall pn, In pn (blocks L' A') -> In pn (blocks Lc Ac)).
  { intros pn Hpn. rewrite EB. rewrite EB' in Hpn. exact (in_mid_inv b1 b2 _ pn Hpn). }
  assert (RJ' : rjr B (aa_MR API) K S rec_area (fun pn => In pn O) L A mem md L' A' m' md').
  { apply (rjr_post B _ SEGS LAWS AX ERRNO_LOW K S rec_area _ L A mem md Lc Ac mc mdc ALLOC_STACK regs_c
             (fun a => t <= a < t + n) (fun _ => False) L' A' regs' m' md' RJ
             (call_post_k_rec B _ _ _ _ _ _ _ _ _ _ _ _ _ POST) HLO HHI).
    - intros a Ha Hf. exfalso. destruct (TB (a - t) ltac:(lia)) as (X1 & X2).
      replace (t + (a - t)) with a in X1, X2 by ring.
      destruct Hf as [Hf|(Hf & _)]; [lia | exact (X2 Hf)].
    - intros p0 n0 _ _ _ [].
    - intros p0 n0 Hin Hc Hn0.
      destruct (YI04.sptr_eq_dec p0 q) as [E|E]; [|exfalso; exact (Hn0 (UB p0 n0 Hc E))].
      subst p0.
      pose proof (hsu_assoc_nd (user_blocks Ac) q n0 n (user_block_ptrs_NoDup Ac HWc) Hc QIN) as <-.
      pose proof (ptr_addr_stable A L Lc q n0 HWA Hin HL) as EQ.
      assert (HB : In (ptr_addr L q, n0) (blocks L A))
        by (unfold blocks; exact (in_map (fun b => (ptr_addr L (fst b), snd b)) (user_blocks A) (q, n0) Hin)).
      rewrite <- EQ in HB |- *. exact (TA HB).
    - exact RGN.
    - intros Hf. rewrite INI in Hf. discriminate. }
  assert (GR' : g_rec_rep rsegs L' A' m' Rc Oc).
  { unfold g_rec_rep in *. apply (rec_rep_frame rsegs G_REC REC_SC Lc Ac mc Rc Oc L' A' m' GR).
    - intros a Ha.
      assert (Hg : GLOB_LO <= a < GLOB_LO + Z.of_nat GLOB_N)
        by (unfold G_REC, REC_SC, REC_SIZE, SC_SIZE, GLOB_LO, GLOB_N in *; lia).
      destruct (GFACT a (glob_in a Hg)) as (Gi & _ & _ & Ge).
      assert (NS : ~ scratch_k B ALLOC_STACK regs_c a).
      { unfold scratch_k. intros [H|H]; [unfold GLOB_LO, GLOB_N, ALLOC_STACK in *; lia | exact (Ge H)]. }
      assert (NE : ~ (t <= a < t + n)).
      { intros H. destruct (TB (a - t) ltac:(lia)) as (_ & X2). replace (t + (a - t)) with a in X2 by ring.
        exact (X2 Gi). }
      destruct (PF a (or_intror Gi) (GOWN Lc Ac mc mdc a HM (glob_in a Hg)) (GOWN L' A' m' md' a PM (glob_in a Hg))
                   NS NE) as [E1 E2].
      split; [exact E1 | exact (proj1 E2)].
    - intros a k i Hin Hi. pose proof (rec_rep_O_in _ _ _ _ _ _ _ _ _ GR Hin) as Hb.
      apply (BK a k i Hb); [|exact Hi]. intros Ea. subst a.
      pose proof (rec_rep_pos _ _ _ _ _ _ _ _ _ GR Hin) as Hk. cbn in Hk.
      pose proof (blocks_same_addr B _ LAWS Lc Ac mc mdc t k n HM Hb TI Hk TP) as ->. exact (TO Hin).
    - intros pn Hpn. apply CUR; [exact (rec_rep_O_in _ _ _ _ _ _ _ _ _ GR Hpn)|].
      intros E. apply TO. rewrite <- E. exact Hpn. }
  split; [exact RJ'|]. split; [exact GR'|]. split; [exact ON|].
  split.
  { intros pn Hpn. destruct (B1 pn (BACK pn Hpn)) as [X|[X|X]]; [left; exact X | right; exact X |].
    exfalso. apply NOT'. rewrite <- X. exact Hpn. }
  split.
  { intros pn H1 H2. destruct (in_dec pair_dec pn (blocks Lc Ac)) as [Hc|Hc]; [|exact (B2 pn H1 Hc)].
    destruct (pair_dec pn (t, n)) as [E|E]; [subst pn; exact (TA H1) | exfalso; exact (H2 (CUR pn Hc E))]. }
  split; [exact RA'|].
  split.
  { destruct (ax_statics AX L' A' m' md' PM) as (_ & (g & Hg & HWg) & _).
    rewrite GUARDG, SEGS in HWg.
    apply (f18_words_after mc m' g F18); [|exact Hg | exact HWg].
    intros i Hi. pose proof (GK i Hi) as G. rewrite GOTG, SEGS in G. exact G. }
  rewrite <- (sb_shift_trans bc A Ac A'). rewrite <- (sb_shift_del (sb_shift bc A Ac) Lc Ac L' A' b1 b2 t n EB EB').
  exact RS'.
Qed.

Lemma sinvT_arg : forall T K S L A mem md O Lc Ac mc mdc Rp fn As Oc bc Kc regs_c Ec L' A' regs' m' md' x p k,
  sinvT T K S L A mem md O Lc Ac mc mdc (rec_record Rp fn As) Oc bc ->
  (length As < 6)%nat ->
  S - K <= spZ regs_c - Kc -> spZ regs_c <= S ->
  call_post_k B (aa_MR API) Kc Lc Ac regs_c mc mdc Ec L' A' regs' m' md' ->
  (forall a, Ec a ->
     rec_entry G_REC REC_SC Rp + CALL_OFF_NARGS <= a < rec_entry G_REC REC_SC Rp + CALL_OFF_NARGS + 4 \/
     rec_entry G_REC REC_SC Rp + CALL_OFF_ARGS + 8 * Z.of_nat (length As) <= a <
       rec_entry G_REC REC_SC Rp + CALL_OFF_ARGS + 8 * Z.of_nat (length As) + 8 \/
     p <= a < p + k) ->
  p <> 0 -> fresh_block B p k ->
  (exists b1 b2, blocks L' A' = b1 ++ (p, k) :: b2 /\ blocks Lc Ac = b1 ++ b2) ->
  (forall q n, In (q, n) (user_blocks Ac) -> In (q, n) (user_blocks A')) ->
  blocks_kept B Lc Ac mc m' (fun _ => False) ->
  (length (st_regions Ac) <= length (st_regions A'))%nat ->
  bytes_at rsegs m' (rec_entry G_REC REC_SC Rp + CALL_OFF_NARGS) (le4 (Z_to_bv 64 (Z.of_nat (length As) + 1))) ->
  bytes_at rsegs m' (rec_entry G_REC REC_SC Rp + CALL_OFF_ARGS + 8 * Z.of_nat (length As)) (le8 (Z_to_bv 64 p)) ->
  bytes_at rsegs m' p (x ++ [Z_to_bv 8 0]) ->
  no0 x -> Z.of_nat (length x) <= LMAX -> Z.of_nat (length x) + 1 <= k <= LMAX + 2 ->
  st_init_done A' = true ->
  res_ok_slots A' (sb_malloc (sb_shift bc A Ac) k) ->
  ro_agree rsegs m' -> f18_words rsegs m' ->
  sinvT T K S L A mem md O L' A' m' md' (rec_record Rp fn (As ++ [x])) (Oc ++ [(p, k)]) bc.
Proof using SEGS AX GOWN GFACT ERRNO_LOW.
  intros T K S L A mem md O Lc Ac mc mdc Rp fn As Oc bc Kc regs_c Ec L' A' regs' m' md' x p k
    SI H6 HLO HHI POST HEc Hp0 FB (b1 & b2 & EB' & EB) UB BK RGN BN BS BX Hno Hlx Hsz INI RS' RA' F18'.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof SI as (RJ & GR & ON & B1 & B2 & RA & F18 & RS & TI & TO & TA & TP).
  destruct (rjr_bounds B _ K S rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  pose proof RJ as (HM & _).
  pose proof POST as (PM & PW & PB & PL & PA & PR & PV & PF & PK & PS).
  unfold blocks_kept in BK. rewrite SEGS in BK, PF.
  pose proof FB as (FB1 & FB2 & FB3).
  assert (HN : (length (r_calls Rp) <= 16)%nat)
    by exact (rec_record_calls Rp fn As (rec_rep_calls_le _ _ _ _ _ _ _ _ GR)).
  destruct (rec_entry_bounds Rp HN) as (ER1 & ER2 & _).
  set (e := rec_entry G_REC REC_SC Rp) in *.
  assert (Hk : 0 < k) by lia.
  assert (PIN : In (p, k) (blocks L' A')) by (rewrite EB'; apply in_elt).
  assert (PERM : Permutation (blocks L' A') ((b1 ++ b2) ++ [(p, k)])).
  { rewrite EB'. eapply Permutation_trans; [apply Permutation_sym, Permutation_middle | apply Permutation_cons_append]. }
  assert (NOTC : ~ In (p, k) (blocks Lc Ac)).
  { rewrite EB. intros H. exact (perm_not_both _ _ _ (p, k) PERM (mr_blocks_disjoint B _ LAWS L' A' m' md' PM)
                                   Hk H (or_introl eq_refl)). }
  assert (CUR : forall pn, In pn (blocks Lc Ac) -> In pn (blocks L' A')).
  { intros pn Hpn. rewrite EB'. rewrite EB in Hpn. exact (in_mid_inv b1 b2 (p, k) pn Hpn). }
  assert (APT : forall lo n, 0 < n -> (forall a, lo <= a < lo + n -> in_img B a) -> iv_apart p k lo n).
  { intros lo n Hn HI. unfold iv_apart. destruct (Z_le_gt_dec (p + k) lo) as [H|H]; [left; exact H|].
    destruct (Z_le_gt_dec (lo + n) p) as [H'|H']; [right; exact H'|]. exfalso.
    apply (FB3 (Z.max p lo - p)); [lia|]. replace (p + (Z.max p lo - p)) with (Z.max p lo) by lia. apply HI. lia. }
  assert (RIMG' : forall a, REC_SC <= a < G_REC + REC_SIZE -> GLOB_LO <= a < GLOB_LO + Z.of_nat GLOB_N)
    by (intros a Ha; unfold REC_SC, G_REC, REC_SIZE, GLOB_LO, GLOB_N in *; lia).
  assert (RJ' : rjr B (aa_MR API) K S rec_area (fun pn => In pn O) L A mem md L' A' m' md').
  { apply (rjr_post B _ SEGS LAWS AX ERRNO_LOW K S rec_area _ L A mem md Lc Ac mc mdc Kc regs_c Ec (fun _ => False)
             L' A' regs' m' md' RJ (call_post_k_rec B _ _ _ _ _ _ _ _ _ _ _ _ _ POST) HLO HHI).
    - intros a Ha Hf. destruct (HEc a Ha) as [H|[H|H]].
      + unfold rec_area, G_REC, REC_SC, REC_SIZE, SC_SIZE, CALL_SIZE, CALL_OFF_NARGS in *. split; lia.
      + unfold rec_area, G_REC, REC_SC, REC_SIZE, SC_SIZE, CALL_SIZE, CALL_OFF_ARGS in *. split; lia.
      + exfalso. destruct Hf as [Hf|(Hi & _)]; [lia|].
        apply (FB3 (a - p)); [lia|]. replace (p + (a - p)) with a by ring. exact Hi.
    - intros p0 n0 _ _ _ [].
    - intros p0 n0 _ Hc Hn. exfalso. exact (Hn (UB p0 n0 Hc)).
    - exact RGN.
    - intros Hf. rewrite INI in Hf. discriminate. }
  assert (NQ : ~ In p (map fst Oc)).
  { intros Hq. apply in_map_iff in Hq as ([q k'] & Eq & Hq). cbn in Eq. subst q.
    pose proof (rec_rep_O_in _ _ _ _ _ _ _ _ _ GR Hq) as Hb.
    pose proof (rec_rep_pos _ _ _ _ _ _ _ _ _ GR Hq) as Hk'. cbn in Hk'.
    pose proof (blocks_same_addr B _ LAWS L' A' m' md' p k k' PM PIN (CUR _ Hb) Hk Hk') as <-.
    exact (NOTC Hb). }
  assert (GR' : g_rec_rep rsegs L' A' m' (rec_record Rp fn (As ++ [x])) (Oc ++ [(p, k)])).
  { unfold g_rec_rep in *.
    apply (rec_rep_arg rsegs G_REC REC_SC Lc Ac mc L' A' m' Rp fn As Oc x p k GR H6 BN BS).
    - intros a Ha N1 N2.
      assert (Hg : GLOB_LO <= a < GLOB_LO + Z.of_nat GLOB_N)
        by (apply RIMG'; unfold G_REC, REC_SC, REC_SIZE, SC_SIZE in *; lia).
      destruct (GFACT a (glob_in a Hg)) as (Gi & _ & _ & Ge).
      assert (NS : ~ scratch_k B Kc regs_c a).
      { unfold scratch_k. intros [H|H]; [unfold GLOB_LO, GLOB_N in Hg; lia | exact (Ge H)]. }
      assert (NE : ~ Ec a).
      { intros HE. destruct (HEc a HE) as [H|[H|H]]; [contradiction | contradiction |].
        apply (FB3 (a - p)); [lia|]. replace (p + (a - p)) with a by ring. exact Gi. }
      exact (proj1 (PF a (or_intror Gi) (GOWN Lc Ac mc mdc a HM (glob_in a Hg)) (GOWN L' A' m' md' a PM (glob_in a Hg))
                       NS NE)).
    - intros a Ha _. apply glob_writable. unfold G_REC, REC_SC, REC_SIZE, SC_SIZE, GLOB_LO, GLOB_N in *. lia.
    - intros pn Hpn. pose proof (rec_rep_O_in _ _ _ _ _ _ _ _ _ GR Hpn) as Hb.
      split; [exact (CUR pn Hb)|]. intros i Hi. destruct pn as [q n]. cbn [fst snd] in *.
      exact (BK q n i Hb (fun H => H) Hi).
    - exact NQ.
    - exact Hp0.
    - exact PIN.
    - exact Hno.
    - exact Hlx.
    - exact Hsz.
    - exact BX.
    - apply APT; [unfold REC_SIZE; lia|]. intros a Ha. apply (glob_in_img B SEGS).
      unfold G_REC, REC_SIZE, GLOB_LO, GLOB_N in *. lia.
    - apply APT; [unfold SC_SIZE; lia|]. intros a Ha. apply (glob_in_img B SEGS).
      unfold REC_SC, SC_SIZE, GLOB_LO, GLOB_N in *. lia. }
  split; [exact RJ'|]. split; [exact GR'|].
  split.
  { intros pn Hpn. apply in_app_or in Hpn as [H|[<-|[]]]; [exact (ON pn H)|].
    destruct (in_dec pair_dec (p, k) O) as [H|H]; [left; exact H | right; intros Hb].
    destruct (in_dec pair_dec (p, k) (blocks Lc Ac)) as [Hc|Hc]; [exact (NOTC Hc) | exact (H (B2 _ Hb Hc))]. }
  split.
  { intros pn Hpn. rewrite EB' in Hpn. apply in_app_or in Hpn as [H|[H|H]].
    - destruct (B1 pn ltac:(rewrite EB; apply in_or_app; left; exact H)) as [X|[X|X]];
        [left; exact X | right; left; apply in_or_app; left; exact X | right; right; exact X].
    - subst pn. right. left. apply in_or_app. right. left. reflexivity.
    - destruct (B1 pn ltac:(rewrite EB; apply in_or_app; right; exact H)) as [X|[X|X]];
        [left; exact X | right; left; apply in_or_app; left; exact X | right; right; exact X]. }
  split.
  { intros pn H1 H2. apply B2; [exact H1|]. intros Hc. exact (H2 (CUR pn Hc)). }
  split; [exact RA'|]. split; [exact F18'|].
  split.
  { rewrite <- (sb_shift_trans bc A Ac A'). rewrite <- (sb_shift_add (sb_shift bc A Ac) Lc Ac L' A' b1 b2 p k EB' EB).
    exact RS'. }
  split; [exact (CUR T TI)|].
  split.
  { intros Hin. apply in_app_or in Hin as [H|[H|[]]]; [exact (TO H)|]. rewrite <- H in TI. exact (NOTC TI). }
  split; [exact TA | exact TP].
Qed.

End TMP.

Definition hsu_kx (xs : list Z) (R R' : bvmap 5 word) : Prop :=
  forall r, callee_saved r -> ~ In r xs -> getr R' (Z_to_bv 5 r) = getr R (Z_to_bv 5 r).

Lemma hsu_kx_trans : forall xs R1 R2 R3, hsu_kx xs R1 R2 -> hsu_kx xs R2 R3 -> hsu_kx xs R1 R3.
Proof. intros xs R1 R2 R3 H1 H2 r Hr N. rewrite (H2 r Hr N). exact (H1 r Hr N). Qed.

Lemma hsu_kx_of_pres : forall xs R R', regs_preserved R R' -> hsu_kx xs R R'.
Proof. intros xs R R' H r Hr _. exact (H r Hr). Qed.

Lemma hsu_kx_pres : forall xs R R', hsu_kx xs R R' ->
  (forall r, In r xs -> getr R' (Z_to_bv 5 r) = getr R (Z_to_bv 5 r)) -> regs_preserved R R'.
Proof.
  intros xs R R' K E r Hr. destruct (in_dec Z.eq_dec r xs) as [H|H]; [exact (E r H) | exact (K r Hr H)].
Qed.

Ltac hsu_kx_one X :=
  first [ exfalso; match goal with N : ~ In _ _ |- _ => apply N end; cbn [In]; lia
        | match goal with |- getr _ ?k = _ => rewrite (getr_of_eqv _ _ k X eq_refl) end;
          simp_regs; first [reflexivity | unfold getr; reflexivity] ].

Ltac hsu_kx_tac X :=
  let rr := fresh "rr" in let Hrr := fresh "Hrr" in let Nrr := fresh "Nrr" in
  intros rr Hrr Nrr; unfold callee_saved in Hrr;
  assert (CC : rr = 2 \/ rr = 3 \/ rr = 4 \/ rr = 8 \/ rr = 9 \/ rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/
               rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia;
  clear Hrr;
  repeat (destruct CC as [CC|CC]; [subst rr; hsu_kx_one X|]);
  subst rr; hsu_kx_one X.

Lemma hsu_nra_apart : forall s Ln lo hi, (forall a, s <= a < s + Ln -> ~ rec_area a) ->
  REC_SC <= lo -> hi <= G_REC + REC_SIZE -> lo < hi -> 0 < Ln -> s + Ln <= lo \/ hi <= s.
Proof.
  intros s Ln lo hi H H1 H2 H3 H4. destruct (Z_le_gt_dec (s + Ln) lo) as [D|D]; [left; exact D|].
  destruct (Z_le_gt_dec hi s) as [D'|D']; [right; exact D'|]. exfalso.
  unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE in *.
  destruct (Z_le_gt_dec s lo) as [D1|D1].
  - apply (H lo); [lia|]. destruct (Z_lt_ge_dec lo 213032); [left | right]; lia.
  - apply (H s); [lia|]. destruct (Z_lt_ge_dec s 213032); [left | right]; lia.
Qed.

Lemma hsu_pad_le : forall e c a, e <= c -> a < e + (- e) mod 8 -> a < 8 * ((c + 7) / 8).
Proof.
  intros e c a H1 H2.
  pose proof (Z.div_mod (- e) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (- e) 8 ltac:(lia)).
  pose proof (Z.div_mod (c + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (c + 7) 8 ltac:(lia)).
  lia.
Qed.

Lemma hsu_present : forall segs m a, present m a -> mbyte segs m a <> None.
Proof. intros segs m a [b E]. unfold mbyte. rewrite E. discriminate. Qed.

Lemma hsu_combine_snd : forall (X Y : Type) (l1 : list X) (l2 : list Y), length l1 = length l2 ->
  map snd (combine l1 l2) = l2.
Proof.
  intros X Y l1. induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H |- *;
    [reflexivity | discriminate | discriminate | rewrite (IH l2 ltac:(lia)); reflexivity].
Qed.

Lemma hsu_nth_combine : forall (X Y : Type) (l1 : list X) (l2 : list Y) k a b,
  nth_error (combine l1 l2) k = Some (a, b) -> nth_error l1 k = Some a /\ nth_error l2 k = Some b.
Proof.
  intros X Y l1. induction l1 as [|x l1 IH]; intros [|y l2] [|k] a b H; cbn in H |- *; try discriminate.
  - injection H as -> ->. split; reflexivity.
  - exact (IH l2 k a b H).
Qed.

Lemma hsu_len_eq : forall toks, hsu_len toks = sup_host_setting_len toks.
Proof. reflexivity. Qed.

Section P.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis FREE_PC : ms_free B = 0x18ad0.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GOTG : ms_got_guard B = snprintf_c.GOT_GUARD.
Hypothesis GUARDG : ms_guard B = snprintf_c.GUARD.
Hypothesis GFACT : forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis GOWN : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CTX : ctx_owned B API.
Hypothesis SLACK : block_slack_present B API.
Hypothesis REC : record_contract B API.
Hypothesis ARGL : arg_line_contract B API.
Hypothesis ARGS : forall fx0 : YK11.FPState, arg_s_contract (fx := fx0) B API.
Hypothesis SNP : snprintf_contract.
Hypothesis XM : forall fx0 : YK11.FPState, xmalloc_contract (fx := fx0) B API.
Hypothesis FREE : forall fx0 : YK11.FPState, free_contract (fx := fx0) B API.
Hypothesis SLEN : strlen_contract.
Hypothesis SCAT : strcat_contract.
Hypothesis MIX : mix_call_contract.

Lemma hsu_mc_arg : forall Lc Ac mc mdc e k pn s lo hi,
  aa_MR API Lc Ac mc mdc -> ro_agree rsegs mc ->
  bytes_at rsegs mc (e + CALL_OFF_ARGS + 8 * Z.of_nat k) (le8 (Z_to_bv 64 (fst pn))) ->
  In pn (blocks Lc Ac) -> Z.of_nat (length s) + 1 <= snd pn ->
  bytes_at rsegs mc (fst pn) (s ++ [Z_to_bv 8 0]) -> no0 s -> Z.of_nat (length s) <= LMAX ->
  alloc_ceiling <= lo ->
  mc_arg (normalize rsegs mc) lo hi e k (Z_to_bv 64 (fst pn), s).
Proof using SEGS SLACK.
  intros Lc Ac mc mdc e k [q n] s lo hi HM RA BP Hb Hn BS N0 LX HLO. cbn [fst snd] in *.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_value as ACV.
  pose proof Hb as Hb0.
  unfold blocks in Hb. apply in_map_iff in Hb as ([u n'] & Eu & Hu). cbn in Eu. injection Eu as E0 E2. subst n'.
  assert (E1 : ptr_addr Lc u = q) by (rewrite <- E0; reflexivity). clear E0.
  pose proof (bytes_at_bound _ _ _ _ BS) as BB. rewrite length_app in BB. cbn [length] in BB.
  destruct (mr_blocks B _ LAWS Lc Ac mc mdc u n 0 HM Hu ltac:(lia)) as (_ & HQ1 & HQ2 & _). rewrite E1 in HQ1, HQ2.
  pose proof (Z.mod_pos_bound (- (q + Z.of_nat (length s) + 1)) 8 ltac:(lia)) as Hpad.
  assert (CE : forall a, a < q + Z.of_nat (length s) + 1 + (- (q + Z.of_nat (length s) + 1)) mod 8 ->
            a < alloc_ceiling).
  { intros a Ha. pose proof (hsu_pad_le (q + Z.of_nat (length s) + 1) (q + n) a ltac:(lia) Ha) as X.
    pose proof (Z.div_mod (q + n + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (q + n + 7) 8 ltac:(lia)).
    pose proof (Z.div_mod alloc_ceiling 4096 ltac:(lia)). destruct ACV as (_ & ACM). lia. }
  destruct (rs_bytes_pad rsegs mc q (s ++ [Z_to_bv 8 0])
              (Z.to_nat ((- (q + Z.of_nat (length s) + 1)) mod 8)) BS) as (sl & LS & BS2).
  - rewrite length_app. cbn [length].
    pose proof (CE (q + Z.of_nat (length s) + 1 + (- (q + Z.of_nat (length s) + 1)) mod 8 - 1) ltac:(lia)). lia.
  - intros j Hj. rewrite length_app. cbn [length].
    destruct (Z_lt_le_dec (q + Z.of_nat (length s + 1) + Z.of_nat j) (q + n)) as [Hl|Hl].
    + destruct (mr_blocks B _ LAWS Lc Ac mc mdc u n (Z.of_nat (length s + 1) + Z.of_nat j) HM Hu ltac:(lia))
        as (Hp & _).
      rewrite E1 in Hp. apply hsu_present. replace (q + Z.of_nat (length s + 1) + Z.of_nat j)
        with (q + (Z.of_nat (length s + 1) + Z.of_nat j)) by ring. exact Hp.
    + apply hsu_present. apply (SLACK Lc Ac mc mdc q n _ HM Hb0). split; [exact Hl|].
      apply (hsu_pad_le (q + Z.of_nat (length s) + 1) (q + n)); lia.
  - unfold mc_arg. cbn [fst snd]. rewrite unsigned_lit by lia.
    split; [apply bytes_at_normalize; [exact RA | unfold CALL_OFF_ARGS in BP; exact BP]|].
    split; [exact N0|]. split; [exact LX|]. split; [lia|]. split; [lia|].
    exists sl. rewrite <- app_assoc in BS2. cbn [app] in BS2.
    split; [apply bytes_at_normalize; [exact RA | exact BS2]|].
    rewrite LS, Z2Nat.id by lia. split; [lia|]. left.
    pose proof (CE (q + Z.of_nat (length s) + 1 + (- (q + Z.of_nat (length s) + 1)) mod 8 - 1) ltac:(lia)). lia.
Qed.

Lemma hsu_tstr : forall T K S L A mem md O Lc Ac mc mdc Rc Oc bc p x,
  sinvT B API T K S L A mem md O Lc Ac mc mdc Rc Oc bc -> fst T mod 8 = 0 ->
  ro_agree rsegs mem -> str_arg B L A O S K mem p (Some x) ->
  exists sl, bytes_at rsegs mc p (x ++ Z_to_bv 8 0 :: sl) /\ no0 x /\ 0 <= p /\
    (- (p + Z.of_nat (length x) + 1)) mod 8 = Z.of_nat (length sl) /\
    (p + Z.of_nat (length (x ++ Z_to_bv 8 0 :: sl)) <= S - K \/ S <= p) /\
    (p + Z.of_nat (length (x ++ Z_to_bv 8 0 :: sl)) <= fst T \/ fst T + snd T <= p).
Proof using SEGS ERRNO_LOW SLACK AX.
  intros T K S L A mem md O Lc Ac mc mdc Rc Oc bc p x SI TA RA H.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof SI as (RJ & _ & _ & _ & B2 & RAc & _ & _ & TI & _ & TAo & TP).
  destruct (rjr_bounds B _ K S rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  destruct H as (Hp0 & N0 & LX & slack & BS & AL & DJ & HOME & NRA).
  rewrite SEGS in BS.
  pose proof RJ as (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & HF & _ & HK & _).
  rewrite SEGS in HF, HK.
  destruct T as [t nT]. cbn [fst snd] in *.
  destruct (block_facts B _ LAWS Lc Ac mc mdc t nT 0 HM TI ltac:(lia)) as (_ & T1 & T2 & _).
  pose proof (bytes_at_bound _ _ _ _ BS) as BB. rewrite length_app in BB. cbn [length] in BB.
  rewrite length_app in DJ, NRA. cbn [length] in DJ, NRA.
  set (pad := (- (p + Z.of_nat (length x) + 1)) mod 8) in *.
  assert (PADR : 0 <= pad < 8) by (unfold pad; apply Z.mod_pos_bound; lia).
  assert (PADA : (p + Z.of_nat (length x) + 1 + pad) mod 8 = 0).
  { unfold pad. rewrite Zplus_mod_idemp_r. replace (p + Z.of_nat (length x) + 1 + - (p + Z.of_nat (length x) + 1)) with 0
      by ring. reflexivity. }
  assert (PR0 : forall j, 0 <= j < pad -> mbyte rsegs mem (p + Z.of_nat (length x) + 1 + j) <> None).
  { intros j Hj E. pose proof BS as (_ & _ & HB).
    assert (Hlt : (Z.to_nat (Z.of_nat (length x) + 1 + j) < length (x ++ Z_to_bv 8 0 :: slack))%nat)
      by (rewrite length_app; cbn [length]; lia).
    specialize (HB (Z.to_nat (Z.of_nat (length x) + 1 + j)) Hlt).
    change (mrd rsegs mem (wa (p + Z.of_nat (Z.to_nat (Z.of_nat (length x) + 1 + j)))))
      with (mbyte rsegs mem (p + Z.of_nat (Z.to_nat (Z.of_nat (length x) + 1 + j)))) in HB.
    rewrite Z2Nat.id in HB by lia.
    replace (p + (Z.of_nat (length x) + 1 + j)) with (p + Z.of_nat (length x) + 1 + j) in HB by ring.
    rewrite E in HB. symmetry in HB. apply nth_error_None in HB. lia. }
  assert (TX0 : bytes_at rsegs mem p (x ++ [Z_to_bv 8 0])).
  { replace (x ++ Z_to_bv 8 0 :: slack) with ((x ++ [Z_to_bv 8 0]) ++ slack) in BS
      by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app in BS. exact (proj1 BS). }
  assert (LX1 : Z.of_nat (length (x ++ [Z_to_bv 8 0])) = Z.of_nat (length x) + 1)
    by (rewrite length_app; cbn [length]; lia).
  assert (SAME : (forall i, 0 <= i < Z.of_nat (length x) + 1 + pad -> mbyte rsegs mc (p + i) = mbyte rsegs mem (p + i)) ->
                 bytes_at rsegs mc p (x ++ [Z_to_bv 8 0]) /\
                 (forall j, 0 <= j < pad -> mbyte rsegs mc (p + Z.of_nat (length x) + 1 + j) <> None)).
  { intros KE. split.
    - apply (bytes_at_transfer rsegs mem); [exact TX0|]. intros i Hi. rewrite LX1 in Hi. apply KE. lia.
    - intros j Hj. replace (p + Z.of_nat (length x) + 1 + j) with (p + (Z.of_nat (length x) + 1 + j)) by ring.
      rewrite KE by lia. replace (p + (Z.of_nat (length x) + 1 + j)) with (p + Z.of_nat (length x) + 1 + j) by ring.
      exact (PR0 j Hj). }
  assert (CASES : bytes_at rsegs mc p (x ++ [Z_to_bv 8 0]) /\
                  (forall j, 0 <= j < pad -> mbyte rsegs mc (p + Z.of_nat (length x) + 1 + j) <> None) /\
                  (p + Z.of_nat (length x) + 1 + pad <= t \/ t + nT <= p)).
  { destruct HOME as [(H1 & H2) | [(q & k & Hq & Hnq & H1 & H2) | (H1 & H2 & H3)]].
    - assert (KE : forall i, 0 <= i < Z.of_nat (length x) + 1 + pad -> mbyte rsegs mc (p + i) = mbyte rsegs mem (p + i)).
      { intros i Hi. refine (proj1 (HF (p + i) _ _ _ _)).
        - unfold free_a. left. lia.
        - lia.
        - lia.
        - intros Hr. unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE in Hr. lia. }
      destruct (SAME KE) as [S1 S2]. split; [exact S1 | split; [exact S2 | right; lia]].
    - assert (NG : ~ In (q, k) O).
      { intros Ho. apply Hnq. apply in_map_iff. exists (q, k). split; [reflexivity | exact Ho]. }
      assert (QC : In (q, k) (blocks Lc Ac)).
      { destruct (in_dec pair_dec (q, k) (blocks Lc Ac)) as [Hc|Hc]; [exact Hc|]. exfalso. exact (NG (B2 _ Hq Hc)). }
      assert (NTq : (q, k) <> (t, nT)).
      { intros E. apply NG. rewrite E. apply TAo. rewrite <- E. exact Hq. }
      assert (DT : q + k <= t \/ t + nT <= q).
      { destruct (hsu_blk_disj B API Lc Ac mc mdc (q, k) (t, nT) HM QC TI NTq) as [D|D];
          unfold ranges_disjoint in D; cbn [fst snd] in D; lia. }
      pose proof Hq as Hq'. unfold blocks in Hq'. apply in_map_iff in Hq' as ([pp k'] & E & Hp). cbn [fst snd] in E.
      injection E as E1 E2. subst k'.
      split.
      { apply (bytes_at_transfer rsegs mem); [exact TX0|]. intros i Hi. rewrite LX1 in Hi.
        assert (Hng : ~ (fun pn => In pn O) (ptr_addr L pp, k)) by (intros Hg; apply NG; rewrite <- E1; exact Hg).
        pose proof (HK pp k (p + i - q) Hp Hng ltac:(lia)) as E. rewrite E1 in E.
        replace (q + (p + i - q)) with (p + i) in E by ring. exact E. }
      split.
      { intros j Hj.
        assert (PRc : present mc (p + Z.of_nat (length x) + 1 + j)).
        { destruct (Z_lt_ge_dec (p + Z.of_nat (length x) + 1 + j) (q + k)) as [Hlt|Hge].
          - replace (p + Z.of_nat (length x) + 1 + j) with (q + (p + Z.of_nat (length x) + 1 + j - q)) by ring.
            exact (proj1 (block_facts B _ LAWS Lc Ac mc mdc q k (p + Z.of_nat (length x) + 1 + j - q) HM QC ltac:(lia))).
          - apply (SLACK Lc Ac mc mdc q k _ HM QC). split; [lia|]. Z.div_mod_to_equations. lia. }
        destruct PRc as [bb E]. unfold mbyte. rewrite E. discriminate. }
      destruct DT as [D|D]; [left | right; lia].
      pose proof (Z.div_mod (p + Z.of_nat (length x) + 1 + pad) 8 ltac:(lia)) as M1.
      pose proof (Z.div_mod t 8 ltac:(lia)) as M2. rewrite PADA in M1. rewrite TA in M2. lia.
    - pose proof H3 as H3'. rewrite SEGS in H3'.
      assert (ROALL : forall i, 0 <= i < Z.of_nat (length x) + 1 + pad -> ro_addr rsegs (Z_to_bv 64 (p + i)) = true).
      { intros i Hi. destruct (Z_lt_ge_dec i (Z.of_nat (length x) + 1)) as [Hl|Hl]; [exact (H3' i ltac:(lia))|].
        pose proof (H3' (Z.of_nat (length x)) ltac:(lia)) as Hlast. apply rs_ro_rsegs in Hlast; [|lia].
        apply rs_ro_rsegs; [lia|]. Z.div_mod_to_equations. lia. }
      assert (KE : forall i, 0 <= i < Z.of_nat (length x) + 1 + pad -> mbyte rsegs mc (p + i) = mbyte rsegs mem (p + i)).
      { intros i Hi. pose proof (ROALL i Hi) as RO.
        rewrite (mbyte_ro_agree _ _ _ RAc RO), (mbyte_ro_agree _ _ _ RA RO). reflexivity. }
      destruct (SAME KE) as [S1 S2].
      split; [exact S1 | split; [exact S2|]].
      destruct (Z_le_gt_dec (p + Z.of_nat (length x) + 1 + pad) t) as [D1|D1]; [left; exact D1|].
      destruct (Z_le_gt_dec (t + nT) p) as [D2|D2]; [right; exact D2|]. exfalso.
      apply (hsu_blk_img B API AX Lc Ac mc mdc t nT (Z.max p t - t) HM TI ltac:(lia)).
      replace (t + (Z.max p t - t)) with (Z.max p t) by ring.
      apply (ro_in_img B SEGS); [lia|]. replace (Z.max p t) with (p + (Z.max p t - p)) by ring. apply ROALL. lia. }
  destruct CASES as (TX & PADP & DT).
  destruct (rs_bytes_pad rsegs mc p (x ++ [Z_to_bv 8 0]) (Z.to_nat pad) TX) as (sl & SL & BS').
  { rewrite LX1, Z2Nat.id by lia. lia. }
  { intros j Hj. rewrite LX1. replace (p + (Z.of_nat (length x) + 1) + Z.of_nat j)
      with (p + Z.of_nat (length x) + 1 + Z.of_nat j) by ring. apply PADP. lia. }
  rewrite <- app_assoc in BS'. cbn [app] in BS'.
  exists sl.
  split; [exact BS'|]. split; [exact N0|]. split; [lia|].
  split; [change ((- (p + Z.of_nat (length x) + 1)) mod 8) with pad; rewrite SL, Z2Nat.id by lia; reflexivity|].
  split; [rewrite length_app; cbn [length]; rewrite SL; destruct DJ as [D|D]; [left; lia | right; exact D]|].
  rewrite length_app; cbn [length]; rewrite SL. lia.
Qed.

Lemma hsu_home_T : forall T K S L A mem md O Lc Ac mc mdc Rc Oc bc s n,
  sinvT B API T K S L A mem md O Lc Ac mc mdc Rc Oc bc -> 0 < n ->
  buf_home B L A O S s n -> s + n <= fst T \/ fst T + snd T <= s.
Proof using SEGS AX.
  intros T K S L A mem md O Lc Ac mc mdc Rc Oc bc s n SI Hn HOME.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof SI as (RJ & _ & _ & _ & B2 & _ & _ & _ & TI & _ & TAo & TP).
  destruct (rjr_bounds B _ K S rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  pose proof RJ as (HM & _).
  destruct T as [t nT]. cbn [fst snd] in *.
  destruct (block_facts B _ LAWS Lc Ac mc mdc t nT 0 HM TI ltac:(lia)) as (_ & T1 & T2 & _).
  unfold buf_home in HOME. rewrite SEGS in HOME.
  destruct HOME as [(H1 & H2) | [(q & k & Hq & Hnq & H1 & H2) | (H1 & H2 & H3)]].
  - right. lia.
  - assert (NG : ~ In (q, k) O).
    { intros Ho. apply Hnq. apply in_map_iff. exists (q, k). split; [reflexivity | exact Ho]. }
    assert (QC : In (q, k) (blocks Lc Ac)).
    { destruct (in_dec pair_dec (q, k) (blocks Lc Ac)) as [Hc|Hc]; [exact Hc|]. exfalso. exact (NG (B2 _ Hq Hc)). }
    assert (NTq : (q, k) <> (t, nT)).
    { intros E. apply NG. rewrite E. apply TAo. rewrite <- E. exact Hq. }
    destruct (hsu_blk_disj B API Lc Ac mc mdc (q, k) (t, nT) HM QC TI NTq) as [D|D];
      unfold ranges_disjoint in D; cbn [fst snd] in D; lia.
  - destruct (Z_le_gt_dec (s + n) t) as [D1|D1]; [left; exact D1|].
    destruct (Z_le_gt_dec (t + nT) s) as [D2|D2]; [right; exact D2|]. exfalso.
    apply (hsu_blk_img B API AX Lc Ac mc mdc t nT (Z.max s t - t) HM TI ltac:(lia)).
    replace (t + (Z.max s t - t)) with (Z.max s t) by ring.
    apply (ro_in_img B SEGS); [lia|]. replace (Z.max s t) with (s + (Z.max s t - s)) by ring. apply H3. lia.
Qed.

Lemma hsu_str : forall K S L A mem md O Lc Ac mc mdc Rc Oc bc p x,
  sinv B API K S L A mem md O Lc Ac mc mdc Rc Oc bc ->
  ro_agree rsegs mem ->
  str_arg B L A O S K mem p (Some x) ->
  exists slack, 0 <= p < 2 ^ 64 /\ p <> 0 /\
    bytes_at rsegs mc p (x ++ Z_to_bv 8 0 :: slack) /\ no0 x /\ Z.of_nat (length x) <= LMAX /\
    (- (p + Z.of_nat (length x) + 1)) mod 8 <= Z.of_nat (length slack) /\
    (p + Z.of_nat (length (x ++ Z_to_bv 8 0 :: slack)) <= S - K \/ S <= p) /\
    str_home B Lc Ac S p (Z.of_nat (length x) + 1) /\
    (forall a, p <= a < p + Z.of_nat (length (x ++ Z_to_bv 8 0 :: slack)) -> ~ rec_area a).
Proof.
  intros K S L A mem md O Lc Ac mc mdc Rc Oc bc p x SI RA0 H.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof SI as (RJ & _ & _ & _ & B2 & RAc & _).
  destruct (rjr_bounds B _ K S rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  destruct H as (Hp0 & N0 & LX & slack & BS & AL & DJ & HOME & NRA).
  rewrite SEGS in BS.
  pose proof RJ as (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & HF & _ & HK & _).
  rewrite SEGS in HF, HK.
  pose proof (bytes_at_bound _ _ _ _ BS) as BB. rewrite length_app in BB. cbn [length] in BB.
  rewrite length_app in DJ, NRA. cbn [length] in DJ, NRA.
  set (pad := (- (p + Z.of_nat (length x) + 1)) mod 8) in *.
  assert (PADR : 0 <= pad < 8) by (unfold pad; apply Z.mod_pos_bound; lia).
  assert (PADA : (p + Z.of_nat (length x) + 1 + pad) mod 8 = 0).
  { unfold pad. rewrite Zplus_mod_idemp_r. replace (p + Z.of_nat (length x) + 1 + - (p + Z.of_nat (length x) + 1)) with 0
      by ring. reflexivity. }
  assert (PR0 : forall j, 0 <= j < pad -> mbyte rsegs mem (p + Z.of_nat (length x) + 1 + j) <> None).
  { intros j Hj E. pose proof BS as (_ & _ & HB).
    assert (Hlt : (Z.to_nat (Z.of_nat (length x) + 1 + j) < length (x ++ Z_to_bv 8 0 :: slack))%nat)
      by (rewrite length_app; cbn [length]; lia).
    specialize (HB (Z.to_nat (Z.of_nat (length x) + 1 + j)) Hlt).
    change (mrd rsegs mem (wa (p + Z.of_nat (Z.to_nat (Z.of_nat (length x) + 1 + j)))))
      with (mbyte rsegs mem (p + Z.of_nat (Z.to_nat (Z.of_nat (length x) + 1 + j)))) in HB.
    rewrite Z2Nat.id in HB by lia.
    replace (p + (Z.of_nat (length x) + 1 + j)) with (p + Z.of_nat (length x) + 1 + j) in HB by ring.
    rewrite E in HB. symmetry in HB. apply nth_error_None in HB. lia. }
  assert (TX0 : bytes_at rsegs mem p (x ++ [Z_to_bv 8 0])).
  { replace (x ++ Z_to_bv 8 0 :: slack) with ((x ++ [Z_to_bv 8 0]) ++ slack) in BS
      by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app in BS. exact (proj1 BS). }
  assert (LX1 : Z.of_nat (length (x ++ [Z_to_bv 8 0])) = Z.of_nat (length x) + 1)
    by (rewrite length_app; cbn [length]; lia).
  assert (SAME : (forall i, 0 <= i < Z.of_nat (length x) + 1 + pad -> mbyte rsegs mc (p + i) = mbyte rsegs mem (p + i)) ->
                 bytes_at rsegs mc p (x ++ [Z_to_bv 8 0]) /\
                 (forall j, 0 <= j < pad -> mbyte rsegs mc (p + Z.of_nat (length x) + 1 + j) <> None)).
  { intros KE. split.
    - apply (bytes_at_transfer rsegs mem); [exact TX0|]. intros i Hi. rewrite LX1 in Hi. apply KE. lia.
    - intros j Hj. replace (p + Z.of_nat (length x) + 1 + j) with (p + (Z.of_nat (length x) + 1 + j)) by ring.
      rewrite KE by lia. replace (p + (Z.of_nat (length x) + 1 + j)) with (p + Z.of_nat (length x) + 1 + j) by ring.
      exact (PR0 j Hj). }
  assert (CASES : bytes_at rsegs mc p (x ++ [Z_to_bv 8 0]) /\
                  (forall j, 0 <= j < pad -> mbyte rsegs mc (p + Z.of_nat (length x) + 1 + j) <> None) /\
                  str_home B Lc Ac S p (Z.of_nat (length x) + 1)).
  { destruct HOME as [(H1 & H2) | [(q & k & Hq & Hnq & H1 & H2) | (H1 & H2 & H3)]].
    - assert (KE : forall i, 0 <= i < Z.of_nat (length x) + 1 + pad -> mbyte rsegs mc (p + i) = mbyte rsegs mem (p + i)).
      { intros i Hi. refine (proj1 (HF (p + i) _ _ _ _)).
        - unfold free_a. left. lia.
        - lia.
        - lia.
        - intros Hr. unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE in Hr. lia. }
      destruct (SAME KE) as [S1 S2]. split; [exact S1 | split; [exact S2 | left; lia]].
    - assert (NG : ~ In (q, k) O).
      { intros Ho. apply Hnq. apply in_map_iff. exists (q, k). split; [reflexivity | exact Ho]. }
      assert (QC : In (q, k) (blocks Lc Ac)).
      { destruct (in_dec pair_dec (q, k) (blocks Lc Ac)) as [Hc|Hc]; [exact Hc|]. exfalso. exact (NG (B2 _ Hq Hc)). }
      pose proof Hq as Hq'. unfold blocks in Hq'. apply in_map_iff in Hq' as ([pp k'] & E & Hp). cbn [fst snd] in E.
      injection E as E1 E2. subst k'.
      split.
      { apply (bytes_at_transfer rsegs mem); [exact TX0|]. intros i Hi. rewrite LX1 in Hi.
        assert (Hng : ~ (fun pn => In pn O) (ptr_addr L pp, k)) by (intros Hg; apply NG; rewrite <- E1; exact Hg).
        pose proof (HK pp k (p + i - q) Hp Hng ltac:(lia)) as E. rewrite E1 in E.
        replace (q + (p + i - q)) with (p + i) in E by ring. exact E. }
      split.
      { intros j Hj.
        assert (PRc : present mc (p + Z.of_nat (length x) + 1 + j)).
        { destruct (Z_lt_ge_dec (p + Z.of_nat (length x) + 1 + j) (q + k)) as [Hlt|Hge].
          - replace (p + Z.of_nat (length x) + 1 + j) with (q + (p + Z.of_nat (length x) + 1 + j - q)) by ring.
            exact (proj1 (block_facts B _ LAWS Lc Ac mc mdc q k (p + Z.of_nat (length x) + 1 + j - q) HM QC ltac:(lia))).
          - apply (SLACK Lc Ac mc mdc q k _ HM QC). split; [lia|]. Z.div_mod_to_equations. lia. }
        destruct PRc as [bb E]. unfold mbyte. rewrite E. discriminate. }
      right. left. exists q, k. split; [exact QC | lia].
    - pose proof H3 as H3'. rewrite SEGS in H3'.
      assert (KE : forall i, 0 <= i < Z.of_nat (length x) + 1 + pad -> mbyte rsegs mc (p + i) = mbyte rsegs mem (p + i)).
      { intros i Hi.
        assert (RO : ro_addr rsegs (Z_to_bv 64 (p + i)) = true).
        { destruct (Z_lt_ge_dec i (Z.of_nat (length x) + 1)) as [Hl|Hl]; [exact (H3' i ltac:(lia))|].
          pose proof (H3' (Z.of_nat (length x)) ltac:(lia)) as Hlast. apply rs_ro_rsegs in Hlast; [|lia].
          apply rs_ro_rsegs; [lia|]. Z.div_mod_to_equations. lia. }
        rewrite (mbyte_ro_agree _ _ _ RAc RO), (mbyte_ro_agree _ _ _ RA0 RO). reflexivity. }
      destruct (SAME KE) as [S1 S2].
      split; [exact S1 | split; [exact S2 | right; right; split; [exact H1 | split; [exact H2 | exact H3]]]]. }
  destruct CASES as (TX & PADP & HOMEc).
  destruct (rs_bytes_pad rsegs mc p (x ++ [Z_to_bv 8 0]) (Z.to_nat pad) TX) as (sl & SL & BS').
  { rewrite LX1, Z2Nat.id by lia. lia. }
  { intros j Hj. rewrite LX1. replace (p + (Z.of_nat (length x) + 1) + Z.of_nat j)
      with (p + Z.of_nat (length x) + 1 + Z.of_nat j) by ring. apply PADP. lia. }
  rewrite <- app_assoc in BS'. cbn [app] in BS'.
  exists sl.
  split; [lia|]. split; [exact Hp0|].
  split; [exact BS'|]. split; [exact N0|]. split; [exact LX|].
  split; [change ((- (p + Z.of_nat (length x) + 1)) mod 8) with pad; rewrite SL, Z2Nat.id by lia; lia|].
  split; [rewrite length_app; cbn [length]; rewrite SL; destruct DJ as [D|D]; [left; lia | right; exact D]|].
  split; [exact HOMEc|].
  intros a Ha. apply NRA. rewrite length_app in Ha. cbn [length] in Ha. rewrite SL in Ha. lia.
Qed.

Section Run.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (pl ptok : Z) (ps : list Z) (line : list byte) (toks : list (list byte)) (R : rstate) (O : list (Z * Z))
  (b : sbound).
Hypothesis PRE : call_pre_t B API SUP_HOST_SETTING_K L A regs mem md.
Hypothesis A10 : getr regs 10 = Z_to_bv 64 pl.
Hypothesis A11 : getr regs 11 = Z_to_bv 64 ptok.
Hypothesis A12 : getr regs 12 = Z_to_bv 64 (Z.of_nat (length toks)).
Hypothesis NT : (1 <= length toks <= 64)%nat.
Hypothesis SA : str_arg B L A O (spZ regs) SUP_HOST_SETTING_K mem pl (Some line).
Hypothesis PT0 : ptok <> 0.
Hypothesis PT8 : ptok mod 8 = 0.
Hypothesis PTB : Mem.bytes_at (ms_segs B) mem ptok (concat (map (fun p => Mem.le8 (Z_to_bv 64 p)) ps)).
Hypothesis PTW : ptok + 8 * Z.of_nat (length toks) <= spZ regs - SUP_HOST_SETTING_K \/ spZ regs <= ptok.
Hypothesis PTH : buf_home B L A O (spZ regs) ptok (8 * Z.of_nat (length toks)).
Hypothesis PTR : forall a, ptok <= a < ptok + 8 * Z.of_nat (length toks) -> ~ rec_area a.
Hypothesis TKS : Forall2 (fun p w => str_arg B L A O (spZ regs) SUP_HOST_SETTING_K mem p (Some w)) ps toks.
Hypothesis TLEN : sup_host_setting_len toks <= LMAX + 1.
Hypothesis GR : g_rec_rep (ms_segs B) L A mem R O.
Hypothesis RA : ro_agree (ms_segs B) mem.
Hypothesis FRM : frm_zero fp_csr.
Hypothesis F18 : f18_words (ms_segs B) mem.
Hypothesis RES : res_ok_slots A b.
Hypothesis ROOM : room_slots (sb_mallocs b (sup_host_setting_sizes line toks)) (LMAX + 2).

Definition hsu_fr (m : word -> option byte) : Prop :=
  rw_cells rsegs m (spZ regs - 80)
    [C8 (getr regs 24); C8 (getr regs 23); C8 (getr regs 22); C8 (getr regs 21); C8 (getr regs 20);
     C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)].

Definition hsu_KX : list Z := [2; 8; 9; 18; 19; 20; 21; 22; 23; 24].

Lemma hsu_args_len : Forall (fun s => Z.of_nat (length s) <= LMAX)
  [canon line; dec (Z.of_nat (length toks)); join_sp toks].
Proof.
  pose proof SA as (_ & _ & LX & _).
  pose proof (canon_length line) as CL.
  pose proof (dec_length (Z.of_nat (length toks)) ltac:(lia)) as DL.
  pose proof (hsu_join_len toks ltac:(destruct toks; [cbn in NT; lia | discriminate])) as JL.
  rewrite hsu_len_eq in JL.
  repeat constructor; unfold LMAX in *; lia.
Qed.

Lemma hsu_tl : forall (fx' : YK11.FPState) L9 A9 R9 m9 md9 O9,
  sinv B API SUP_HOST_SETTING_K (spZ regs) L A mem md O L9 A9 m9 md9
    (rec_record R REC_HOST_SETTING [canon line; dec (Z.of_nat (length toks)); join_sp toks]) O9 b ->
  sb_le (sb_shift b A A9) (sb_mallocs b (sup_host_setting_sizes line toks)) ->
  st_init_done A9 = true -> fp_kept fx fx' ->
  getr R9 2 = Z_to_bv 64 (spZ regs - 96) -> getr R9 8 = Z_to_bv 64 (rec_entry G_REC REC_SC R) ->
  hsu_kx hsu_KX regs R9 -> hsu_fr m9 ->
  SR rsegs (mkCfg (@mkst fx' R9 (Z_to_bv 64 0x16958) m9 (seg_rom rsegs)) md9)
    (sup_host_setting_ret (fx := fx) B API L A regs mem md line toks R O b).
Proof.
  intros fx' L9 A9 R9 m9 md9 O9 SI BLE INI FK T2 T8 KT FR.
  unfold hsu_fr in FR.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC. pose proof wx_apart_rsegs as WX.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  unfold SUP_HOST_SETTING_K in HCEIL, HWS, SI.
  pose proof SI as (RJ & GR9 & ON & B1 & B2 & RA9 & F189 & RS9).
  pose proof RJ as (HM & _ & _ & _ & _ & HLen & _ & _ & _ & _ & _ & _ & _ & HSC & _).
  destruct (mr_model B _ LAWS L9 A9 m9 md9 HM) as (Hh & Hl & _).
  pose proof hsu_args_len as LXA.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (HN : (length (r_calls R) <= 16)%nat) by exact (rec_rep_calls_le _ _ _ _ _ _ _ _ GR).
  destruct (rec_entry_bounds R HN) as (EB1 & EB2 & EB3).
  set (As3 := [canon line; dec (Z.of_nat (length toks)); join_sp toks]) in *.
  set (R3 := rec_record R REC_HOST_SETTING As3) in *.
  pose proof GR9 as (Q & HRep & HO).
  pose proof HRep as (HS & HC & HA & HP & HX & HW).
  pose proof HX as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10).
  destruct (rec_entry_at rsegs L9 A9 m9 R REC_HOST_SETTING As3 O9 GR9) as (P & CA).
  destruct CA as (CF1 & CF2 & CLP & CFN & CNA & CND & CKA). cbn [fst snd] in *.
  set (e := rec_entry G_REC REC_SC R) in *.
  set (args := combine (map (fun pn => Z_to_bv 64 (fst pn)) P) As3).
  assert (LP : length (map (fun pn => Z_to_bv 64 (fst pn)) P) = length As3) by (rewrite length_map; exact CLP).
  assert (LA : length args = length As3) by (unfold args; rewrite length_combine, LP; lia).
  assert (U2 : bv_unsigned (reg_get R9 2) = bv_unsigned sp - 96).
  { change (reg_get R9 2) with (getr R9 2). rewrite T2. apply unsigned_lit. lia. }
  assert (HARG : forall k p, nth_error args k = Some p ->
            mc_arg (normalize rsegs m9) (bv_unsigned sp - 96 - 96) (bv_unsigned sp - 96) e k p).
  { intros k [w s] Hk. destruct (hsu_nth_combine _ _ _ _ k w s Hk) as (Hw & Hs).
    rewrite nth_error_map in Hw. destruct (nth_error P k) as [pn|] eqn:EP; cbn in Hw; [|discriminate].
    injection Hw as <-.
    destruct (CKA k s pn Hs EP) as (BP & PNZ & PIN & PSZ & PBS & PN0).
    apply (hsu_mc_arg L9 A9 m9 md9 e k pn s); [exact HM | exact RA9 | exact BP | exact PIN | lia | exact PBS | exact PN0 | |].
    - rewrite Forall_forall in LXA. apply LXA. exact (nth_error_In _ _ Hs).
    - lia. }
  assert (EF : bytes_at rsegs (normalize rsegs m9) e
                 (le4 (Z_to_bv 64 6) ++ le4 (Z_to_bv 64 (Z.of_nat (length args))))).
  { apply bytes_at_normalize; [exact RA9|]. apply bytes_at_app. split.
    - unfold CALL_OFF_FN in CFN. rewrite Z.add_0_r in CFN. exact CFN.
    - rewrite LA. replace (e + Z.of_nat (length (le4 (Z_to_bv 64 6)))) with (e + CALL_OFF_NARGS)
        by (rewrite length_le4; unfold CALL_OFF_NARGS; reflexivity). exact CNA. }
  assert (STn : stk rsegs (normalize rsegs m9) (bv_unsigned sp - 8432) (bv_unsigned sp - 96)).
  { apply stk_norm; [lia | lia |]. intros a Ha. rewrite <- SEGS. apply HSC. left. lia. }
  assert (FRn : rw_cells rsegs (normalize rsegs m9) (bv_unsigned sp - 80)
                  [C8 (getr regs 24); C8 (getr regs 23); C8 (getr regs 22); C8 (getr regs 21); C8 (getr regs 20);
                   C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]).
  { apply (rw_cells_norm_hi m9 _ _ RA9); [lia | exact FR]. }
  assert (ESn : rw_cells rsegs (normalize rsegs m9) 0x343e0 [C8 (Z_to_bv 64 (r_host R3))]).
  { apply rw_cells_norm_glob; [exact RA9 | unfold GLOB_LO; lia | cbn; unfold GLOB_LO, GLOB_N; lia |].
    apply bytes_cell8; [unfold GLOB_LO; lia | unfold GLOB_LO, GLOB_N; lia |].
    replace 0x343e0 with (G_REC + OFF_HOST) by (unfold G_REC, OFF_HOST; lia). exact X5. }
  assert (Q8 : reg_get R9 8 = Z_to_bv 64 e) by exact T8.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite Q8.
    eapply (evt_normalize rsegs); [exact WX | exact RA9 |].
    eapply (hsu_tail MIX) with (lo := bv_unsigned sp - 8432);
      [apply mem_inv_normalize | rewrite U2; exact STn | rewrite U2; lia | lia
      | rewrite U2; replace (bv_unsigned sp - 96 + 16) with (bv_unsigned sp - 80) by ring; exact FRn
      | exact EF | unfold REC_SC in EB1; lia | unfold G_REC, REC_SIZE, CALL_SIZE in EB2; lia | exact EB3
      | rewrite LA; cbn; lia | | exact ESn | exact X10].
    intros k p Hk. rewrite U2. exact (HARG k p Hk). }
  intros ms1 (can1 & (s1n & Q1 & REL1 & RO1) & EQ1).
  destruct Q1 as (t0' & t1' & t2' & b1 & b2 & b3 & b4 & b5 & b6 & b7 & t3' & t4' & t5' & t6' & m1n & -> & MU1n
    & WM1n & ES1n).
  destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL1) as [EC1 MR1r].
  revert EC1 MR1r RO1 EQ1. generalize (ms_mem can1) as m1. intros m1 EC1 MR1r RO1 EQ1. subst can1.
  pose proof (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs m9 RA9) MR1r RO1 MU1n) as MU1.
  pose proof (wmono_rel rsegs _ _ _ _ (mem_rel_normalize rsegs m9 RA9) MR1r RO1 WM1n) as WM1.
  pose proof (rw_cells_rel rsegs _ _ _ _ MR1r ES1n) as ES1.
  rewrite U2 in MU1. unfold args in ES1. rewrite (hsu_combine_snd _ _ _ _ LP) in ES1.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R10 & -> & X10r).
  assert (HWW : forall a, 0 <= a < 2 ^ 64 ->
            ~ outside [(bv_unsigned sp - 96 - 96, bv_unsigned sp - 96); (0x343e0, 0x343e8)] a ->
            bv_unsigned sp - 8432 <= a < bv_unsigned sp \/ rec_area a).
  { intros a Ra Hm. cbn in Hm. unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE. lia. }
  assert (SI2 : sinv B API 8432 (bv_unsigned sp) L A mem md O L9 A9 m1 md9 (rec_mix_host R3 (REC_HOST_SETTING, As3)) O9 b).
  { apply (sinv_munch_core B API SEGS GOWN AX 8432 (bv_unsigned sp) L A mem md O L9 A9 m9 md9 R3 O9 b m1 _
             (rec_mix_host R3 (REC_HOST_SETTING, As3)) SI MU1 WM1 HWW).
    unfold g_rec_rep in *. unfold rec_mix_host. cbn [fst snd].
    apply (rec_rep_set_host rsegs G_REC REC_SC L9 A9 m9 m1 R3 O9 (mixcall (r_host R3) REC_HOST_SETTING As3) GR9).
    - apply mixcall_range. exact X10.
    - replace (G_REC + OFF_HOST) with 0x343e0 by (unfold G_REC, OFF_HOST; lia). exact (cells_c8 m1 0x343e0 _ ES1).
    - intros a Ha N. apply (munch_mbyte rsegs _ m9 m1 a MU1); [unfold G_REC, REC_SIZE, REC_SC, SC_SIZE in Ha; lia|].
      match goal with |- outside ?W a => destruct (outside_dec W a) as [H|H]; [exact H|] end. exfalso.
      cbn in H. unfold G_REC, REC_SIZE, REC_SC, SC_SIZE, OFF_HOST in *. lia.
    - intros a Ha _. apply glob_writable. unfold G_REC, REC_SIZE, REC_SC, SC_SIZE, GLOB_LO, GLOB_N in *. lia.
    - exact (sinv_kept B API SEGS AX 8432 (bv_unsigned sp) L A mem md O L9 A9 m9 md9 R3 O9 b m1 _ SI MU1 HWW). }
  assert (E10_2 : getr R10 2 = sp).
  { rewrite (getr_of_eqv _ _ 2 X10r eq_refl). simp_regs. rewrite U2.
    replace (bv_unsigned sp - 96 + 96) with (bv_unsigned sp) by ring. apply Z_to_bv_bv_unsigned. }
  assert (RP10 : regs_preserved regs R10).
  { apply (hsu_kx_pres hsu_KX).
    - apply (hsu_kx_trans _ regs R9 R10 KT). unfold hsu_KX. hsu_kx_tac X10r.
    - intros r Hr. cbn [In hsu_KX] in Hr. destruct Hr as [<-|Hr]; [exact E10_2|].
      destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]];
        match goal with |- getr _ ?k = _ => rewrite (getr_of_eqv _ _ k X10r eq_refl) end;
        simp_regs; first [reflexivity | unfold getr; reflexivity]. }
  pose proof SI2 as (RJ2 & GR2 & ON2 & B12 & B22 & RA2 & F182 & RS2).
  apply SR_ret. unfold sup_host_setting_ret.
  exists fx', L9, A9, R10, m1, md9, O9.
  split; [rewrite SEGS, (ret_pc_of_ok _ HRA); reflexivity|].
  split; [exact FK|].
  split.
  { apply (rjr_final B (aa_MR API) CTX 8432 rec_area (fun pn => In pn O) (fun a => In a (map fst O)) L A regs mem md
             L9 A9 R10 m1 md9 PRK RJ2 RP10).
    intros a0 k0 G. exact (in_map fst O (a0, k0) G). }
  split; [rewrite SEGS; exact GR2|].
  split; [exact ON2|].
  split; [exact B12|].
  split; [exact (rjr_others_kept B (aa_MR API) 8432 (bv_unsigned sp) rec_area (fun pn => In pn O) L A mem md
                   L9 A9 m1 md9 O RJ2 (fun pn H => H))|].
  split; [rewrite SEGS; exact RA2|].
  split; [rewrite SEGS; exact F182|].
  split; [exact INI|].
  split; [pose proof RJ2 as (_ & _ & _ & _ & _ & HLen2 & _); exact HLen2|].
  split; [exact BLE | exact RS2].
Qed.

Lemma hsu_toks_no0 : Forall no0 toks.
Proof.
  pose proof TKS as H. clear -H. induction H as [|p w ps' ws' Hp _ IH]; [constructor|].
  constructor; [|exact IH]. destruct Hp as (_ & N0 & _). exact N0.
Qed.

Lemma hsu_xs : forall (fx' : YK11.FPState) Lj Aj Rj mj mdj Oj (q : sptr) slack,
  sinvT B API (ptr_addr Lj q, sup_host_setting_len toks + 1) SUP_HOST_SETTING_K (spZ regs) L A mem md O Lj Aj mj mdj
    (rec_record R REC_HOST_SETTING [canon line; dec (Z.of_nat (length toks))]) Oj b ->
  In (q, sup_host_setting_len toks + 1) (user_blocks Aj) ->
  sb_le (sb_shift b A Aj)
    (sb_malloc (sb_malloc (sb_malloc b (Z.of_nat (length line) + 1))
       (Z.of_nat (length (dec (Z.of_nat (length toks)))) + 1)) (sup_host_setting_len toks + 1)) ->
  fp_kept fx fx' ->
  getr Rj 1 = Z_to_bv 64 0x16950 -> getr Rj 2 = Z_to_bv 64 (spZ regs - 96) -> getr Rj 4 = getr regs 4 ->
  getr Rj 8 = Z_to_bv 64 (rec_entry G_REC REC_SC R) ->
  getr Rj 10 = Z_to_bv 64 (rec_entry G_REC REC_SC R) -> getr Rj 11 = Z_to_bv 64 (ptr_addr Lj q) ->
  getr Rj 19 = Z_to_bv 64 (ptr_addr Lj q) ->
  hsu_kx hsu_KX regs Rj -> hsu_fr mj ->
  bytes_at rsegs mj (ptr_addr Lj q) (join_sp toks ++ Z_to_bv 8 0 :: slack) ->
  (- (ptr_addr Lj q + Z.of_nat (length (join_sp toks)) + 1)) mod 8 <= Z.of_nat (length slack) ->
  ptr_addr Lj q + Z.of_nat (length (join_sp toks ++ Z_to_bv 8 0 :: slack)) <= alloc_ceiling ->
  SR rsegs (mkCfg (@mkst fx' Rj (Z_to_bv 64 ARG_S) mj (seg_rom rsegs)) mdj)
    (sup_host_setting_ret (fx := fx) B API L A regs mem md line toks R O b).
Proof.
  intros fx' Lj Aj Rj mj mdj Oj q slack SI QIN BLE FK E1 E2 E4 E8 E10 E11 E19 KE FR BJ AL SLB.
  unfold hsu_fr in FR.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC. pose proof wx_apart_rsegs as WX.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  unfold SUP_HOST_SETTING_K in HCEIL, HWS, SI.
  pose proof SI as (RJ & GR9 & ON & B1 & B2 & RA9 & F189 & RS9 & TI & TO & TA & TP).
  pose proof RJ as (HM & _).
  assert (HN : (length (r_calls R) <= 16)%nat) by exact (rec_rep_calls_le _ _ _ _ _ _ _ _ GR).
  destruct (rec_entry_bounds R HN) as (EB1 & EB2 & EB3).
  destruct (rec_entry_at rsegs Lj Aj mj R REC_HOST_SETTING [canon line; dec (Z.of_nat (length toks))] Oj GR9)
    as (P & CA).
  destruct CA as (_ & _ & _ & _ & CNA & _). cbn [snd length Z.of_nat] in CNA.
  set (e := rec_entry G_REC REC_SC R) in *.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (SPj : spZ Rj = bv_unsigned sp - 96) by (unfold spZ; rewrite E2; apply unsigned_lit; lia).
  set (t := ptr_addr Lj q) in *.
  set (nT := sup_host_setting_len toks + 1) in *.
  set (x := join_sp toks) in *.
  assert (TNE : toks <> []) by (destruct toks; [cbn in NT; lia | discriminate]).
  pose proof (hsu_join_len toks TNE) as JL. fold x in JL. rewrite hsu_len_eq in JL.
  assert (XN0 : no0 x) by exact (hsu_join_no0 toks hsu_toks_no0).
  assert (XL : Z.of_nat (length x) <= LMAX) by (unfold LMAX in *; lia).
  set (kx := Z.of_nat (length x) + 1) in *.
  pose proof (bytes_at_bound _ _ _ _ BJ) as SB. rewrite length_app in SB. cbn [length] in SB.
  destruct (block_facts B _ LAWS Lj Aj mj mdj t nT 0 HM TI ltac:(cbn in TP; lia)) as (_ & T1 & T2 & _).
  pose proof (ARGS fx') as ASC. unfold arg_s_contract in ASC. rewrite SEGS in ASC.
  assert (ROOMx : room_slots (sb_malloc (sb_shift b A Aj) kx) kx).
  { unfold sb_mallocs, sup_host_setting_sizes in ROOM. cbn [fold_left] in ROOM. fold x kx in ROOM.
    eapply room_slots_mono; [apply sb_malloc_mono; exact BLE | | exact ROOM]. unfold kx, LMAX in *. lia. }
  eapply SR_bind.
  { apply (ASC Lj Aj Rj mj mdj e t 2 (Some x) (sb_shift b A Aj)).
    - apply (call_pre_k_of_rjr B _ 8432 (bv_unsigned sp) rec_area _ L A mem md Lj Aj mj mdj ARG_S_K Rj RJ).
      + rewrite E1. apply bv_eq. vm_compute. reflexivity.
      + rewrite SPj. replace (bv_unsigned sp - 96) with (bv_unsigned sp + (-6) * 16) by ring.
        rewrite Z.mod_add by lia. exact HAL.
      + unfold ARG_S_K, XMALLOC_K, ALLOC_STACK. lia.
      + rewrite SPj. unfold ARG_S_K, XMALLOC_K, ALLOC_STACK. lia.
      + rewrite SPj. lia.
      + rewrite E4. exact HTP.
    - exact E10.
    - exact E11.
    - exact EB3.
    - exact EB1.
    - exact EB2.
    - apply glob_wr_at; unfold REC_SC, G_REC, REC_SIZE, CALL_SIZE, GLOB_LO, GLOB_N in *; lia.
    - exact CNA.
    - lia.
    - cbn [arg_s_src]. rewrite SEGS.
      split; [lia|]. split; [exact XN0|]. split; [exact XL|].
      exists slack. split; [exact BJ|]. split; [exact AL|].
      split; [left; rewrite SPj; unfold ARG_S_K, XMALLOC_K, ALLOC_STACK; lia|].
      right. left. exists t, nT. split; [exact TI|]. unfold nT, kx in *. lia.
    - exact F189.
    - exact RS9.
    - exact ROOMx.
    - exact RA9. }
  intros c2 (L8 & A8 & R8 & m8 & md8 & -> & BK8 & UB8 & RA8 & GK8 & F188 & RGN8 &
    [(M6 & _) | (_ & p & POST8 & Hp0 & PAL & FB8 & BLK8 & NA8 & AS8 & BP8 & INI8 & RS8)]); [lia|].
  rewrite SEGS in NA8, AS8, BP8, RA8, F188 |- *.
  pose proof POST8 as (PM8 & _ & _ & _ & PA8 & RP8 & _).
  pose proof (sinvT_arg B API SEGS ERRNO_LOW GFACT GOWN AX (t, nT) 8432 (bv_unsigned sp) L A mem md O Lj Aj mj mdj R
                REC_HOST_SETTING [canon line; dec (Z.of_nat (length toks))] Oj b ARG_S_K Rj _ L8 A8 R8 m8 md8 x p kx
                SI ltac:(cbn; lia) ltac:(rewrite SPj; unfold ARG_S_K, XMALLOC_K, ALLOC_STACK; lia)
                ltac:(rewrite SPj; lia) POST8
                ltac:(intros a Ha; cbv beta in Ha; cbn [sarg] in Ha; cbn [length Z.of_nat]; unfold kx; lia)
                Hp0 FB8 BLK8 UB8 BK8 RGN8 NA8 AS8 BP8 XN0 XL ltac:(unfold kx, LMAX in *; lia) INI8 RS8 RA8 F188)
    as SI9.
  cbn [app] in SI9.
  assert (PQ : ptr_addr L8 q = t) by exact (PA8 q nT QIN (UB8 q nT QIN)).
  rewrite <- PQ in SI9.
  pose proof SI9 as (RJ9 & _ & _ & _ & _ & RA9' & _ & RS9' & TI9 & _).
  pose proof RJ9 as (HM9 & _).
  pose proof FB8 as (FBa & FBb & FBc).
  assert (FR8 : rw_cells rsegs m8 (bv_unsigned sp - 80)
                  [C8 (getr regs 24); C8 (getr regs 23); C8 (getr regs 22); C8 (getr regs 21); C8 (getr regs 20);
                   C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]).
  { apply (rw_cells_transfer rsegs mj); [exact FR|]. intros i Hi. cbn in Hi.
    destruct (hsu_keep_hi B API SEGS ERRNO_LOW ARG_S_K Lj Aj Rj mj mdj _ L8 A8 R8 m8 md8 (bv_unsigned sp - 80 + i)
                HM POST8 ltac:(lia) ltac:(rewrite SPj; lia)) as [K1 K2].
    - intros H. cbv beta in H. unfold G_REC, REC_SIZE, CALL_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS, kx in *. lia.
    - split; [exact K1 | exact (proj1 K2)]. }
  destruct (mr_model B _ LAWS L8 A8 m8 md8 PM8) as (Hh8 & Hl8 & _).
  rewrite E1.
  eapply evt_SR_canon; [ | exact Hh8 | exact Hl8 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. apply hsu_free_call. }
  intros ms9 (can9 & -> & EQ9).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ9 eq_refl eq_refl) as (R9 & -> & X9).
  assert (KR9 : hsu_kx hsu_KX regs R9).
  { apply (hsu_kx_trans _ regs Rj R9 KE). apply (hsu_kx_trans _ Rj R8 R9 (hsu_kx_of_pres _ _ _ RP8)).
    unfold hsu_KX. hsu_kx_tac X9. }
  assert (R9_1 : getr R9 1 = Z_to_bv 64 0x16958) by (rewrite (getr_of_eqv _ _ 1 X9 eq_refl); simp_regs; reflexivity).
  assert (R9_2 : getr R9 2 = Z_to_bv 64 (bv_unsigned sp - 96)).
  { rewrite (getr_of_eqv _ _ 2 X9 eq_refl). simp_regs. exact (eq_trans (RP8 2 ltac:(unfold callee_saved; lia)) E2). }
  assert (R9_4 : getr R9 4 = getr regs 4).
  { rewrite (getr_of_eqv _ _ 4 X9 eq_refl). simp_regs. exact (eq_trans (RP8 4 ltac:(unfold callee_saved; lia)) E4). }
  assert (R9_8 : getr R9 8 = Z_to_bv 64 e).
  { rewrite (getr_of_eqv _ _ 8 X9 eq_refl). simp_regs. exact (eq_trans (RP8 8 ltac:(unfold callee_saved; lia)) E8). }
  assert (R9_10 : getr R9 10 = Z_to_bv 64 (ptr_addr L8 q)).
  { rewrite (getr_of_eqv _ _ 10 X9 eq_refl). simp_regs. rewrite PQ.
    exact (eq_trans (RP8 19 ltac:(unfold callee_saved; lia)) E19). }
  assert (SP9 : spZ R9 = bv_unsigned sp - 96) by (unfold spZ; rewrite R9_2; apply unsigned_lit; lia).
  assert (BLE8 : sb_le (sb_shift b A A8) (sb_mallocs b (sup_host_setting_sizes line toks))).
  { destruct BLK8 as (bl1 & bl2 & EB1' & EB2').
    rewrite <- (sb_shift_trans b A Aj A8).
    rewrite <- (sb_shift_add (sb_shift b A Aj) Lj Aj L8 A8 bl1 bl2 p _ EB1' EB2').
    unfold sb_mallocs, sup_host_setting_sizes. cbn [fold_left]. fold x kx. fold nT.
    apply sb_malloc_mono. exact BLE. }
  replace (Z_to_bv 64 0x18ad0) with (Z_to_bv 64 (ms_free B)) by (rewrite FREE_PC; reflexivity).
  pose proof (FREE fx') as FRE. unfold free_contract in FRE. rewrite SEGS in FRE.
  eapply SR_bind.
  { apply (FRE L8 A8 R9 m8 md8 q nT (sb_shift b A A8)).
    - apply (proj2 (call_pre_k_alloc B (aa_MR API) _ _ _ _ _)).
      apply (call_pre_k_of_rjr B _ 8432 (bv_unsigned sp) rec_area _ L A mem md L8 A8 m8 md8 ALLOC_STACK R9 RJ9).
      + rewrite R9_1. apply bv_eq. vm_compute. reflexivity.
      + rewrite SP9. replace (bv_unsigned sp - 96) with (bv_unsigned sp + (-6) * 16) by ring.
        rewrite Z.mod_add by lia. exact HAL.
      + unfold ALLOC_STACK. lia.
      + rewrite SP9. unfold ALLOC_STACK. lia.
      + rewrite SP9. lia.
      + rewrite R9_4. exact HTP.
    - exact RA9'.
    - exact (UB8 q nT QIN).
    - exact R9_10.
    - exact RS9'. }
  intros c10 (Lf & Af & Rf & mf & mdf & -> & POST10 & BLK10 & BK10 & RA10 & GK10 & UB10 & INI10 & RGN10 & RS10).
  pose proof (sinvT_free B API SEGS ERRNO_LOW GOTG GUARDG GFACT GOWN AX 8432 (bv_unsigned sp) L A mem md O L8 A8 m8 md8
                (rec_record R REC_HOST_SETTING [canon line; dec (Z.of_nat (length toks)); x]) (Oj ++ [(p, kx)]) b
                R9 Lf Af Rf mf mdf q nT) as SIF.
  pose proof POST10 as POST10k. apply (proj1 (call_post_k_alloc B (aa_MR API) _ _ _ _ _ _ _ _ _ _ _)) in POST10k.
  pose proof POST10k as (PM10 & _ & _ & _ & _ & RP10 & _).
  assert (SI10 := SIF SI9 ltac:(rewrite SP9; unfold ALLOC_STACK; lia) ltac:(rewrite SP9; lia) (UB8 q nT QIN)
                    POST10 BLK10 BK10 RA10 GK10 UB10 (INI10 INI8) RGN10 RS10).
  rewrite R9_1.
  apply (hsu_tl fx' Lf Af Rf mf mdf (Oj ++ [(p, kx)]) SI10).
  - destruct BLK10 as (bl1 & bl2 & EB1' & EB2').
    rewrite <- (sb_shift_trans b A A8 Af).
    rewrite PQ in EB1'. rewrite <- (sb_shift_del (sb_shift b A A8) L8 A8 Lf Af bl1 bl2 t nT EB1' EB2').
    eapply sb_le_trans; [apply sb_free_le; unfold nT; lia | exact BLE8].
  - exact (INI10 INI8).
  - exact FK.
  - exact (eq_trans (RP10 2 ltac:(unfold callee_saved; lia)) R9_2).
  - exact (eq_trans (RP10 8 ltac:(unfold callee_saved; lia)) R9_8).
  - exact (hsu_kx_trans _ regs R9 Rf KR9 (hsu_kx_of_pres _ _ _ RP10)).
  - unfold hsu_fr. change (spZ regs) with (bv_unsigned sp).
    apply (rw_cells_transfer rsegs m8); [exact FR8|]. intros i Hi. cbn in Hi.
    destruct (hsu_keep_hi B API SEGS ERRNO_LOW ALLOC_STACK L8 A8 R9 m8 md8 _ Lf Af Rf mf mdf (bv_unsigned sp - 80 + i)
                HM9 POST10k ltac:(lia) ltac:(rewrite SP9; unfold ALLOC_STACK; lia)) as [K1 K2].
    + intros H. cbv beta in H.
      destruct (block_facts B _ LAWS L8 A8 m8 md8 _ nT 0 HM9 TI9 ltac:(cbn in TP; unfold nT in *; lia)) as (_ & _ & X3 & _).
      lia.
    + split; [exact K1 | exact (proj1 K2)].
Qed.

Lemma hsu_ptok : forall Lc Ac mc mdc,
  rjr B (aa_MR API) 8432 (spZ regs) rec_area (fun pn => In pn O) L A mem md Lc Ac mc mdc ->
  ro_agree rsegs mc -> bytes_at rsegs mc ptok (concat (map (fun p => le8 (Z_to_bv 64 p)) ps)).
Proof.
  intros Lc Ac mc mdc RJ RAc. pose proof alloc_ceiling_val as AC.
  pose proof RJ as (_ & _ & _ & _ & _ & _ & _ & K1 & K2 & K3 & HF & HRM & HKP & _).
  pose proof (Forall2_length TKS) as LT.
  pose proof PTB as BX. rewrite SEGS in BX.
  pose proof RA as RA0. rewrite SEGS in RA0.
  pose proof PTH as HOME. unfold buf_home in HOME. rewrite SEGS in HOME.
  apply (bytes_at_transfer rsegs mem); [exact BX|]. intros i Hi. rewrite length_concat_le8, LT in Hi.
  destruct HOME as [(H1 & H2) | [(qb & kb & Hq & Hnq & H1 & H2) | (H1 & H2 & H3)]].
  - rewrite <- SEGS. refine (proj1 (HF (ptok + i) _ _ _ _)).
    + unfold free_a. left. lia.
    + lia.
    + pose proof ERRNO_LOW. lia.
    + apply PTR. lia.
  - unfold blocks in Hq. apply in_map_iff in Hq as ([pb kb'] & E & Hpb). cbn [fst snd] in E.
    injection E as E1 E2. subst qb kb.
    rewrite <- SEGS. replace (ptok + i) with (ptr_addr L pb + (ptok + i - ptr_addr L pb)) by ring.
    apply (HKP pb kb' (ptok + i - ptr_addr L pb) Hpb); [|lia].
    intros G. apply Hnq. apply in_map_iff. exists (ptr_addr L pb, kb'). split; [reflexivity | exact G].
  - rewrite (mbyte_ro_agree _ _ _ RAc (H3 i Hi)), (mbyte_ro_agree _ _ _ RA0 (H3 i Hi)). reflexivity.
Qed.

Lemma hsu_am : forall (fx' : YK11.FPState) L4 A4 R4 m4 md4 O4 (q : sptr),
  sinvT B API (ptr_addr L4 q, sup_host_setting_len toks + 1) SUP_HOST_SETTING_K (spZ regs) L A mem md O L4 A4 m4 md4
    (rec_record R REC_HOST_SETTING [canon line; dec (Z.of_nat (length toks))]) O4 b ->
  In (q, sup_host_setting_len toks + 1) (user_blocks A4) -> ptr_addr L4 q mod 16 = 0 ->
  sb_le (sb_shift b A A4)
    (sb_malloc (sb_malloc (sb_malloc b (Z.of_nat (length line) + 1))
       (Z.of_nat (length (dec (Z.of_nat (length toks)))) + 1)) (sup_host_setting_len toks + 1)) ->
  fp_kept fx fx' ->
  getr R4 2 = Z_to_bv 64 (spZ regs - 96) -> getr R4 4 = getr regs 4 ->
  getr R4 8 = Z_to_bv 64 (rec_entry G_REC REC_SC R) -> getr R4 9 = getr regs 11 -> getr R4 18 = getr regs 12 ->
  getr R4 10 = Z_to_bv 64 (ptr_addr L4 q) ->
  hsu_kx hsu_KX regs R4 -> hsu_fr m4 ->
  SR rsegs (mkCfg (@mkst fx' R4 (Z_to_bv 64 0x168e0) m4 (seg_rom rsegs)) md4)
    (sup_host_setting_ret (fx := fx) B API L A regs mem md line toks R O b).
Proof.
  intros fx' L4 A4 R4 m4 md4 O4 q SI QIN QA BLE FK E2 E4 E8 E9 E18 E10 KE FR.
  unfold hsu_fr in FR.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC. pose proof alloc_ceiling_value as ACV.
  pose proof wx_apart_rsegs as WX.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  unfold SUP_HOST_SETTING_K in HCEIL, HWS, SI.
  pose proof RA as RA0. rewrite SEGS in RA0.
  pose proof PTW as PTW0. unfold SUP_HOST_SETTING_K in PTW0.
  pose proof SI as (RJ & GR4 & _ & _ & B2 & RA4 & F184 & RS4 & TI & TO & TAo & TP).
  pose proof RJ as (HM & _ & _ & _ & _ & HLen & _ & _ & _ & _ & _ & _ & _ & HSC & _).
  destruct (mr_model B _ LAWS L4 A4 m4 md4 HM) as (Hh & Hl & _).
  pose proof (Forall2_length TKS) as LT.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  set (t := ptr_addr L4 q) in *.
  set (nT := sup_host_setting_len toks + 1) in *.
  assert (NTE : nT = hsu_len toks + 1) by reflexivity.
  pose proof (hsu_len_nn toks) as LN.
  cbn [fst snd] in TP.
  destruct (block_facts B _ LAWS L4 A4 m4 md4 t nT 0 HM TI ltac:(lia)) as (_ & T1 & T2 & _).
  set (Tlen := 8 * ((t + nT + 7) / 8) - t).
  assert (TLE : Tlen = 8 * ((t + nT + 7) / 8) - t) by reflexivity.
  assert (TLa : nT <= Tlen /\ (t + Tlen) mod 8 = 0 /\ t + Tlen <= alloc_ceiling).
  { destruct ACV as (_ & ACM).
    pose proof (Z.div_mod (t + nT + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (t + nT + 7) 8 ltac:(lia)).
    pose proof (Z.div_mod alloc_ceiling 4096 ltac:(lia)).
    rewrite TLE. replace (t + (8 * ((t + nT + 7) / 8) - t)) with (8 * ((t + nT + 7) / 8)) by ring.
    split; [lia|]. split; [rewrite Z.mul_comm, Z_mod_mult; reflexivity | lia]. }
  destruct TLa as (TL1 & TL2 & TL3).
  assert (U2 : bv_unsigned (reg_get R4 2) = bv_unsigned sp - 96).
  { change (reg_get R4 2) with (getr R4 2). rewrite E2. apply unsigned_lit. lia. }
  assert (NRO : forall i, 0 <= i < nT -> ro_addr rsegs (Z_to_bv 64 (t + i)) = false).
  { intros i Hi. destruct (ro_addr rsegs (Z_to_bv 64 (t + i))) eqn:E; [|reflexivity]. exfalso.
    apply (hsu_blk_img B API AX L4 A4 m4 md4 t nT i HM TI Hi). apply (ro_in_img B SEGS); [lia | exact E]. }
  destruct (rs_bytes_pad rsegs m4 t [] (Z.to_nat Tlen)) as (X0 & X0L & X0B).
  { split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. cbn [length] in Hi. lia. }
  { cbn [length]. lia. }
  { intros j Hj. replace (t + Z.of_nat (length (@nil byte)) + Z.of_nat j) with (t + Z.of_nat j) by (cbn [length]; lia).
    apply hsu_present.
    destruct (Z_lt_ge_dec (Z.of_nat j) nT) as [Hjl|Hjg].
    - exact (proj1 (block_facts B _ LAWS L4 A4 m4 md4 t nT (Z.of_nat j) HM TI ltac:(lia))).
    - apply (SLACK L4 A4 m4 md4 t nT _ HM TI). lia. }
  cbn [app] in X0B.
  assert (JI : jinvX (reg_get R4 2) t nT Tlen (bv_unsigned sp - 8432) (normalize rsegs m4) (normalize rsegs m4) X0).
  { split; [apply mem_inv_normalize|].
    split.
    { rewrite U2. apply stk_norm; [lia | lia |]. intros a Ha. rewrite <- SEGS. apply HSC. left. lia. }
    split; [apply munch_refl|].
    split; [apply wmono_refl|].
    split.
    { split; [lia|]. split; [lia|]. intros i Hi.
      destruct (block_facts B _ LAWS L4 A4 m4 md4 t nT i HM TI Hi) as ((bb & Eb) & _).
      apply (present_writable rsegs _ (t + i)). exists bb. unfold normalize. cbv beta. rewrite (NRO i Hi). exact Eb. }
    split; [exact (bytes_at_normalize rsegs m4 _ _ RA4 X0B)|].
    rewrite X0L. lia. }
  assert (TA8 : t mod 8 = 0) by lia.
  assert (TKJ : Forall2 (tokj (reg_get R4 2) t nT (bv_unsigned sp - 8432) (normalize rsegs m4)) ps toks).
  { eapply Forall2_impl; [|exact TKS]. intros p w Hp. unfold SUP_HOST_SETTING_K in Hp.
    destruct (hsu_tstr _ 8432 (bv_unsigned sp) L A mem md O L4 A4 m4 md4 _ O4 b p w SI TA8 RA0 Hp)
      as (sl & BS & N0 & P0 & PAD & DJ & DT).
    unfold tokj. exists sl.
    split; [exact (bytes_at_normalize rsegs m4 _ _ RA4 BS)|]. split; [exact N0|].
    split; [rewrite PAD; lia|]. split; [exact P0|]. rewrite U2.
    split; [destruct DJ as [D|D]; [left; lia | right; lia]|]. exact DT. }
  pose proof (bytes_at_normalize rsegs m4 _ _ RA4 (hsu_ptok L4 A4 m4 md4 RJ RA4)) as PBn.
  assert (PW2 : ptok + 8 * Z.of_nat (length ps) <= t \/ t + nT <= ptok).
  { rewrite LT. exact (hsu_home_T _ 8432 (bv_unsigned sp) L A mem md O L4 A4 m4 md4 _ O4 b ptok
                         (8 * Z.of_nat (length toks)) SI ltac:(lia) PTH). }
  assert (Q9 : reg_get R4 9 = Z_to_bv 64 ptok) by exact (eq_trans E9 A11).
  assert (Q10 : reg_get R4 10 = Z_to_bv 64 t) by exact E10.
  assert (Q18 : reg_get R4 18 = Z_to_bv 64 (Z.of_nat (length ps))) by (rewrite LT; exact (eq_trans E18 A12)).
  pose proof (bytes_at_bound _ _ _ _ PBn) as PBB. rewrite length_concat_le8 in PBB.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite Q9, Q10, Q18.
    eapply (evt_normalize rsegs); [exact WX | exact RA4 |].
    eapply (hsu_e2 SLEN SCAT _ _ _ _ _ _ _ _ _ _ _ t nT Tlen (bv_unsigned sp - 8432) ptok (normalize rsegs m4)
              ps toks X0);
      [lia | lia | lia | exact TL2 | lia | rewrite U2; lia | lia | exact JI | exact TKJ | exact PBn
      | rewrite U2; rewrite LT; lia | exact PW2 | rewrite LT; lia | rewrite NTE; lia]. }
  intros ms1 (can1 & (s1n & Q1 & REL1 & RO1) & EQ1).
  destruct Q1 as (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & s2' & s5' & m5n & slack
    & -> & JI5).
  destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL1) as [EC1 MR1r].
  revert EC1 MR1r RO1 EQ1. generalize (ms_mem can1) as m5. intros m5 EC1 MR1r RO1 EQ1. subst can1.
  destruct JI5 as (MI5 & ST5 & MU5n & WM5n & HW5 & HB5 & HL5).
  pose proof (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs m4 RA4) MR1r RO1 MU5n) as MU5.
  pose proof (wmono_rel rsegs _ _ _ _ (mem_rel_normalize rsegs m4 RA4) MR1r RO1 WM5n) as WM5.
  pose proof (proj2 (bytes_at_rel rsegs _ _ _ _ MR1r) HB5) as BJ.
  rewrite U2 in MU5.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R5 & -> & X5).
  assert (SI5 : sinvT B API (t, nT) 8432 (bv_unsigned sp) L A mem md O L4 A4 m5 md4
                  (rec_record R REC_HOST_SETTING [canon line; dec (Z.of_nat (length toks))]) O4 b).
  { apply (sinvT_munch B API SEGS GOTG GUARDG GOWN AX (t, nT) 8432 (bv_unsigned sp) L A mem md O L4 A4 m4 md4 _ O4 b m5 _
             SI MU5 WM5).
    intros a Ra Hm. cbn [outside] in Hm. cbn [fst snd]. lia. }
  assert (FR5 : rw_cells rsegs m5 (bv_unsigned sp - 80)
                  [C8 (getr regs 24); C8 (getr regs 23); C8 (getr regs 22); C8 (getr regs 21); C8 (getr regs 20);
                   C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]).
  { apply (rw_cells_transport rsegs _ m4 m5 _ _ FR MU5 WM5). cbn [disjoint_from cells_size csize Nat.add].
    repeat split; lia. }
  pose proof HL5 as HL5'. rewrite length_app in HL5'. cbn [length] in HL5'.
  apply (hsu_xs fx' L4 A4 R5 m5 md4 O4 q slack SI5 QIN BLE FK).
  - rewrite (getr_of_eqv _ _ 1 X5 eq_refl). simp_regs. reflexivity.
  - rewrite (getr_of_eqv _ _ 2 X5 eq_refl). simp_regs. exact E2.
  - rewrite (getr_of_eqv _ _ 4 X5 eq_refl). simp_regs. exact E4.
  - rewrite (getr_of_eqv _ _ 8 X5 eq_refl). simp_regs. exact E8.
  - rewrite (getr_of_eqv _ _ 10 X5 eq_refl). simp_regs. exact E8.
  - rewrite (getr_of_eqv _ _ 11 X5 eq_refl). simp_regs. reflexivity.
  - rewrite (getr_of_eqv _ _ 19 X5 eq_refl). simp_regs. reflexivity.
  - apply (hsu_kx_trans _ regs R4 R5 KE). unfold hsu_KX. hsu_kx_tac X5.
  - exact FR5.
  - exact BJ.
  - change (ptr_addr L4 q) with t.
    assert (EM : (- (t + Tlen)) mod 8 = 0) by (apply Z_mod_zero_opp_full; exact TL2).
    replace (- (t + Z.of_nat (length (join_sp toks)) + 1)) with (Z.of_nat (length slack) + - (t + Tlen)) by lia.
    rewrite Zplus_mod, EM, Z.add_0_r, Z.mod_mod by lia. apply Z.mod_le; lia.
  - change (ptr_addr L4 q) with t. rewrite HL5. lia.
Qed.

Lemma hsu_toks_f : forall Lc Ac mc mdc Rc Oc bc,
  sinv B API 8432 (spZ regs) L A mem md O Lc Ac mc mdc Rc Oc bc -> ro_agree rsegs mc ->
  Forall2 (tokf (normalize rsegs mc)) ps toks.
Proof.
  intros Lc Ac mc mdc Rc Oc bc SI RAc. pose proof RA as RA0. rewrite SEGS in RA0.
  eapply Forall2_impl; [|exact TKS]. intros p w Hp. unfold SUP_HOST_SETTING_K in Hp.
  destruct (sinv_arg_src B API SEGS ERRNO_LOW SLACK 8432 (spZ regs) L A mem md O Lc Ac mc mdc Rc Oc bc p (Some w)
              (spZ regs) SI RA0 ltac:(unfold ARG_S_K, XMALLOC_K, ALLOC_STACK; lia) ltac:(lia) Hp)
    as (Hp0 & N0 & LX & slack & BS & ALN & _).
  rewrite SEGS in BS.
  pose proof (bytes_at_bound _ _ _ _ BS) as BB.
  unfold tokf. exists slack.
  split; [exact (bytes_at_normalize rsegs mc _ _ RAc BS)|]. split; [exact N0|]. split; [exact ALN | lia].
Qed.

Lemma hsu_room : forall k, 0 <= k <= LMAX + 2 -> forall bb,
  sb_le bb (sb_mallocs b (sup_host_setting_sizes line toks)) -> room_slots bb k.
Proof.
  intros k Hk bb H. eapply room_slots_mono; [exact H | exact Hk | exact ROOM].
Qed.

Lemma hsu_m : forall (fx' : YK11.FPState) L2 A2 R2 m2 md2 O2,
  sinv B API SUP_HOST_SETTING_K (spZ regs) L A mem md O L2 A2 m2 md2
    (rec_record R REC_HOST_SETTING [canon line; dec (Z.of_nat (length toks))]) O2 b ->
  sb_le (sb_shift b A A2)
    (sb_malloc (sb_malloc b (Z.of_nat (length line) + 1)) (Z.of_nat (length (dec (Z.of_nat (length toks)))) + 1)) ->
  fp_kept fx fx' ->
  getr R2 2 = Z_to_bv 64 (spZ regs - 96) -> getr R2 4 = getr regs 4 ->
  getr R2 8 = Z_to_bv 64 (rec_entry G_REC REC_SC R) ->
  getr R2 9 = getr regs 11 -> getr R2 18 = getr regs 12 ->
  hsu_kx hsu_KX regs R2 -> hsu_fr m2 ->
  SR rsegs (mkCfg (@mkst fx' R2 (Z_to_bv 64 0x16880) m2 (seg_rom rsegs)) md2)
    (sup_host_setting_ret (fx := fx) B API L A regs mem md line toks R O b).
Proof.
  intros fx' L2 A2 R2 m2 md2 O2 SI2 BLE2 FK E2 E4 E8 E9 E18 KE2 FR2.
  unfold hsu_fr in FR2.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC. pose proof wx_apart_rsegs as WX.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  unfold SUP_HOST_SETTING_K in HCEIL, HWS, SI2.
  pose proof SI2 as (RJ2 & _ & _ & _ & _ & RA2 & F182 & RS2).
  pose proof RJ2 as (HM2 & _).
  destruct (mr_model B _ LAWS L2 A2 m2 md2 HM2) as (Hh & Hl & _).
  pose proof (Forall2_length TKS) as LT.
  pose proof (hsu_len_nn toks) as LN.
  pose proof (hsu_toks_f L2 A2 m2 md2 _ O2 b SI2 RA2) as TF.
  pose proof (bytes_at_normalize rsegs m2 _ _ RA2 (hsu_ptok L2 A2 m2 md2 RJ2 RA2)) as PBn.
  pose proof (bytes_at_bound _ _ _ _ PBn) as PBB. rewrite length_concat_le8 in PBB.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (Q9 : reg_get R2 9 = Z_to_bv 64 ptok) by exact (eq_trans E9 A11).
  assert (Q18 : reg_get R2 18 = Z_to_bv 64 (Z.of_nat (length ps))) by (rewrite LT; exact (eq_trans E18 A12)).
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite Q9, Q18.
    eapply (evt_normalize rsegs); [exact WX | exact RA2 |].
    eapply (hsu_e1 SLEN _ _ _ _ _ _ _ _ _ ptok ps toks);
      [lia | apply mem_inv_normalize | exact TF | exact PBn | rewrite LT; lia | exact PT8
      | rewrite hsu_len_eq; exact TLEN]. }
  intros ms1 (can1 & (s1n & Q1 & REL1 & RO1) & EQ1).
  destruct Q1 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1n & -> & MU1n
    & MI1n).
  destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL1) as [EC1 MR1r].
  revert EC1 MR1r RO1 EQ1. generalize (ms_mem can1) as m3. intros m3 EC1 MR1r RO1 EQ1. subst can1.
  pose proof (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs m2 RA2) MR1r RO1 MU1n) as MU1.
  assert (WM1 : wmono rsegs m2 m3).
  { intros x Hx. unfold wview in *. rewrite (MU1 x I). exact Hx. }
  pose proof (ro_agree_of_mem_rel rsegs _ _ MR1r) as RA3.
  pose proof (sinv_stack B API SEGS GOWN AX 8432 (bv_unsigned sp) L A mem md O L2 A2 m2 md2 _ O2 b m3 [] SI2 MU1 WM1
                ltac:(intros a Ra Hm; exfalso; exact (Hm I))) as SI3.
  pose proof SI3 as (RJ3 & _ & _ & _ & _ & _ & _ & RS3).
  assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp - 80)
                  [C8 (getr regs 24); C8 (getr regs 23); C8 (getr regs 22); C8 (getr regs 21); C8 (getr regs 20);
                   C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]).
  { apply (rw_cells_transport rsegs [] m2 m3 _ _ FR2 MU1 WM1). cbn [disjoint_from]. exact I. }
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R3 & -> & X3).
  assert (E3_1 : getr R3 1 = Z_to_bv 64 0x168e0) by (rewrite (getr_of_eqv _ _ 1 X3 eq_refl); simp_regs; reflexivity).
  assert (E3_2 : getr R3 2 = Z_to_bv 64 (bv_unsigned sp - 96))
    by (rewrite (getr_of_eqv _ _ 2 X3 eq_refl); simp_regs; exact E2).
  assert (E3_4 : getr R3 4 = getr regs 4) by (rewrite (getr_of_eqv _ _ 4 X3 eq_refl); simp_regs; exact E4).
  assert (E3_8 : getr R3 8 = Z_to_bv 64 (rec_entry G_REC REC_SC R))
    by (rewrite (getr_of_eqv _ _ 8 X3 eq_refl); simp_regs; exact E8).
  assert (E3_10 : getr R3 10 = Z_to_bv 64 (sup_host_setting_len toks + 1))
    by (rewrite (getr_of_eqv _ _ 10 X3 eq_refl); simp_regs; reflexivity).
  assert (E3_9 : getr R3 9 = getr regs 11).
  { rewrite (getr_of_eqv _ _ 9 X3 eq_refl). simp_regs. rewrite A11. reflexivity. }
  assert (E3_18 : getr R3 18 = getr regs 12).
  { rewrite (getr_of_eqv _ _ 18 X3 eq_refl). simp_regs. rewrite A12, LT. reflexivity. }
  assert (KE3 : hsu_kx hsu_KX regs R3).
  { apply (hsu_kx_trans _ regs R2 R3 KE2). unfold hsu_KX. hsu_kx_tac X3. }
  assert (SP3 : spZ R3 = bv_unsigned sp - 96) by (unfold spZ; rewrite E3_2; apply unsigned_lit; lia).
  replace (Z_to_bv 64 0x15a88) with (Z_to_bv 64 XMALLOC) by reflexivity.
  pose proof (XM fx') as XMC. unfold xmalloc_contract in XMC. rewrite SEGS in XMC.
  assert (XS : xmalloc_size (sup_host_setting_len toks + 1) = sup_host_setting_len toks + 1).
  { unfold xmalloc_size. rewrite (proj2 (Z.eqb_neq _ 0)) by (rewrite <- hsu_len_eq; lia). reflexivity. }
  eapply SR_bind.
  { apply (XMC L2 A2 R3 m3 md2 (sup_host_setting_len toks + 1) (sb_shift b A A2)).
    - apply (call_pre_k_of_rjr B _ 8432 (bv_unsigned sp) rec_area _ L A mem md L2 A2 m3 md2 XMALLOC_K R3 RJ3).
      + rewrite E3_1. apply bv_eq. vm_compute. reflexivity.
      + rewrite SP3. replace (bv_unsigned sp - 96) with (bv_unsigned sp + (-6) * 16) by ring.
        rewrite Z.mod_add by lia. exact HAL.
      + unfold XMALLOC_K, ALLOC_STACK. lia.
      + rewrite SP3. unfold XMALLOC_K, ALLOC_STACK. lia.
      + rewrite SP3. lia.
      + rewrite E3_4. exact HTP.
    - exact E3_10.
    - pose proof TLEN as TL'. rewrite <- hsu_len_eq in TL' |- *. unfold LMAX in *. lia.
    - exact RS3.
    - rewrite XS. apply hsu_room; [pose proof TLEN as TL'; rewrite <- hsu_len_eq in TL' |- *; unfold LMAX in *; lia|].
      eapply sb_le_trans; [apply sb_malloc_mono; exact BLE2|].
      unfold sb_mallocs, sup_host_setting_sizes. cbn [fold_left]. apply sb_le_malloc. lia.
    - exact RA3. }
  intros c4 RET. unfold malloc_ret in RET. rewrite XS in RET.
  destruct RET as (L4 & A4 & R4 & m4 & md4 & res & -> & POST4 & A04 & NZ & AL16 & FB4 & BLK4 & BK4 & RA4 & GK4 & UB4
    & INI4 & RGN4 & RS4).
  rewrite SEGS in RA4 |- *.
  pose proof (sinvT_malloc B API SEGS ERRNO_LOW GOTG GUARDG GFACT GOWN AX 8432 (bv_unsigned sp) L A mem md O L2 A2 m3 md2 _
                O2 b XMALLOC_K R3 L4 A4 R4 m4 md4 res (sup_host_setting_len toks + 1) SI3
                ltac:(rewrite SP3; unfold XMALLOC_K, ALLOC_STACK; lia) ltac:(rewrite SP3; lia) POST4
                ltac:(rewrite <- hsu_len_eq; lia) FB4 BLK4 UB4 BK4 RGN4 INI4 RS4 RA4 GK4) as SIT.
  assert (INB : In (res, sup_host_setting_len toks + 1) (blocks L4 A4)).
  { destruct BLK4 as (bl1 & bl2 & EB1 & _). rewrite EB1. apply in_or_app. right. left. reflexivity. }
  unfold blocks in INB. apply in_map_iff in INB as ([q k'] & EQ & QIN). cbn [fst snd] in EQ.
  injection EQ as QE1 QE2. subst k'.
  rewrite <- QE1 in SIT, A04, AL16.
  pose proof POST4 as (PM4 & _ & _ & _ & _ & RP4 & _).
  assert (BLE4 : sb_le (sb_shift b A A4)
                   (sb_malloc (sb_malloc (sb_malloc b (Z.of_nat (length line) + 1))
                      (Z.of_nat (length (dec (Z.of_nat (length toks)))) + 1)) (sup_host_setting_len toks + 1))).
  { destruct BLK4 as (bl1 & bl2 & EB1 & EB2).
    rewrite <- (sb_shift_trans b A A2 A4).
    rewrite <- (sb_shift_add (sb_shift b A A2) L2 A2 L4 A4 bl1 bl2 res _ EB1 EB2).
    apply sb_malloc_mono. exact BLE2. }
  pose proof RJ3 as (HM3 & _).
  assert (FR4 : rw_cells rsegs m4 (bv_unsigned sp - 80)
                  [C8 (getr regs 24); C8 (getr regs 23); C8 (getr regs 22); C8 (getr regs 21); C8 (getr regs 20);
                   C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]).
  { apply (rw_cells_transfer rsegs m3); [exact FR3|]. intros i Hi. cbn in Hi.
    destruct (hsu_keep_hi B API SEGS ERRNO_LOW XMALLOC_K L2 A2 R3 m3 md2 _ L4 A4 R4 m4 md4 (bv_unsigned sp - 80 + i)
                HM3 POST4 ltac:(lia) ltac:(rewrite SP3; unfold XMALLOC_K, ALLOC_STACK; lia)) as [K1 K2].
    - intros H. exact H.
    - split; [exact K1 | exact (proj1 K2)]. }
  rewrite E3_1.
  apply (hsu_am fx' L4 A4 R4 m4 md4 O2 q SIT QIN AL16 BLE4 FK).
  - exact (eq_trans (RP4 2 ltac:(unfold callee_saved; lia)) E3_2).
  - exact (eq_trans (RP4 4 ltac:(unfold callee_saved; lia)) E3_4).
  - exact (eq_trans (RP4 8 ltac:(unfold callee_saved; lia)) E3_8).
  - exact (eq_trans (RP4 9 ltac:(unfold callee_saved; lia)) E3_9).
  - exact (eq_trans (RP4 18 ltac:(unfold callee_saved; lia)) E3_18).
  - exact A04.
  - exact (hsu_kx_trans _ regs R3 R4 KE3 (hsu_kx_of_pres _ _ _ RP4)).
  - exact FR4.
Qed.

Lemma hsu_args : forall (fx' : YK11.FPState) L2 A2 R3 m3 md2 O2 slack,
  sinv B API SUP_HOST_SETTING_K (spZ regs) L A mem md O L2 A2 m3 md2
    (rec_record R REC_HOST_SETTING [canon line]) O2 b ->
  sb_le (sb_shift b A A2) (sb_malloc b (Z.of_nat (length line) + 1)) ->
  fp_kept fx fx' ->
  getr R3 1 = Z_to_bv 64 0x16880 -> getr R3 2 = Z_to_bv 64 (spZ regs - 96) -> getr R3 4 = getr regs 4 ->
  getr R3 8 = Z_to_bv 64 (rec_entry G_REC REC_SC R) -> getr R3 10 = Z_to_bv 64 (rec_entry G_REC REC_SC R) ->
  getr R3 11 = Z_to_bv 64 (spZ regs - 96) ->
  getr R3 9 = getr regs 11 -> getr R3 18 = getr regs 12 ->
  hsu_kx hsu_KX regs R3 -> hsu_fr m3 ->
  length slack = (15 - length (dec (Z.of_nat (length toks))))%nat ->
  bytes_at rsegs m3 (spZ regs - 96) (dec (Z.of_nat (length toks)) ++ Z_to_bv 8 0 :: slack) ->
  SR rsegs (mkCfg (@mkst fx' R3 (Z_to_bv 64 ARG_S) m3 (seg_rom rsegs)) md2)
    (sup_host_setting_ret (fx := fx) B API L A regs mem md line toks R O b).
Proof.
  intros fx' L2 A2 R3 m3 md2 O2 slack SI BLE FK E1 E2 E4 E8 E10 E11 E9 E18 KE FR SL BUF.
  unfold hsu_fr in FR.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  unfold SUP_HOST_SETTING_K in HCEIL, SI.
  pose proof (dec_length (Z.of_nat (length toks)) ltac:(lia)) as DL.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (SP3 : spZ R3 = bv_unsigned sp - 96) by (unfold spZ; rewrite E2; apply unsigned_lit; lia).
  apply (sinv_arg_sn (fx := fx') B API SEGS ERRNO_LOW GFACT GOWN AX (ARGS fx') 8432 (bv_unsigned sp) L A mem md O
           L2 A2 m3 md2 R REC_HOST_SETTING [canon line] O2 b R3 (bv_unsigned sp - 96)
           (Some (dec (Z.of_nat (length toks)))) _ SI).
  - cbn [length]. lia.
  - rewrite E1. apply bv_eq. vm_compute. reflexivity.
  - rewrite SP3. replace (bv_unsigned sp - 96) with (bv_unsigned sp + (-6) * 16) by ring.
    rewrite Z.mod_add by lia. exact HAL.
  - rewrite SP3. unfold ARG_S_K, XMALLOC_K, ALLOC_STACK. lia.
  - rewrite SP3. lia.
  - rewrite E4. exact HTP.
  - exact E10.
  - exact E11.
  - cbn [arg_s_src]. rewrite SEGS.
    split; [lia|]. split; [apply dec_no0|]. split; [unfold LMAX; lia|].
    exists slack. split; [exact BUF|].
    assert (SLZ : Z.of_nat (length slack) = 15 - Z.of_nat (length (dec (Z.of_nat (length toks)))))
      by (rewrite SL; lia).
    split.
    { rewrite SLZ. pose proof (Z.div_mod (bv_unsigned sp) 16 ltac:(lia)) as DS. rewrite HAL, Z.add_0_r in DS.
      Z.div_mod_to_equations. lia. }
    split; [right; rewrite SP3; lia|].
    left. rewrite SP3. split; lia.
  - cbn [sarg]. eapply room_slots_mono; [| | exact ROOM].
    + eapply sb_le_trans; [apply sb_malloc_mono; exact BLE|].
      unfold sb_mallocs, sup_host_setting_sizes. cbn [fold_left].
      eapply sb_le_trans; [|apply sb_le_malloc; lia].
      eapply sb_le_trans; [|apply sb_le_malloc; pose proof (hsu_len_nn toks) as LNN; rewrite hsu_len_eq in LNN; lia].
      apply sb_le_refl.
    + unfold LMAX. lia.
  - intros L4 A4 R4 m4 md4 p SI4 SB4 INI4 RP4 FK4.
    cbn [sarg app] in SI4, SB4.
    rewrite E1.
    assert (FR4 : rw_cells rsegs m4 (bv_unsigned sp - 80)
                    [C8 (getr regs 24); C8 (getr regs 23); C8 (getr regs 22); C8 (getr regs 21); C8 (getr regs 20);
                     C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]).
    { apply (rw_cells_transfer rsegs m3); [exact FR|]. intros i Hi. cbn in Hi.
      destruct (FK4 (bv_unsigned sp - 80 + i) ltac:(rewrite SP3; lia)) as [K1 K2]. split; [exact K1 | exact (proj1 K2)]. }
    assert (BLE4 : sb_le (sb_shift b A A4) (sb_malloc (sb_malloc b (Z.of_nat (length line) + 1))
                     (Z.of_nat (length (dec (Z.of_nat (length toks)))) + 1))).
    { rewrite SB4. apply sb_malloc_mono. exact BLE. }
    apply (hsu_m fx' L4 A4 R4 m4 md4 (O2 ++ [(p, Z.of_nat (length (dec (Z.of_nat (length toks)))) + 1)]) SI4 BLE4 FK).
    + exact (eq_trans (RP4 2 ltac:(unfold callee_saved; lia)) E2).
    + exact (eq_trans (RP4 4 ltac:(unfold callee_saved; lia)) E4).
    + exact (eq_trans (RP4 8 ltac:(unfold callee_saved; lia)) E8).
    + exact (eq_trans (RP4 9 ltac:(unfold callee_saved; lia)) E9).
    + exact (eq_trans (RP4 18 ltac:(unfold callee_saved; lia)) E18).
    + exact (hsu_kx_trans _ regs R3 R4 KE (hsu_kx_of_pres _ _ _ RP4)).
    + unfold hsu_fr. exact FR4.
Qed.

Lemma hsu_snp : forall L2 A2 R2 m2 md2 O2,
  sinv B API SUP_HOST_SETTING_K (spZ regs) L A mem md O L2 A2 m2 md2
    (rec_record R REC_HOST_SETTING [canon line]) O2 b ->
  sb_le (sb_shift b A A2) (sb_malloc b (Z.of_nat (length line) + 1)) ->
  getr R2 2 = Z_to_bv 64 (spZ regs - 96) -> getr R2 4 = getr regs 4 ->
  getr R2 8 = Z_to_bv 64 (rec_entry G_REC REC_SC R) ->
  getr R2 9 = getr regs 11 -> getr R2 18 = getr regs 12 ->
  hsu_kx hsu_KX regs R2 -> hsu_fr m2 ->
  SR rsegs (mkCfg (mkst R2 (Z_to_bv 64 0x1685c) m2 (seg_rom rsegs)) md2)
    (sup_host_setting_ret (fx := fx) B API L A regs mem md line toks R O b).
Proof.
  intros L2 A2 R2 m2 md2 O2 SI BLE E2 E4 E8 E9 E18 KE FR.
  unfold hsu_fr in FR.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC. pose proof wx_apart_rsegs as WX.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  unfold SUP_HOST_SETTING_K in HCEIL, HWS, SI, TS.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  pose proof SI as (RJ & GR2 & _ & _ & _ & RA2 & F182 & _).
  pose proof RJ as (HM2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSC2 & _).
  rewrite SEGS in HSC2.
  destruct (mr_model B _ LAWS L2 A2 m2 md2 HM2) as (Hh2 & Hl2 & _).
  pose proof F182 as (GG & canary & GW).
  assert (GGb : bytes_at rsegs m2 snprintf_c.GOT_GUARD (Mem.le8 (Z_to_bv 64 snprintf_c.GUARD))).
  { destruct GG as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (GWb : bytes_at rsegs m2 snprintf_c.GUARD (Mem.le8 canary)).
  { destruct GW as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  pose proof (bytes_at_normalize_cj_low rsegs m2 snprintf_c.GOT_GUARD (Mem.le8 (Z_to_bv 64 snprintf_c.GUARD)) RA2
    ltac:(rewrite Mem.length_le8; unfold snprintf_c.GOT_GUARD, TASK_SIZE; lia) GGb) as GGn.
  pose proof (bytes_at_normalize_cj_low rsegs m2 snprintf_c.GUARD (Mem.le8 canary) RA2
    ltac:(rewrite Mem.length_le8; unfold snprintf_c.GUARD, TASK_SIZE; lia) GWb) as GWn.
  assert (STn : stk rsegs (normalize_cj rsegs m2) (bv_unsigned sp - 8432) (bv_unsigned sp - 80)).
  { apply stk_normalize_cj; [lia | lia | intros a Ha; apply HSC2; left; lia]. }
  assert (Q2 : reg_get R2 2 = Z_to_bv 64 (bv_unsigned sp - 96)) by exact E2.
  assert (Q18 : reg_get R2 18 = Z_to_bv 64 (Z.of_nat (length toks))) by exact (eq_trans E18 A12).
  eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite Q2, Q18.
    eapply (evt_normalize_cj rsegs); [exact WX | exact RA2 |].
    eapply (hsu_run1 SNP) with (lo := bv_unsigned sp - 8432) (canary := canary).
    - lia.
    - rewrite unsigned_lit by lia. replace (bv_unsigned sp - 96 + 16) with (bv_unsigned sp - 80) by ring. exact STn.
    - rewrite unsigned_lit by lia. unfold SNPRINTF_K. lia.
    - lia.
    - rewrite unsigned_lit by lia. lia.
    - exact FRM.
    - exact (mem_inv_cj_inv rsegs _ (mem_inv_cj_normalize rsegs m2)).
    - exact (mem_inv_cj_task rsegs _ (mem_inv_cj_normalize rsegs m2)).
    - exact GGn.
    - exact GWn. }
  intros ms3 (can3 & (s3n & Q3 & REL3 & RO3) & EQ3).
  destruct Q3 as (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F1 & fc1 & m3n & slack
    & -> & MU3n & WM3n & MI3n & FRM1 & FK1 & SL & BUF3n).
  destruct (ms_rel_cj_MS _ _ _ _ _ _ _ _ REL3) as [EC3 MR3r].
  revert EC3 MR3r RO3 EQ3. generalize (ms_mem can3) as m3. intros m3 EC3 MR3r RO3 EQ3. subst can3.
  pose proof (munch_rel_cj rsegs _ _ _ _ _ (mem_rel_cj_normalize rsegs m2 RA2) MR3r RO3 MU3n) as MU3.
  pose proof (wmono_rel_cj rsegs _ _ _ _ (mem_rel_cj_normalize rsegs m2 RA2) MR3r RO3 WM3n) as WM3.
  pose proof (bytes_at_rel_cj rsegs _ _ _ _ MR3r BUF3n) as BUF3.
  destruct (eqv_mkst_fx _ _ _ _ _ _ _ EQ3) as (R3 & -> & X3).
  clear MU3n WM3n MI3n BUF3n EQ3 MR3r.
  rewrite unsigned_lit in MU3, BUF3 by lia.
  assert (FKA : fp_kept fx (mkFP F1 fc1)).
  { unfold fp_kept. cbn [fp_regs fp_csr]. split; [exact FRM1|].
    intros r Hr. apply FK1. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
    unfold fs_saved in Hr. rewrite Z.mod_small by lia. lia. }
  pose proof (sinv_stack B API SEGS GOWN AX 8432 (bv_unsigned sp) L A mem md O L2 A2 m2 md2 _ _ b m3 _ SI MU3 WM3
                ltac:(intros a Ra Hm; cbn [outside] in Hm; lia)) as SI3.
  assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp - 80)
                  [C8 (getr regs 24); C8 (getr regs 23); C8 (getr regs 22); C8 (getr regs 21); C8 (getr regs 20);
                   C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]).
  { apply (rw_cells_transport rsegs _ m2 m3 _ _ FR MU3 WM3). cbn [disjoint_from cells_size csize Nat.add].
    repeat split; lia. }
  apply (hsu_args (mkFP F1 fc1) L2 A2 R3 m3 md2 O2 slack SI3 BLE FKA).
  - rewrite (getr_of_eqv _ _ 1 X3 eq_refl). simp_regs. reflexivity.
  - rewrite (getr_of_eqv _ _ 2 X3 eq_refl). simp_regs. reflexivity.
  - rewrite (getr_of_eqv _ _ 4 X3 eq_refl). simp_regs. exact E4.
  - rewrite (getr_of_eqv _ _ 8 X3 eq_refl). simp_regs. exact E8.
  - rewrite (getr_of_eqv _ _ 10 X3 eq_refl). simp_regs. exact E8.
  - rewrite (getr_of_eqv _ _ 11 X3 eq_refl). simp_regs. reflexivity.
  - rewrite (getr_of_eqv _ _ 9 X3 eq_refl). simp_regs. exact E9.
  - rewrite (getr_of_eqv _ _ 18 X3 eq_refl). simp_regs. exact (eq_sym A12).
  - apply (hsu_kx_trans _ regs R2 R3 KE). unfold hsu_KX. hsu_kx_tac X3.
  - unfold hsu_fr. exact FR3.
  - exact SL.
  - exact BUF3.
Qed.

Lemma hsu_argl : forall L1 A1 R1 m1 md1 O1,
  sinv B API SUP_HOST_SETTING_K (spZ regs) L A mem md O L1 A1 m1 md1 (rec_record R REC_HOST_SETTING []) O1 b ->
  sb_le (sb_shift b A A1) b ->
  getr R1 1 = Z_to_bv 64 0x1685c -> getr R1 2 = Z_to_bv 64 (spZ regs - 96) -> getr R1 4 = getr regs 4 ->
  getr R1 8 = Z_to_bv 64 (rec_entry G_REC REC_SC R) -> getr R1 10 = Z_to_bv 64 (rec_entry G_REC REC_SC R) ->
  getr R1 11 = getr regs 10 -> getr R1 9 = getr regs 11 -> getr R1 18 = getr regs 12 ->
  hsu_kx hsu_KX regs R1 -> hsu_fr m1 ->
  bytes_at rsegs m1 (rec_entry G_REC REC_SC R + CALL_OFF_NARGS) (le4 (Z_to_bv 64 0)) ->
  SR rsegs (mkCfg (mkst R1 (Z_to_bv 64 0x16608) m1 (seg_rom rsegs)) md1)
    (sup_host_setting_ret (fx := fx) B API L A regs mem md line toks R O b).
Proof.
  intros L1 A1 R1 m1 md1 O1 SI1 BLE1 E1 E2 E4 E8 E10 E11 E9 E18 KE1 FR1 NA1.
  unfold hsu_fr in FR1.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  unfold SUP_HOST_SETTING_K in HCEIL, SI1.
  assert (AKL : ARG_LINE_K = 8272) by reflexivity.
  assert (HN : (length (r_calls R) <= 16)%nat) by exact (rec_rep_calls_le _ _ _ _ _ _ _ _ GR).
  pose proof (rec_entry_bounds R HN) as ER.
  pose proof SA as SA0. unfold SUP_HOST_SETTING_K in SA0.
  set (e := rec_entry G_REC REC_SC R) in *.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (SP1 : spZ R1 = bv_unsigned sp - 96) by (unfold spZ; rewrite E2; apply unsigned_lit; lia).
  pose proof SI1 as (RJ1 & _ & _ & _ & _ & RA1 & F181 & RS1).
  pose proof RJ1 as (HM1 & _).
  pose proof RA as RA0. rewrite SEGS in RA0.
  destruct (hsu_str 8432 (bv_unsigned sp) L A mem md O L1 A1 m1 md1 _ O1 b pl line SI1 RA0 SA0)
    as (slack & PR & Hp0 & BS & N0 & LX & ALN & DJ & HOME & NRA).
  pose proof (hsu_len_nn toks) as LNN. rewrite hsu_len_eq in LNN.
  pose proof ARGL as AL. unfold arg_line_contract in AL. rewrite SEGS in AL.
  eapply SR_bind.
  { apply (AL L1 A1 R1 m1 md1 e pl 0 line slack (sb_shift b A A1)).
    - apply (call_pre_k_of_rjr B _ 8432 (bv_unsigned sp) rec_area _ L A mem md L1 A1 m1 md1 ARG_LINE_K R1 RJ1).
      + rewrite E1. apply bv_eq. vm_compute. reflexivity.
      + rewrite SP1. replace (bv_unsigned sp - 96) with (bv_unsigned sp + (-6) * 16) by ring.
        rewrite Z.mod_add by lia. exact HAL.
      + lia.
      + rewrite SP1. lia.
      + rewrite SP1. lia.
      + rewrite E4. exact HTP.
    - exact E10.
    - rewrite E11. exact A10.
    - exact (proj2 (proj2 ER)).
    - exact (proj1 ER).
    - exact (proj1 (proj2 ER)).
    - apply glob_wr_at; unfold REC_SC, G_REC, REC_SIZE, CALL_SIZE, GLOB_LO, GLOB_N in *; lia.
    - exact NA1.
    - lia.
    - exact BS.
    - exact N0.
    - exact LX.
    - exact ALN.
    - rewrite SP1. lia.
    - rewrite SP1. destruct HOME as [H1|[H1|H1]]; [left; lia | right; left; exact H1 | right; right; exact H1].
    - unfold iv_apart. apply (hsu_nra_apart pl _ e (e + CALL_SIZE)).
      + intros a Ha. apply NRA. rewrite length_app. cbn [length]. lia.
      + exact (proj1 ER).
      + exact (proj1 (proj2 ER)).
      + unfold CALL_SIZE. lia.
      + lia.
    - exact RS1.
    - apply hsu_room; [unfold LMAX in *; lia|].
      eapply sb_le_trans; [apply sb_malloc_mono; exact BLE1|].
      unfold sb_mallocs, sup_host_setting_sizes. cbn [fold_left].
      eapply sb_le_trans; [|apply sb_le_malloc; lia].
      eapply sb_le_trans; [|apply sb_le_malloc; lia].
      eapply sb_le_trans; [|apply sb_le_malloc; lia].
      apply sb_le_refl.
    - exact RA1. }
  intros c3 (L3 & A3 & R4 & m3 & md3 & -> & BK3 & UB3 & _ & RA3 & GK3 & RGN3 & ALT3).
  destruct ALT3 as [(H6 & _)|(_ & p2 & POST3 & Hp2 & _ & FB3 & BLK3 & BN3 & BS3 & BX3 & INI3 & RS3)]; [lia|].
  rewrite SEGS in RA3, BN3, BS3, BX3 |- *.
  pose proof POST3 as (PM3 & _ & _ & _ & _ & RP4 & _).
  destruct (ax_statics AX L3 A3 m3 md3 PM3) as (_ & (g & Hg & HWg) & _).
  rewrite GUARDG, SEGS in HWg.
  assert (F183 : f18_words rsegs m3).
  { apply (f18_words_after m1 m3 g F181); [|exact Hg | exact HWg].
    intros i Hi. pose proof (GK3 i Hi) as G. rewrite GOTG, SEGS in G. exact G. }
  pose proof (sinv_arg B API SEGS ERRNO_LOW GFACT GOWN AX 8432 (bv_unsigned sp) L A mem md O L1 A1 m1 md1 R
                REC_HOST_SETTING [] O1 b ARG_LINE_K R1 _ L3 A3 R4 m3 md3 (canon line) p2 (Z.of_nat (length line) + 1)
                SI1 ltac:(cbn; lia) ltac:(rewrite SP1; lia) ltac:(rewrite SP1; lia) POST3
                ltac:(intros a Ha; cbv beta in Ha; cbn [length Z.of_nat]; lia)
                Hp2 FB3 BLK3 UB3 BK3 RGN3 BN3 BS3 BX3 (canon_no0 line N0)
                ltac:(pose proof (canon_length line); unfold LMAX in *; lia)
                ltac:(pose proof (canon_length line); unfold LMAX in *; lia)
                INI3 RS3 RA3 F183) as SI3.
  cbn [app] in SI3.
  assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp - 80)
                  [C8 (getr regs 24); C8 (getr regs 23); C8 (getr regs 22); C8 (getr regs 21); C8 (getr regs 20);
                   C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]).
  { apply (rw_cells_transfer rsegs m1); [exact FR1|]. intros i Hi. cbn in Hi.
    destruct FB3 as (_ & FBb & _).
    destruct (hsu_keep_hi B API SEGS ERRNO_LOW ARG_LINE_K L1 A1 R1 m1 md1 _ L3 A3 R4 m3 md3 (bv_unsigned sp - 80 + i)
                HM1 POST3 ltac:(lia) ltac:(rewrite SP1; lia)) as [K1 K2].
    - intros H. cbv beta in H. unfold G_REC, REC_SIZE, CALL_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS in *. lia.
    - split; [exact K1 | exact (proj1 K2)]. }
  assert (BLE3 : sb_le (sb_shift b A A3) (sb_malloc b (Z.of_nat (length line) + 1))).
  { destruct BLK3 as (bl1 & bl2 & EB1 & EB2).
    rewrite <- (sb_shift_trans b A A1 A3).
    rewrite <- (sb_shift_add (sb_shift b A A1) L1 A1 L3 A3 bl1 bl2 p2 _ EB1 EB2).
    apply sb_malloc_mono. exact BLE1. }
  rewrite E1.
  apply (hsu_snp L3 A3 R4 m3 md3 (O1 ++ [(p2, Z.of_nat (length line) + 1)]) SI3 BLE3).
  - exact (eq_trans (RP4 2 ltac:(unfold callee_saved; lia)) E2).
  - exact (eq_trans (RP4 4 ltac:(unfold callee_saved; lia)) E4).
  - exact (eq_trans (RP4 8 ltac:(unfold callee_saved; lia)) E8).
  - exact (eq_trans (RP4 9 ltac:(unfold callee_saved; lia)) E9).
  - exact (eq_trans (RP4 18 ltac:(unfold callee_saved; lia)) E18).
  - exact (hsu_kx_trans _ regs R1 R4 KE1 (hsu_kx_of_pres _ _ _ RP4)).
  - unfold hsu_fr. exact FR3.
Qed.

Lemma hsu_main :
  SR (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 SUP_HOST_SETTING) mem (seg_rom (ms_segs B))) md)
    (sup_host_setting_ret (fx := fx) B API L A regs mem md line toks R O b).
Proof.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & _).
  unfold SUP_HOST_SETTING_K in PRK, HCEIL, HWS, TS.
  unfold SUP_HOST_SETTING.
  pose proof GR as GR0. pose proof RA as RA0. pose proof F18 as F180.
  rewrite SEGS in GR0, RA0, F180, HWS |- *.
  pose proof (sinv_init B API 8432 L A regs mem md R O b PRK ltac:(lia) GR0 RA0 F180 RES) as SI0.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (ST : stk rsegs mem (bv_unsigned sp - 8432) (bv_unsigned sp)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (W : writable_at rsegs mem a) by (apply HWS; lia).
    split; [exact W|].
    destruct (writable_hi_present mem a ltac:(lia) W) as [bb E]. exists bb. unfold mrd, wa. rewrite E. reflexivity. }
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp. eapply hsu_run0; [exact ST | lia | lia]. }
  intros ms1 (can1 & (m1 & -> & MU1 & WM1 & FR1) & EQ1).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
  assert (E1_1 : getr R1 1 = Z_to_bv 64 0x16850) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 96))
    by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; f_equal; lia).
  assert (E1_4 : getr R1 4 = getr regs 4) by (rewrite (getr_of_eqv _ _ 4 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_10 : getr R1 10 = Z_to_bv 64 REC_HOST_SETTING)
    by (rewrite (getr_of_eqv _ _ 10 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_9 : getr R1 9 = getr regs 11) by (rewrite (getr_of_eqv _ _ 9 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_18 : getr R1 18 = getr regs 12) by (rewrite (getr_of_eqv _ _ 18 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_19 : getr R1 19 = getr regs 10) by (rewrite (getr_of_eqv _ _ 19 X1 eq_refl); simp_regs; reflexivity).
  assert (KX1 : hsu_kx hsu_KX regs R1) by (unfold hsu_KX; hsu_kx_tac X1).
  assert (SP1 : spZ R1 = bv_unsigned sp - 96) by (unfold spZ; rewrite E1_2; apply unsigned_lit; lia).
  assert (FR1' : rw_cells rsegs m1 (bv_unsigned sp - 80)
                   [C8 (getr regs 24); C8 (getr regs 23); C8 (getr regs 22); C8 (getr regs 21); C8 (getr regs 20);
                    C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]).
  { replace (bv_unsigned sp - 80) with (bv_unsigned sp + -80) by ring. exact FR1. }
  pose proof (sinv_stack B API SEGS GOWN AX 8432 (bv_unsigned sp) L A mem md O L A mem md R O b m1 _ SI0 MU1 WM1
                ltac:(intros a Ra Hm; cbn [outside] in Hm; lia)) as SI1.
  replace (Z_to_bv 64 0x1612c) with (Z_to_bv 64 RECORD) by reflexivity.
  apply (sinv_record B API SEGS ERRNO_LOW AX REC 8432 (bv_unsigned sp) L A mem md O L A m1 md R O b R1
           REC_HOST_SETTING _ SI1).
  - rewrite E1_1. apply bv_eq. vm_compute. reflexivity.
  - rewrite SP1. replace (bv_unsigned sp - 96) with (bv_unsigned sp + (-6) * 16) by ring.
    rewrite Z.mod_add by lia. exact HAL.
  - rewrite SP1. unfold RECORD_K, ALLOC_STACK. lia.
  - rewrite SP1. lia.
  - rewrite E1_4. exact HTP.
  - exact E1_10.
  - unfold REC_FN_COUNT, REC_HOST_SETTING. lia.
  - intros L2 A2 R2 m2 md2 O2 SI2 BLE2 RP2 R10 FK2.
    rewrite sb_shift_refl in BLE2.
    rewrite E1_1.
    assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp - 80)
                    [C8 (getr regs 24); C8 (getr regs 23); C8 (getr regs 22); C8 (getr regs 21); C8 (getr regs 20);
                     C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]).
    { apply (rw_cells_transfer rsegs m1); [exact FR1'|]. intros i Hi. cbn in Hi.
      destruct (FK2 (bv_unsigned sp - 80 + i) ltac:(rewrite SP1; lia)) as [K1 K2]. split; [exact K1 | exact (proj1 K2)]. }
    pose proof SI2 as (RJ2 & GR2 & _). pose proof RJ2 as (HM2 & _).
    destruct (mr_model _ _ LAWS _ _ _ _ HM2) as (Hh2 & Hl2 & _).
    destruct (rec_entry_at rsegs L2 A2 m2 R REC_HOST_SETTING [] O2 GR2) as (P0 & CA).
    pose proof CA as (_ & _ & _ & _ & NA2 & _). cbn [snd length Z.of_nat] in NA2.
    eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
    { rewrite canon_mkst. unfold Regs6ss.mkR_of. apply hsu_mid1. }
    intros ms3 (can3 & -> & EQ3).
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ3 eq_refl eq_refl) as (R3 & -> & X3).
    apply (hsu_argl L2 A2 R3 m2 md2 O2 SI2 BLE2).
    + rewrite (getr_of_eqv _ _ 1 X3 eq_refl). simp_regs. reflexivity.
    + rewrite (getr_of_eqv _ _ 2 X3 eq_refl). simp_regs. exact (eq_trans (RP2 2 ltac:(unfold callee_saved; lia)) E1_2).
    + rewrite (getr_of_eqv _ _ 4 X3 eq_refl). simp_regs. exact (eq_trans (RP2 4 ltac:(unfold callee_saved; lia)) E1_4).
    + rewrite (getr_of_eqv _ _ 8 X3 eq_refl). simp_regs. exact R10.
    + rewrite (getr_of_eqv _ _ 10 X3 eq_refl). simp_regs. exact R10.
    + rewrite (getr_of_eqv _ _ 11 X3 eq_refl). simp_regs. exact (eq_trans (RP2 19 ltac:(unfold callee_saved; lia)) E1_19).
    + rewrite (getr_of_eqv _ _ 9 X3 eq_refl). simp_regs. exact (eq_trans (RP2 9 ltac:(unfold callee_saved; lia)) E1_9).
    + rewrite (getr_of_eqv _ _ 18 X3 eq_refl). simp_regs. exact (eq_trans (RP2 18 ltac:(unfold callee_saved; lia)) E1_18).
    + apply (hsu_kx_trans _ regs R1 R3 KX1). apply (hsu_kx_trans _ R1 R2 R3 (hsu_kx_of_pres _ _ _ RP2)).
      unfold hsu_KX. hsu_kx_tac X3.
    + unfold hsu_fr. exact FR2.
    + exact NA2.
Qed.

End Run.

Theorem sup_host_setting_holds : sup_host_setting_contract B API.
Proof.
  unfold sup_host_setting_contract.
  intros L A regs mem md pl ptok ps line toks R O b PRE A10 A11 A12 NT SA PT0 PT8 PTB PTW PTH PTR TKS TLEN GR RA FRM
    F18 RES ROOM.
  eapply hsu_main; eassumption.
Qed.

End P.
