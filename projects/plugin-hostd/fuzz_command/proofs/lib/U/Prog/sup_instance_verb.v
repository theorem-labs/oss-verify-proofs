(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 1088 of its 1116 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/chain_words.v, with its module paths, addresses and numbers changed; 2641 of its 2742 lines of code are new or changed and 1015 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/sup_host_setting.v, with its addresses and numbers changed; 1126 of its 1319 lines of code are new or changed and 2549 lines of the source are left out. *)
From Stdlib Require Import String ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes FP.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0 MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import printf_facts_c snprintf_c RecAns
  rec_shape_of_c strspn_c strcspn_c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Lemma siv_pf_dec : forall v, (-2^31 <= v < 2^31)%Z -> pf_bytes (pf_dec v) = dec v.
Proof.
  intros c Hc. unfold pf_dec, dec. unfold pf_bytes.
  assert (P : (10 ^ Z.of_nat (S 9) = 10000000000)%Z) by reflexivity.
  destruct (Z.ltb_spec c 0) as [N|N].
  - cbn [map app]. f_equal. replace (Z.abs c) with (- c)%Z by lia.
    exact (pf_digits_digits 9 11 (- c) [] ltac:(rewrite P; lia) ltac:(lia)).
  - cbn [app]. replace (Z.abs c) with c by lia.
    exact (pf_digits_digits 9 11 c [] ltac:(rewrite P; lia) ltac:(lia)).
Qed.

Definition SIV_FMT : list Z := [37%Z; 100%Z].
Definition SIV_PS : list pf_piece := [Pd].

Lemma siv_parse : pf_parse SIV_FMT = Some SIV_PS.
Proof. reflexivity. Qed.

Lemma siv_text : forall v, pf_text SIV_PS [AInt v] = Some (pf_dec v).
Proof. intros v. cbn. rewrite app_nil_r. reflexivity. Qed.

Lemma siv_fmt_at : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x10828 (pf_bytes (SIV_FMT ++ [0%Z])).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | lia | cbn; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Definition siv_rom_chk (a : Z) (bs : list byte) : bool :=
  forallb (fun i => ro_addr rsegs (Z_to_bv 64 (a + Z.of_nat i)) &&
     match seg_rom rsegs (Z_to_bv 64 (a + Z.of_nat i)), nth_error bs i with
     | Some b, Some c => Z.eqb (bv_unsigned b) (bv_unsigned c)
     | _, _ => false
     end) (seq 0 (length bs)).

Lemma siv_rom_chk_at : forall a bs i, siv_rom_chk a bs = true -> (i < length bs)%nat ->
  ro_addr rsegs (Z_to_bv 64 (a + Z.of_nat i)) = true /\
  seg_rom rsegs (Z_to_bv 64 (a + Z.of_nat i)) = nth_error bs i.
Proof.
  intros a bs i C Hi. unfold siv_rom_chk in C.
  pose proof (proj1 (forallb_forall _ _) C i ltac:(apply in_seq; lia)) as Ci. cbv beta in Ci.
  apply andb_prop in Ci as [Cr Cv]. split; [exact Cr|].
  destruct (seg_rom rsegs (Z_to_bv 64 (a + Z.of_nat i))) as [b|]; [|discriminate].
  destruct (nth_error bs i) as [c|]; [|discriminate].
  apply Z.eqb_eq in Cv. f_equal. apply bv_eq. exact Cv.
Qed.

Lemma siv_rom_chk_bytes : forall m a bs, ro_agree rsegs m -> (0 <= a)%Z -> (a + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  siv_rom_chk a bs = true -> bytes_at rsegs m a bs.
Proof.
  intros m a bs RA H0 H1 C. split; [lia|]. split; [lia|]. intros i Hi.
  destruct (siv_rom_chk_at a bs i C Hi) as [Cr Cv]. unfold wa. rewrite (RA _ Cr). exact Cv.
Qed.

Lemma siv_ro_agree_of_inv : forall m, mem_inv rsegs m -> ro_agree rsegs m.
Proof.
  intros m MI x Hx. unfold mrd. destruct (m x) as [b|] eqn:E; [|reflexivity].
  rewrite (MI _ _ E) in Hx. discriminate.
Qed.

Lemma siv_run0 :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> (lo + 48 <= bv_unsigned sp)%Z -> (2 ^ 21 <= lo)%Z ->
  evt rsegs (fun ms' => exists m',
       ms' = MS (mkR (Z_to_bv 64 0x169c4) (Z_to_bv 64 (bv_unsigned sp - 48)) gp tp t0 t1 t2 s0 a0 (Z_to_bv 64 7)
                     a1 a2 a3 a4 a5 a6 a7 a1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x1612c) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' (bv_unsigned sp - 32)%Z [C8 s2; C8 s1; C8 s0; C8 ra])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x169a0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ST LO LO2.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 32%nat junk [] [8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  carve_frame 16%nat ST.
  clear FR0.
  do 9 step.
  apply evt_done.
  eexists. split; [reflexivity|].
  split; [eassumption|]. split; eassumption.
Qed.

Lemma siv_run1 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x169d0) sp gp tp t0 t1 t2 a0 s1 a0 s1
                                      a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 0x16608) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x169c4) fc None m (seg_rom rsegs)).
Proof. intros. do 3 step. apply evt_done. reflexivity. Qed.

Definition siv_mid2 (sp gp tp s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (lo v e : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' slack,
    ms' = MS (mkR (Z_to_bv 64 0x169f4) sp gp tp t0 t1 t2 (Z_to_bv 64 e) s1 (Z_to_bv 64 e) sp
                  a2 a3 a4 a5 a6 a7 (Z_to_bv 64 v) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (Z_to_bv 64 0x161c4) fc' None m' (seg_rom rsegs)
    /\ munch [(lo, bv_unsigned sp + 16)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get F' k = reg_get F k)
    /\ length slack = (15 - length (dec v))%nat
    /\ bytes_at rsegs m' (bv_unsigned sp) (dec v ++ Z_to_bv 8 0 :: slack).

Lemma siv_run2 : snprintf_contract ->
  forall ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo v e : Z) (canary : word),
  (-2^31 <= v < 2^31)%Z ->
  stk rsegs m lo (bv_unsigned sp + 16) -> (lo + SNPRINTF_K <= bv_unsigned sp)%Z -> (2 ^ 21 <= lo)%Z ->
  (bv_unsigned sp + 16 < 2^63)%Z ->
  frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m -> (bv_unsigned sp + 16 <= TASK_SIZE)%Z ->
  bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) -> bytes_at rsegs m GUARD (le8 canary) ->
  evt rsegs (siv_mid2 sp gp tp s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo v e m)
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 e) s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 v) s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x169d0) fc None m (seg_rom rsegs)).
Proof.
  intros SNP ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo v e canary HV ST LO IE S63 FRM MI TM HTS GG GW.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold SNPRINTF_K, IMG_END, GOT_GUARD, GUARD in *.
  pose proof (dec_length v HV) as DL.
  pose proof (siv_pf_dec v HV) as PD.
  assert (TL : length (pf_dec v) = length (dec v)) by (rewrite <- PD; unfold pf_bytes; rewrite length_map; reflexivity).
  carve_frame 16%nat ST.
  match type of ST with stk _ _ _ ?h => replace h with (bv_unsigned sp) in ST by lia end.
  match type of FR with rw_cells _ _ ?h _ => replace h with (bv_unsigned sp) in FR by lia end.
  do 6 step.
  pose proof (rw_cells_bound _ _ _ _ FR) as FRB. cbn [cells_size csize Nat.add] in FRB.
  assert (BJ : bytes_at rsegs m (bv_unsigned sp) junk).
  { destruct FR as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  pose proof (bytes_at_bound _ _ _ _ BJ) as BJL.
  assert (JL : length junk = 16%nat) by (destruct FR as [[[HJ _] _] _]; exact HJ).
  eapply evt_cut.
  { eapply (SNP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo canary SIV_FMT SIV_PS
              [AInt v] (pf_dec v) junk).
    - rewrite unsigned_lit by lia. apply siv_fmt_at. exact MI.
    - rewrite unsigned_lit by lia. unfold RO_LO. lia.
    - rewrite unsigned_lit by lia. unfold RO_END, SIV_FMT. cbn [length]. lia.
    - exact siv_parse.
    - cbn [pf_args_ok pf_arg_ok]. split; [|exact I]. split; [exact HV | apply lit_mod32].
    - exact (siv_text v).
    - rewrite !unsigned_lit by lia. exact FR.
    - rewrite unsigned_lit by lia. lia.
    - lia.
    - lia.
    - right. lia.
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
  replace (ret_pc (Z_to_bv 64 0x169e8)) with (Z_to_bv 64 0x169e8) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  destruct (bytes_at_firstn_skipn _ _ _ _ (S (length (pf_dec v))) BJ) as [_ BJT].
  rewrite firstn_length_le in BJT by lia.
  assert (BJT2 : bytes_at rsegs m2 (bv_unsigned sp + Z.of_nat (S (length (pf_dec v))))%Z
                   (skipn (S (length (pf_dec v))) junk)).
  { apply (bytes_at_transport rsegs _ m m2 _ _ BJT MU2). cbn [disjoint_from]. rewrite length_skipn.
    split; [lia | split; [lia | exact I]]. }
  assert (PB : pf_bytes (pf_dec v ++ [0%Z]) = dec v ++ [Z_to_bv 8 0]).
  { unfold pf_bytes. rewrite map_app. change (map (Z_to_bv 8) (pf_dec v)) with (pf_bytes (pf_dec v)).
    rewrite PD. reflexivity. }
  rewrite PB in BT.
  assert (BUF : bytes_at rsegs m2 (bv_unsigned sp) (dec v ++ Z_to_bv 8 0 :: skipn (S (length (pf_dec v))) junk)).
  { replace (dec v ++ Z_to_bv 8 0 :: skipn (S (length (pf_dec v))) junk) with
      ((dec v ++ [Z_to_bv 8 0]) ++ skipn (S (length (pf_dec v))) junk)
      by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app. split; [exact BT|]. rewrite length_app, <- TL. cbn [length].
    replace (Z.of_nat (length (pf_dec v) + 1)) with (Z.of_nat (S (length (pf_dec v)))) by lia. exact BJT2. }
  clear BT BJT BJT2 BJ BJL FR.
  do 3 step.
  apply evt_done. unfold siv_mid2.
  do 16 eexists. exists (skipn (S (length (pf_dec v))) junk). split; [reflexivity|].
  split.
  { eapply munch_weaken; [|exact MU2].
    unfold sub_fp. cbn [outside]. intros x [Hx _]. split; [lia | split; [lia | exact I]]. }
  split; [eapply wmono_trans; [apply wmono_refl | exact WM2]|].
  split; [exact MI2|]. split; [exact FRM2|]. split; [exact FK|].
  split; [rewrite length_skipn, JL, TL; lia|].
  exact BUF.
Qed.

Local Open Scope Z_scope.

Definition siv_set : list byte := [Z_to_bv 8 32; Z_to_bv 8 9].

Lemma siv_set_no0 : no0 siv_set.
Proof. apply no0_nz. vm_compute. reflexivity. Qed.

Lemma siv_set_at : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x1064c (siv_set ++ [Z_to_bv 8 0]).
Proof.
  intros m MI. apply siv_rom_chk_bytes; [exact (siv_ro_agree_of_inv m MI) | lia | cbn; lia | vm_compute; reflexivity].
Qed.

Lemma siv_gl : length g_shapes_bytes = 448%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma siv_in_set : forall x, in_set siv_set x = is_sep x.
Proof.
  intros x. unfold in_set, siv_set, is_sep. cbn [existsb]. rewrite orb_false_r.
  change (bv_unsigned (Z_to_bv 8 32)) with 32. change (bv_unsigned (Z_to_bv 8 9)) with 9.
  rewrite (Z.eqb_sym 32), (Z.eqb_sym 9). reflexivity.
Qed.

Lemma siv_cspn_cons : forall x s, cspn_len siv_set (x :: s) = if is_sep x then O else S (cspn_len siv_set s).
Proof. intros x s. cbn [cspn_len]. rewrite <- siv_in_set. reflexivity. Qed.

Lemma siv_spn_le : forall s, (spn_len siv_set s <= length s)%nat.
Proof. intros s. induction s as [|x s IH]; cbn [spn_len length]; [lia|]. destruct (in_set siv_set x); lia. Qed.

Lemma siv_cspn_le : forall s, (cspn_len siv_set s <= length s)%nat.
Proof.
  intros s. induction s as [|x s IH]; [cbn [cspn_len length]; lia|].
  rewrite siv_cspn_cons. destruct (is_sep x); cbn [length]; lia.
Qed.

Lemma siv_words_skip : forall T, words_go [] T = words_go [] (skipn (spn_len siv_set T) T).
Proof.
  induction T as [|x T IH]; [reflexivity|].
  cbn [spn_len]. rewrite siv_in_set. destruct (is_sep x) eqn:E.
  - cbn [skipn]. rewrite <- IH. cbn [words_go]. rewrite E. reflexivity.
  - reflexivity.
Qed.

Lemma siv_words_head : forall T cur, cur <> [] ->
  exists rest, words_go cur T = (rev cur ++ firstn (cspn_len siv_set T) T) :: rest.
Proof.
  induction T as [|x T IH]; intros cur Hc.
  - destruct cur as [|y cur]; [exfalso; apply Hc; reflexivity|]. exists []. cbn [words_go cspn_len firstn].
    rewrite app_nil_r. reflexivity.
  - rewrite siv_cspn_cons. cbn [words_go]. destruct (is_sep x).
    + destruct cur as [|y cur]; [exfalso; apply Hc; reflexivity|]. exists (words_go [] T). cbn [firstn].
      rewrite app_nil_r. reflexivity.
    + destruct (IH (x :: cur) ltac:(discriminate)) as (rest & E). exists rest. rewrite E. cbn [rev firstn].
      rewrite <- app_assoc. reflexivity.
Qed.

Lemma siv_first_word : forall T,
  firstn (cspn_len siv_set (skipn (spn_len siv_set T) T)) (skipn (spn_len siv_set T) T) = first_word T.
Proof.
  intros T. unfold first_word, words. rewrite (siv_words_skip T).
  assert (H : skipn (spn_len siv_set T) T = [] \/
              exists x T', skipn (spn_len siv_set T) T = x :: T' /\ is_sep x = false).
  { clear. induction T as [|x T IH]; [left; reflexivity|].
    cbn [spn_len]. rewrite siv_in_set. destruct (is_sep x) eqn:E.
    - exact IH.
    - right. exists x, T. split; [reflexivity | exact E]. }
  destruct H as [H | (x & T' & H & E)]; rewrite H; [reflexivity|].
  rewrite siv_cspn_cons, E. cbn [words_go]. rewrite E.
  destruct (siv_words_head T' [x] ltac:(discriminate)) as (rest & H2). rewrite H2. reflexivity.
Qed.

Ltac siv_lits :=
  repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by lia end.

Ltac siv_tr H MU :=
  apply (bytes_at_transport rsegs _ _ _ _ _ H MU); cbn [disjoint_from];
  rewrite ?length_app, ?length_skipn, ?Mem.length_le8, ?siv_gl; cbn [length];
  unfold G_SHAPES, SSP_GOT, SSP_GUARD in *; repeat split; lia.

Ltac siv_br b :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with b;
      [ cbv iota
      | symmetry; unfold bv_eqb, bv_ltu, bv_leu; siv_lits; cbn [negb];
        repeat match goal with
               | |- context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y)
               | |- context [Z.eqb ?x ?y] => destruct (Z.eqb_spec x y)
               end;
        cbn [negb]; first [reflexivity | exfalso; lia] ]
  end.

Lemma siv_after : strspn_contract -> strcspn_contract -> rec_shape_of_contract ->
  forall ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo p : Z) (line : list byte) (can : word),
  stk rsegs m lo (bv_unsigned sp) -> lo + 96 <= bv_unsigned sp -> 2 ^ 21 <= lo ->
  bytes_at rsegs m G_SHAPES g_shapes_bytes -> mem_inv rsegs m ->
  bytes_at rsegs m SSP_GOT (le8 (Z_to_bv 64 SSP_GUARD)) -> bytes_at rsegs m SSP_GUARD (le8 can) ->
  bytes_at rsegs m p (line ++ [Z_to_bv 8 0]) -> no0 line -> p <> 0 ->
  p + Z.of_nat (length line) + 1 <= lo \/ bv_unsigned sp <= p ->
  evt rsegs (fun ms' => exists m' (t0' t1' t2' a3' a4' a5' a6' a7' s2' t3' t4' t5' t6' : word),
       ms' = MS (mkR (Z_to_bv 64 0x16a48) sp gp tp t0' t1' t2' s0 (Z_to_bv 64 p) s0
                     (Z_to_bv 64 (shape_find shape_rows (first_word line))) (Z_to_bv 64 1)
                     a3' a4' a5' a6' a7' s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x16310) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m' /\ wmono rsegs m m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 p) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x169f4) fc None m (seg_rom rsegs)).
Proof.
  intros SSPN SCSPN RSO ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo p line can ST LO LO2 GS MI GOT GRD LB N0 P0 DJ.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof LB as (LB0 & LB1 & _). rewrite length_app in LB1. cbn [length] in LB1.
  do 4 step.
  eapply evt_cut.
  { eapply (SSPN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ line siv_set lo can).
    - siv_lits. exact LB.
    - exact N0.
    - siv_lits. exact (siv_set_at m MI).
    - exact siv_set_no0.
    - exact GOT.
    - exact GRD.
    - exact ST.
    - lia.
    - siv_lits. lia.
    - left. siv_lits. unfold siv_set. cbn [length]. lia.
    - left. unfold SSP_GOT. lia.
    - left. unfold SSP_GUARD. lia.
    - exact MI. }
  intros ms1 PO. unfold strspn_post in PO.
  destruct PO as (t0a & t1a & t2a & a1a & a2a & a3a & a4a & a5a & a6a & a7a & t3a & t4a & t5a & t6a & m1 & -> & MU1
    & WM1 & MI1 & ST1).
  rewrite (ret_pc_even 0x16a04) by lia.
  set (k := spn_len siv_set line) in *.
  pose proof (siv_spn_le line) as Hk. fold k in Hk.
  pose proof (length_skipn k line) as LSK.
  assert (LB2 : bytes_at rsegs m1 p (line ++ [Z_to_bv 8 0])) by siv_tr LB MU1.
  assert (GS1 : bytes_at rsegs m1 G_SHAPES g_shapes_bytes) by siv_tr GS MU1.
  assert (GOT1 : bytes_at rsegs m1 SSP_GOT (le8 (Z_to_bv 64 SSP_GUARD))) by siv_tr GOT MU1.
  assert (GRD1 : bytes_at rsegs m1 SSP_GUARD (le8 can)) by siv_tr GRD MU1.
  assert (SUF : bytes_at rsegs m1 (p + Z.of_nat k) (skipn k line ++ [Z_to_bv 8 0])).
  { pose proof LB2 as FU. rewrite <- (firstn_skipn k line), <- app_assoc in FU.
    apply bytes_at_app in FU. destruct FU as [_ FU]. rewrite firstn_length_le in FU by lia. exact FU. }
  assert (NZ2 : ~ In (Z_to_bv 8 0) (skipn k line)).
  { intros HIn. apply N0. rewrite <- (firstn_skipn k line). apply in_or_app. right. exact HIn. }
  step.
  replace (Z.of_nat k + p) with (p + Z.of_nat k) by lia.
  step.
  siv_br false.
  do 3 step.
  step.
  assert (V1 : v_sltu (Z_to_bv 64 0) (Z_to_bv 64 p) = Z_to_bv 64 1).
  { unfold v_sltu, c_ltu, bv_ltu. rewrite !unsigned_lit by lia. destruct (Z.ltb_spec 0 p); [reflexivity | lia]. }
  assert (V2 : v_sltiu (Z_to_bv 64 (p + Z.of_nat k)) 1 = Z_to_bv 64 0).
  { unfold v_sltiu. rewrite unsigned_lit by lia. change (bv_wrap 64 1) with 1.
    destruct (Z.ltb_spec (p + Z.of_nat k) 1); [lia | reflexivity]. }
  rewrite V1, V2.
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with false by (vm_compute; reflexivity); cbv iota
  end.
  do 4 step.
  eapply evt_cut.
  { eapply (SCSPN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (skipn k line) [] siv_set lo can).
    - siv_lits. exact SUF.
    - exact NZ2.
    - intros HL. unfold siv_set in HL. cbn [length] in HL. lia.
    - siv_lits. exact (siv_set_at m1 MI1).
    - exact siv_set_no0.
    - exact GOT1.
    - exact GRD1.
    - exact ST1.
    - lia.
    - siv_lits. cbn [length]. rewrite LSK. lia.
    - left. siv_lits. unfold siv_set. cbn [length]. lia.
    - left. unfold CSPN_SSP_GOT. lia.
    - left. unfold CSPN_SSP_GUARD. lia.
    - exact MI1. }
  intros ms2 PO. unfold strcspn_post in PO.
  destruct PO as (t0b & t1b & t2b & a1b & a2b & a3b & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & m2 & -> & MU2
    & WM2 & MI2 & ST2).
  rewrite (ret_pc_even 0x16a2c) by lia.
  set (c := cspn_len siv_set (skipn k line)) in *.
  pose proof (siv_cspn_le (skipn k line)) as Hc. fold c in Hc. rewrite LSK in Hc.
  assert (SUF2 : bytes_at rsegs m2 (p + Z.of_nat k) (skipn k line ++ [Z_to_bv 8 0])) by siv_tr SUF MU2.
  assert (GS2 : bytes_at rsegs m2 G_SHAPES g_shapes_bytes) by siv_tr GS1 MU2.
  do 3 step.
  eapply evt_cut.
  { eapply RSO with (lo := lo) (v := firstn c (skipn k line)).
    - exact MI2.
    - exact ST2.
    - unfold REC_SHAPE_OF_FRAME. lia.
    - exact GS2.
    - left. unfold REC_SHAPE_OF_FRAME, G_SHAPES. lia.
    - siv_lits. rewrite firstn_length_le by lia. reflexivity.
    - intros _. siv_lits. split.
      + pose proof SUF2 as FU. rewrite <- (firstn_skipn c (skipn k line)), <- app_assoc in FU.
        apply bytes_at_app in FU. exact (proj1 FU).
      + unfold REC_SHAPE_OF_FRAME. lia. }
  intros ms3 (t0c & t1c & t2c & a1c & a2c & a3c & a4c & a5c & a6c & a7c & t3c & t4c & t5c & t6c & m3 & -> & MU3 & WM3
    & MI3 & ST3).
  unfold REC_SHAPE_OF_FRAME in MU3.
  rewrite (ret_pc_even 0x16a38) by lia.
  assert (FW : firstn c (skipn k line) = first_word line) by (unfold c, k; apply siv_first_word).
  rewrite FW.
  do 4 step.
  apply evt_done.
  do 14 eexists. split; [reflexivity|].
  split.
  { apply (munch_trans _ m m1 m3); [|apply (munch_trans _ m1 m2 m3)].
    - refine (munch_weaken _ _ _ _ _ MU1). intros x (H1 & _). split; [lia | exact I].
    - refine (munch_weaken _ _ _ _ _ MU2). intros x (H1 & _). split; [lia | exact I].
    - refine (munch_weaken _ _ _ _ _ MU3). intros x (H1 & _). split; [lia | exact I]. }
  exact (wmono_trans rsegs _ _ _ WM1 (wmono_trans rsegs _ _ _ WM2 WM3)).
Qed.

Lemma siv_run4 :
  forall ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp0 ra0 s00 s01 s02 : word),
  rw_cells rsegs m (bv_unsigned sp0 + -32) [C8 s02; C8 s01; C8 s00; C8 ra0] -> 48 <= bv_unsigned sp0 ->
  evt rsegs (fun ms' => ms' = MS (mkR ra0 sp0 gp tp t0 t1 t2 s00 s01 a0 a1 a2 a3 a4 a5 a6 a7
                                      s02 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (ret_pc ra0) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 + -48)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16a48) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 ra0 s00 s01 s02 FR SPR.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  do 6 step.
  replace (Z_to_bv 64 (bv_unsigned sp0 + -48 + 48)) with sp0
    by (replace (bv_unsigned sp0 + -48 + 48) with (bv_unsigned sp0) by ring; symmetry; apply Z_to_bv_bv_unsigned).
  apply evt_done. reflexivity.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInv RecInvU RecKindB RecSeq RecStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecGlue RecTail RecAnsB RecStubU.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import xmalloc_c record_c arg_s_c answer_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import rec_canonical_c arg_line_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import sup_instance_verb_c.
Local Open Scope Z_scope.

Definition siv_kept (R R' : bvmap 5 word) : Prop :=
  forall r, callee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> r <> 18 -> getr R' (Z_to_bv 5 r) = getr R (Z_to_bv 5 r).

Lemma siv_kept_trans : forall R1 R2 R3, siv_kept R1 R2 -> siv_kept R2 R3 -> siv_kept R1 R3.
Proof.
  intros R1 R2 R3 H1 H2 r Hr N2 N8 N9 N18. rewrite (H2 r Hr N2 N8 N9 N18). exact (H1 r Hr N2 N8 N9 N18).
Qed.

Lemma siv_kept_of_pres : forall R R', regs_preserved R R' -> siv_kept R R'.
Proof. intros R R' H r Hr _ _ _ _. exact (H r Hr). Qed.

Ltac siv_kept_tac X :=
  intros rr Hrr Nrr2 Nrr8 Nrr9 Nrr18; unfold callee_saved in Hrr;
  assert (CC : rr = 3 \/ rr = 4 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/ rr = 22 \/ rr = 23 \/ rr = 24 \/
               rr = 25 \/ rr = 26 \/ rr = 27) by lia;
  clear Hrr Nrr2 Nrr8 Nrr9 Nrr18;
  repeat (destruct CC as [CC|CC]; [subst rr; match goal with |- getr _ ?k = _ => rewrite (getr_of_eqv _ _ k X eq_refl) end;
    simp_regs; first [reflexivity | unfold getr; reflexivity]|]);
  subst rr; match goal with |- getr _ ?k = _ => rewrite (getr_of_eqv _ _ k X eq_refl) end;
  simp_regs; first [reflexivity | unfold getr; reflexivity].

Lemma siv_pres : forall (regs R : bvmap 5 word), siv_kept regs R ->
  getr R (Z_to_bv 5 2) = getr regs (Z_to_bv 5 2) -> getr R (Z_to_bv 5 8) = getr regs (Z_to_bv 5 8) ->
  getr R (Z_to_bv 5 9) = getr regs (Z_to_bv 5 9) -> getr R (Z_to_bv 5 18) = getr regs (Z_to_bv 5 18) ->
  regs_preserved regs R.
Proof.
  intros regs R KR E2 E8 E9 E18 r Hr.
  destruct (Z.eq_dec r 2) as [->|N2]; [exact E2|].
  destruct (Z.eq_dec r 8) as [->|N8]; [exact E8|].
  destruct (Z.eq_dec r 9) as [->|N9]; [exact E9|].
  destruct (Z.eq_dec r 18) as [->|N18]; [exact E18|].
  exact (KR r Hr N2 N8 N9 N18).
Qed.

Lemma siv_mod8 : forall s0 k, s0 mod 16 = 0 -> 1 <= k <= 11 -> (- (s0 - 48 + k + 1)) mod 8 <= 15 - k.
Proof. intros s0 k H1 H2. Z.div_mod_to_equations. lia. Qed.

Lemma siv_le_a : forall b b1 n1 n2 nt, sb_le b1 b -> 0 <= n2 -> 0 <= nt ->
  sb_le (sb_malloc b1 n1) (sb_malloc (sb_malloc (sb_malloc (sb_malloc b n1) n2) nt) nt).
Proof. intros b b1 n1 n2 nt H H2 H3. unfold sb_le, sb_malloc in *. cbn in *. lia. Qed.

Lemma siv_le_b : forall b b1 n1 n2 nt, sb_le b1 b -> 0 <= nt ->
  sb_le (sb_malloc (sb_malloc b1 n1) n2) (sb_malloc (sb_malloc (sb_malloc (sb_malloc b n1) n2) nt) nt).
Proof. intros b b1 n1 n2 nt H H3. unfold sb_le, sb_malloc in *. cbn in *. lia. Qed.

Lemma siv_le_c : forall b b1 n1 n2 nt, sb_le b1 (sb_malloc (sb_malloc b n1) n2) ->
  sb_le (sb_malloc (sb_malloc b1 nt) nt) (sb_malloc (sb_malloc (sb_malloc (sb_malloc b n1) n2) nt) nt).
Proof. intros b b1 n1 n2 nt H. unfold sb_le, sb_malloc in *. cbn in *. lia. Qed.

Lemma siv_host_shape : forall m, ro_agree rsegs m -> ans_shape rsegs m 0x10417 REC_MOD_HOST_SHAPE.
Proof.
  intros m RA.
  assert (RO : forall i, 0 <= i <= 6 -> ro_addr rsegs (Z_to_bv 64 (0x10417 + i)) = true).
  { intros i Hi. assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6) by lia.
    repeat (destruct C as [C|C]; [subst i; vm_compute; reflexivity|]). subst i. vm_compute. reflexivity. }
  split.
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi.
    unfold wa. rewrite (RA _ (RO (Z.of_nat i) ltac:(lia))).
    assert (C : i = 0%nat \/ i = 1%nat \/ i = 2%nat \/ i = 3%nat \/ i = 4%nat \/ i = 5%nat \/ i = 6%nat) by lia.
    repeat (destruct C as [C|C]; [subst i; vm_compute; reflexivity|]). subst i. vm_compute. reflexivity.
  - split; [apply no0_nz; vm_compute; reflexivity|]. split; [cbn; unfold LMAX; lia|].
    split; [apply fits_shape_set; left; reflexivity|]. intros i Hi. apply RO. cbn in Hi. lia.
Qed.

Lemma siv_ans_shape_chk : forall m a x, ro_agree rsegs m -> 0 <= a -> a + Z.of_nat (length x) + 1 <= 2 ^ 64 ->
  siv_rom_chk a (x ++ [Z_to_bv 8 0]) = true -> no0 x -> Z.of_nat (length x) <= LMAX -> fits x ->
  ans_shape rsegs m a x.
Proof.
  intros m a x RA H0 H1 C N0 LX FT. pose proof (length_app x [Z_to_bv 8 0]) as LA. cbn [length] in LA.
  split; [apply siv_rom_chk_bytes; [exact RA | lia | rewrite LA; lia | exact C]|].
  split; [exact N0|]. split; [exact LX|]. split; [exact FT|].
  intros i Hi. replace i with (Z.of_nat (Z.to_nat i)) by lia.
  exact (proj1 (siv_rom_chk_at a _ (Z.to_nat i) C ltac:(rewrite LA; lia))).
Qed.

Fixpoint siv_rows_ok (rows : list (Z * String.string * Z)) (tab : list (list byte * list byte)) : bool :=
  match rows, tab with
  | [], [] => true
  | (_, nm, rp) :: rows', (x, y) :: tab' =>
      bl_eqb x (str_bytes nm) && (0 <=? rp) && (rp + Z.of_nat (length y) + 1 <=? 2 ^ 64) &&
      siv_rom_chk rp (y ++ [Z_to_bv 8 0]) && siv_rows_ok rows' tab'
  | _, _ => false
  end.

Lemma siv_rows_true : siv_rows_ok shape_rows shape_table = true.
Proof. vm_compute. reflexivity. Qed.

Lemma siv_rows_find : forall v rows tab, siv_rows_ok rows tab = true ->
  (shape_find rows v = SHAPE_LIT /\ shape_lookup tab v = REC_MOD_HOST_SHAPE) \/
  (0 <= shape_find rows v /\ shape_find rows v + Z.of_nat (length (shape_lookup tab v)) + 1 <= 2 ^ 64 /\
   siv_rom_chk (shape_find rows v) (shape_lookup tab v ++ [Z_to_bv 8 0]) = true).
Proof.
  intros v rows. induction rows as [|[[na nm] rp] rows IH]; intros tab H;
    destruct tab as [|[x y] tab]; cbn [siv_rows_ok] in H; try discriminate H.
  - left. split; reflexivity.
  - apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3].
    apply andb_prop in H as [H H2]. apply andb_prop in H as [H0 H1].
    apply Z.leb_le in H1. apply Z.leb_le in H2.
    cbn [shape_find shape_lookup].
    assert (E : map bv_unsigned x = map bv_unsigned (str_bytes nm)).
    { revert H0. unfold bl_eqb.
      destruct (list_eq_dec Z.eq_dec (map bv_unsigned x) (map bv_unsigned (str_bytes nm))) as [E|E];
        intros H0; [exact E | discriminate H0]. }
    assert (EQ : bl_eqb x v = bytes_eqb (str_bytes nm) v).
    { unfold bl_eqb, bytes_eqb.
      destruct (list_eq_dec Z.eq_dec (map bv_unsigned x) (map bv_unsigned v)) as [E1|E1];
        destruct (list_eq_dec Z.eq_dec (map bv_unsigned (str_bytes nm)) (map bv_unsigned v)) as [E2|E2];
        try reflexivity; exfalso; congruence. }
    rewrite EQ. destruct (bytes_eqb (str_bytes nm) v).
    + right. split; [lia|]. split; [lia | exact H3].
    + exact (IH tab H4).
Qed.

Lemma siv_ans_shape : forall m v, ro_agree rsegs m -> ans_shape rsegs m (shape_find shape_rows v) (shape_of v).
Proof.
  intros m v RA. destruct (shape_of_facts v) as (FT & _ & L78 & N0). unfold shape_of in *.
  destruct (siv_rows_find v shape_rows shape_table siv_rows_true) as [(E1 & E2) | (H0 & H1 & H2)].
  - rewrite E1, E2. exact (siv_host_shape m RA).
  - apply siv_ans_shape_chk; [exact RA | lia | lia | exact H2 | exact N0 | unfold LMAX; lia | exact FT].
Qed.

Lemma siv_code_record : forall R fn As, r_code (rec_record R fn As) = r_code R.
Proof. intros R fn As. unfold rec_record. destruct (Nat.ltb (length (r_calls R)) 16); reflexivity. Qed.

Lemma siv_stub_len : forall R fn As x chg, -2^31 <= r_code R < 2^31 ->
  (length (snd (rec_answer (rec_record R fn As) (fn, As) x chg)) <= Nat.max (length x) 16)%nat.
Proof.
  intros R fn As x chg H. rewrite rec_answer_text. destruct (r_refuse (rec_record R fn As) =? 0).
  - pose proof (inst_length x). lia.
  - rewrite siv_code_record. pose proof (resp_length (r_code R) H). lia.
Qed.

Lemma siv_nra_apart : forall s Ln lo hi, (forall a, s <= a < s + Ln -> ~ rec_area a) ->
  REC_SC <= lo -> hi <= G_REC + REC_SIZE -> lo < hi -> 0 < Ln -> s + Ln <= lo \/ hi <= s.
Proof.
  intros s Ln lo hi H H1 H2 H3 H4. destruct (Z_le_gt_dec (s + Ln) lo) as [D|D]; [left; exact D|].
  destruct (Z_le_gt_dec hi s) as [D'|D']; [right; exact D'|]. exfalso.
  unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE in *.
  destruct (Z_le_gt_dec s lo) as [D1|D1].
  - apply (H lo); [lia|]. destruct (Z_lt_ge_dec lo 213032); [left | right]; lia.
  - apply (H s); [lia|]. destruct (Z_lt_ge_dec s 213032); [left | right]; lia.
Qed.

Section SivAns.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis ANS : answer_contract B API.
Hypothesis SLACK : block_slack_present B API.

Definition siv_ans_mid (K S : Z) (L : layout) (A : astate) (mem : word -> option byte) (md : Model) (O : list (Z * Z))
    (regs1 : bvmap 5 word) (mem1 : word -> option byte) (R1 : rstate) (e : rcall) (x : list byte) (chg : bool)
    (b bpre : sbound) (c' : config) : Prop :=
  let t := snd (rec_answer R1 e x chg) in
  let n := Z.of_nat (length t) + 1 in
  exists (fx' : YK11.FPState) L' A' regs' mem' md' O' q,
    c' = mkCfg (@mkst fx' regs' (getr regs1 1) mem' (seg_rom rsegs)) md' /\
    fp_kept fx fx' /\
    rjr B (aa_MR API) K S rec_area (fun pn => In pn O) L A mem md L' A' mem' md' /\
    regs_preserved regs1 regs' /\
    (forall a, spZ regs1 <= a < S ->
       mbyte rsegs mem' a = mbyte rsegs mem1 a /\ (writable_at rsegs mem1 a <-> writable_at rsegs mem' a)) /\
    getr regs' 10 = Z_to_bv 64 q /\
    g_rec_rep rsegs L' A' mem' (fst (rec_answer R1 e x chg)) O' /\ owns_new L A O O' /\
    (forall pn, In pn (blocks L' A') -> (In pn (blocks L A) /\ ~ In pn O) \/ In pn O' \/ pn = (q, n)) /\
    In (q, n) (blocks L' A') /\ fresh_block B q n /\ ~ In q (map fst O') /\
    Mem.bytes_at rsegs mem' q (t ++ [Z_to_bv 8 0]) /\
    others_kept rsegs L A mem L' A' mem' O /\
    (forall p k, In (p, k) (user_blocks A) -> ~ In (ptr_addr L p, k) O ->
       ptr_addr L p + k <= q \/ q + n <= ptr_addr L p) /\
    ro_agree rsegs mem' /\ f18_words rsegs mem' /\ st_init_done A' = true /\
    (length (st_regions A) <= length (st_regions A'))%nat /\
    sb_le (sb_shift b A A') (sb_malloc (sb_malloc bpre n) n) /\ res_ok_slots A' (sb_shift b A A').

Lemma siv_answer_call : forall K S L A mem md (O : list (Z * Z)) L1 A1 regs1 mem1 md1 (R1 : rstate)
    (O1 : list (Z * Z)) bc bpre c sh e x chg,
  sinv B API K S L A mem md O L1 A1 mem1 md1 R1 O1 bc ->
  YK0s.ret_ok (getr regs1 1) -> spZ regs1 mod 16 = 0 -> S - K <= spZ regs1 - ANSWER_K -> spZ regs1 <= S ->
  spZ regs1 <= TASK_SIZE -> getr regs1 4 = Z_to_bv 64 (ms_tp B) ->
  getr regs1 10 = Z_to_bv 64 c -> getr regs1 11 = Z_to_bv 64 sh -> chg = negb (bv_unsigned (getr regs1 12) =? 0) ->
  (r_refuse R1 = 0 -> ans_shape rsegs mem1 sh x) ->
  (r_refuse R1 = 0 -> chg = true -> ans_entry R1 c e) ->
  frm_zero fp_csr ->
  sb_le (sb_shift bc A A1) bpre ->
  room_slots (sb_malloc (sb_malloc (sb_shift bc A A1) (Z.of_nat (length (snd (rec_answer R1 e x chg))) + 1))
                (Z.of_nat (length (snd (rec_answer R1 e x chg))) + 1))
             (Z.of_nat (length (snd (rec_answer R1 e x chg))) + 1) ->
  SR rsegs (mkCfg (mkst regs1 (Z_to_bv 64 ANSWER) mem1 (seg_rom rsegs)) md1)
    (siv_ans_mid K S L A mem md O regs1 mem1 R1 e x chg bc bpre).
Proof using SEGS AX ERRNO_LOW ANS SLACK.
  intros K S L A mem md O L1 A1 regs1 mem1 md1 R1 O1 bc bpre c sh e x chg
    SI RET AL LO HI HTS HTP A10 A11 ACH SHAPE ENTRY FRM BLE ROOM1.
  pose proof (aa_laws API) as LAWS.
  pose proof alloc_ceiling_val as AC.
  pose proof ERRNO_LOW as EL.
  pose proof SI as (R & GREP1 & P1 & P2 & P5 & RO1 & F18 & RES1).
  pose proof R as R0.
  destruct R0 as (HM1 & HWA & HW1 & HBd & HL & HLen & HV & HK1 & HK2 & HK3 & HF & HRM & HKP & HSC & HAX).
  assert (KA : 0 <= ANSWER_K) by (apply Z.leb_le; vm_compute; reflexivity).
  assert (PRE1 : call_pre_t B API ANSWER_K L1 A1 regs1 mem1 md1).
  { split; [|exact HTS].
    exact (call_pre_k_of_rjr B (aa_MR API) K S rec_area (fun pn => In pn O) L A mem md L1 A1 mem1 md1 ANSWER_K regs1
             R RET AL KA LO HI HTP). }
  pose proof ANS as ANS0. unfold answer_contract in ANS0. rewrite SEGS in ANS0.
  eapply SR_mono.
  { apply (ANS0 L1 A1 regs1 mem1 md1 R1 O1 c sh e x chg (sb_shift bc A A1) PRE1 A10 A11 ACH GREP1 SHAPE);
      [|exact FRM | exact F18 | exact RES1 | exact ROOM1 | exact RO1].
    intros Hr Hc. split; [exact (ENTRY Hr Hc)|]. intros q k a Hq Ha. exact (SLACK L1 A1 mem1 md1 q k a HM1 Hq Ha). }
  intros c' RETA. unfold answer_ret in RETA.
  destruct RETA as (fx' & L' & A' & regs' & mem' & md' & p1 & p2 & old & O' & EC & FPK & OLDB & POST & A0 & NE12 & AL1
    & AL2 & FR1 & FR2 & (c1 & c2 & HB & HIFF & NI1 & NI2) & BK & UBK & GREP' & HO' & HO2 & HBC & BY1 & BY2 & RA' & F18'
    & GK & INIT & REG & GR' & RES').
  pose proof POST as (PM & PW & PB & PL & PA & PR & PV & PF & PK & PS).
  rewrite SEGS in EC, GREP', BY2, RA', F18'.
  set (n := Z.of_nat (length (snd (rec_answer R1 e x chg))) + 1) in *.
  assert (HB' : exists kold, (old = 0 /\ blocks L1 A1 = c1 ++ c2) \/
                             (old <> 0 /\ In (old, kold) O1 /\ blocks L1 A1 = c1 ++ (old, kold) :: c2)).
  { destruct HB as [H|(k & H)]; [exists 0; left; exact H | exists k; right; exact H]. }
  destruct HB' as [kold HB'].
  assert (STAB : forall p k, In (p, k) (user_blocks A) -> ~ In (ptr_addr L p, k) O ->
            In (p, k) (user_blocks A1) /\ ptr_addr L1 p = ptr_addr L p).
  { intros p k Hu Hno.
    split; [exact (rjr_in_cur B (aa_MR API) K S rec_area (fun pn => In pn O) L A mem md L1 A1 mem1 md1 p k R Hu Hno)|].
    exact (ptr_addr_stable A L L1 p k HWA Hu HL). }
  assert (R2 : rjr B (aa_MR API) K S rec_area (fun pn => In pn O) L A mem md L' A' mem' md').
  { apply (rjr_post B (aa_MR API) SEGS LAWS AX ERRNO_LOW K S rec_area (fun pn => In pn O) L A mem md L1 A1 mem1 md1
             ANSWER_K regs1 ans_writes (fun a => a = old) L' A' regs' mem' md' R POST).
    - exact LO.
    - exact HI.
    - intros a Ha _.
      unfold ans_writes, rec_area, G_REC, REC_SC, OFF_ANSWER, OFF_STATE, SC_SIZE, REC_SIZE in *.
      split; [lia|]. lia.
    - intros p k Hu Hno Hk E.
      destruct (STAB p k Hu Hno) as [Hu1 Ep].
      pose proof (mr_blocks_range B (aa_MR API) LAWS L1 A1 mem1 md1 p k HM1 Hu1) as Hr. rewrite Ep in Hr.
      destruct HB' as [(E0 & _)|(NZ & Ho & EB)]; [lia|].
      assert (Hob : In (old, kold) (blocks L1 A1)) by (rewrite EB; apply in_or_app; right; left; reflexivity).
      pose proof (user_in_blocks L1 A1 p k Hu1) as Hb. rewrite Ep, E in Hb.
      pose proof (rec_rep_pos rsegs G_REC REC_SC L1 A1 mem1 R1 O1 (old, kold) GREP1 Ho) as Hk0. cbn [snd] in Hk0.
      assert (Ek : k = kold) by exact (blocks_same_addr B (aa_MR API) LAWS L1 A1 mem1 md1 old k kold HM1 Hb Hob Hk Hk0).
      subst k. rewrite E in Hno.
      destruct (P1 _ Ho) as [H|H]; [exact (Hno H)|]. apply H. rewrite <- E. exact (user_in_blocks L A p kold Hu).
    - intros p k Hu Hu1 Hu'.
      destruct (in_dec pair_dec (ptr_addr L p, k) O) as [H|H]; [exact H|]. exfalso. apply Hu'. apply UBK; [exact Hu1|].
      rewrite (ptr_addr_stable A L L1 p k HWA Hu HL). intros Ho.
      destruct (P1 _ Ho) as [H'|H']; [exact (H H') | exact (H' (user_in_blocks L A p k Hu))].
    - exact REG.
    - rewrite INIT. discriminate. }
  assert (KST : forall a, spZ regs1 <= a < S ->
            mbyte rsegs mem' a = mbyte rsegs mem1 a /\ (writable_at rsegs mem1 a <-> writable_at rsegs mem' a)).
  { intros a Ha. rewrite <- SEGS. apply PF.
    - left. lia.
    - intros Ho. pose proof (mr_owned_low B _ LAWS L1 A1 mem1 md1 a HM1 Ho). lia.
    - intros Ho. pose proof (mr_owned_low B _ LAWS L' A' mem' md' a PM Ho). lia.
    - unfold scratch_k. intros [H|H]; lia.
    - unfold ans_writes, G_REC, OFF_ANSWER, OFF_STATE. lia. }
  pose proof (rjr_others_kept B (aa_MR API) K S rec_area (fun pn => In pn O) L A mem md L' A' mem' md' O R2
                (fun pn H => H)) as OK.
  rewrite SEGS in OK.
  destruct (tail_owns_blocks (blocks L A) (blocks L1 A1) (blocks L' A') O O1 O' c1 c2 old kold p1 p2 n
              P1 P2 P5 HB' NI1 HO' HBC) as [OWN BLK].
  assert (Hq : In (p2, n) (blocks L' A')) by (apply HIFF; right; right; reflexivity).
  unfold siv_ans_mid. exists fx', L', A', regs', mem', md', O', p2.
  split; [exact EC|].
  split; [exact FPK|]. split; [exact R2|]. split; [exact PR|]. split; [exact KST|]. split; [exact A0|].
  split; [exact GREP'|]. split; [exact OWN|]. split; [exact BLK|]. split; [exact Hq|]. split; [exact FR2|].
  split; [intros Hin; apply in_map_iff in Hin as (pn & Epn & Hpn); exact (HO2 pn Hpn Epn)|].
  split; [exact BY2|]. split; [exact OK|].
  split.
  { intros p0 k0 Hu0 Hno0.
    revert p0 k0 Hu0 Hno0.
    apply (q_apart_tail B (aa_MR API) LAWS rsegs L A mem L' A' mem' md' O p2 n PM OK Hq).
    intros p k Hu Hno. destruct (STAB p k Hu Hno) as [Hu1 Ep].
    apply (tail_q_distinct (blocks L A) (blocks L1 A1) O O1 c1 c2 old kold p2 n (ptr_addr L p, k) P1 HB' NI2).
    - exact (user_in_blocks L A p k Hu).
    - exact Hno.
    - rewrite <- Ep. exact (user_in_blocks L1 A1 p k Hu1). }
  split; [exact RA'|]. split; [exact F18'|]. split; [exact INIT|]. split; [lia|].
  rewrite <- (sb_shift_trans bc A A1 A').
  split; [eapply sb_le_trans; [exact GR' | apply sb_malloc_mono; apply sb_malloc_mono; exact BLE] | exact RES'].
Qed.

End SivAns.

Section SivShapes.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis RIMG : forall a, in_globals frame_RELRO a ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4).

Lemma siv_rjr_shapes : forall K S O L A mem md Lc Ac mc mdc,
  rjr B (aa_MR API) K S rec_area (fun pn => In pn O) L A mem md Lc Ac mc mdc ->
  bytes_at rsegs mem G_SHAPES g_shapes_bytes ->
  bytes_at rsegs mc G_SHAPES g_shapes_bytes.
Proof using SEGS RIMG.
  intros K S O L A mem md Lc Ac mc mdc RJ BS. pose proof alloc_ceiling_val as AC.
  destruct (rjr_bounds B _ K S rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  destruct RJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HF & _).
  apply (bytes_at_transfer rsegs mem); [exact BS|]. intros i Hi. rewrite siv_gl in Hi.
  assert (RL : in_globals frame_RELRO (G_SHAPES + i)).
  { exists 0x226b0, 1680. split; [left; reflexivity | unfold G_SHAPES; lia]. }
  destruct (RIMG _ RL) as (I1 & I2 & I3 & I4).
  pose proof (in_img_low B SEGS _ I1) as IL.
  assert (NS : ~ (S - K <= G_SHAPES + i < S)) by lia.
  assert (NR : ~ rec_area (G_SHAPES + i))
    by (unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE, G_SHAPES; lia).
  rewrite <- SEGS. exact (proj1 (HF _ (or_intror (conj I1 (conj I2 I3))) NS I4 NR)).
Qed.

End SivShapes.

Section SivArg.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GOTG : ms_got_guard B = 0x22d40.
Hypothesis GRD : ms_guard B = 0x54730.
Hypothesis GFACT : forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis GOWN : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis SLACK : block_slack_present B API.
Hypothesis ARGL : arg_line_contract B API.

Lemma siv_home_lower : forall L A sp1 sp2 s n, sp2 <= sp1 -> str_home B L A sp1 s n -> str_home B L A sp2 s n.
Proof.
  intros L A sp1 sp2 s n H [H1|[H1|H1]]; [left; lia | right; left; exact H1 | right; right; exact H1].
Qed.

Lemma siv_str : forall K S L A mem md O Lc Ac mc mdc Rc Oc bc p x,
  sinv B API K S L A mem md O Lc Ac mc mdc Rc Oc bc ->
  ro_agree rsegs mem ->
  str_arg B L A O S K mem p (Some x) ->
  exists slack, 0 <= p < 2 ^ 64 /\ p <> 0 /\
    bytes_at rsegs mc p (x ++ Z_to_bv 8 0 :: slack) /\ no0 x /\ Z.of_nat (length x) <= LMAX /\
    (- (p + Z.of_nat (length x) + 1)) mod 8 <= Z.of_nat (length slack) /\
    (p + Z.of_nat (length (x ++ Z_to_bv 8 0 :: slack)) <= S - K \/ S <= p) /\
    str_home B Lc Ac S p (Z.of_nat (length x) + 1) /\
    (forall a, p <= a < p + Z.of_nat (length (x ++ Z_to_bv 8 0 :: slack)) -> ~ rec_area a).
Proof using SEGS ERRNO_LOW SLACK.
  intros K S L A mem md O Lc Ac mc mdc Rc Oc bc p x SI RA H.
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
        rewrite (mbyte_ro_agree _ _ _ RAc RO), (mbyte_ro_agree _ _ _ RA RO). reflexivity. }
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

Lemma siv_arg_line : forall K S L A mem md O Lc Ac mc mdc Rp fn Oc bc regs_c p x (P : config -> Prop),
  sinv B API K S L A mem md O Lc Ac mc mdc (rec_record Rp fn []) Oc bc ->
  ro_agree rsegs mem -> str_arg B L A O S K mem p (Some x) ->
  YK0s.ret_ok (getr regs_c 1) -> spZ regs_c mod 16 = 0 -> S - K <= spZ regs_c - ARG_LINE_K -> spZ regs_c <= S ->
  getr regs_c 4 = Z_to_bv 64 (ms_tp B) ->
  getr regs_c 10 = Z_to_bv 64 (rec_entry G_REC REC_SC Rp) -> getr regs_c 11 = Z_to_bv 64 p ->
  room_slots (sb_malloc (sb_shift bc A Ac) (Z.of_nat (length x) + 1)) (Z.of_nat (length x) + 1) ->
  (forall L2 A2 regs2 m2 md2 q,
     sinv B API K S L A mem md O L2 A2 m2 md2 (rec_record Rp fn [canon x]) (Oc ++ [(q, Z.of_nat (length x) + 1)]) bc ->
     sb_shift bc A A2 = sb_malloc (sb_shift bc A Ac) (Z.of_nat (length x) + 1) ->
     st_init_done A2 = true -> regs_preserved regs_c regs2 ->
     (forall a, spZ regs_c <= a < S ->
        mbyte rsegs m2 a = mbyte rsegs mc a /\ (writable_at rsegs mc a <-> writable_at rsegs m2 a)) ->
     SR rsegs (mkCfg (mkst regs2 (getr regs_c 1) m2 (seg_rom rsegs)) md2) P) ->
  SR rsegs (mkCfg (mkst regs_c (Z_to_bv 64 ARG_LINE) mc (seg_rom rsegs)) mdc) P.
Proof using SEGS ERRNO_LOW GOTG GRD GFACT GOWN AX SLACK ARGL.
  intros K S L A mem md O Lc Ac mc mdc Rp fn Oc bc regs_c p x P SI RA SA Hra Hal Hlo Hhi Htp H10 H11 ROOM KONT.
  pose proof alloc_ceiling_val as AC. pose proof (aa_laws API) as LAWS.
  pose proof SI as (RJ & GR & _ & _ & _ & RAc & F18 & RS).
  destruct (rjr_bounds B _ K S rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  assert (HN : (length (r_calls Rp) <= 16)%nat)
    by exact (rec_record_calls Rp fn [] (rec_rep_calls_le _ _ _ _ _ _ _ _ GR)).
  destruct (rec_entry_bounds Rp HN) as (ER1 & ER2 & ER3).
  destruct (rec_entry_at rsegs Lc Ac mc Rp fn [] Oc GR) as (P0 & CA).
  pose proof CA as (_ & _ & _ & _ & NA0 & _). cbn [snd length Z.of_nat] in NA0.
  destruct (siv_str K S L A mem md O Lc Ac mc mdc _ Oc bc p x SI RA SA)
    as (slack & PR & Hp0 & BS & N0 & LX & ALN & DJ & HOME & NRA).
  set (e := rec_entry G_REC REC_SC Rp) in *.
  pose proof ARGL as AL. unfold arg_line_contract in AL. rewrite SEGS in AL.
  eapply SR_bind.
  { apply (AL Lc Ac regs_c mc mdc e p 0 x slack (sb_shift bc A Ac)).
    - apply (call_pre_k_of_rjr B _ K S rec_area _ L A mem md Lc Ac mc mdc ARG_LINE_K regs_c RJ Hra Hal);
        [unfold ARG_LINE_K, REC_CANONICAL_K, XMALLOC_K, ALLOC_STACK; lia | exact Hlo | exact Hhi | exact Htp].
    - exact H10.
    - exact H11.
    - exact ER3.
    - exact ER1.
    - exact ER2.
    - apply glob_wr_at; unfold GLOB_LO, GLOB_N, REC_SC, G_REC, REC_SIZE, CALL_SIZE in *; lia.
    - exact NA0.
    - lia.
    - exact BS.
    - exact N0.
    - exact LX.
    - exact ALN.
    - destruct DJ as [D|D]; [left; lia | right; lia].
    - apply (siv_home_lower Lc Ac S); [exact Hhi | exact HOME].
    - unfold iv_apart. apply (siv_nra_apart p _ e (e + CALL_SIZE)).
      + intros a Ha. apply NRA. rewrite length_app. cbn [length]. lia.
      + exact ER1.
      + exact ER2.
      + unfold CALL_SIZE. lia.
      + lia.
    - exact RS.
    - exact ROOM.
    - exact RAc. }
  intros c2 (L2 & A2 & regs2 & m2 & md2 & -> & BK & UB & _ & RA2 & GK & RGN & ALT2).
  destruct ALT2 as [(M6 & _) | (_ & q & POST & Hq0 & QAL & FB & BLK & NA2 & AS2 & BP & INI & RES2)]; [lia|].
  rewrite SEGS in NA2, AS2, BP, RA2.
  pose proof POST as (PM & _ & _ & _ & _ & PR2 & _ & PF & _). rewrite SEGS in PF.
  assert (F182 : f18_words rsegs m2).
  { destruct (ax_statics AX L2 A2 m2 md2 PM) as (_ & (g & Hg & HWg) & _).
    apply (f18_words_after mc m2 g F18); [| exact Hg | rewrite SEGS, GRD in HWg; exact HWg].
    intros i Hi. unfold snprintf_c.GOT_GUARD. rewrite <- GOTG, <- SEGS. exact (GK i Hi). }
  assert (FK : forall a, spZ regs_c <= a < S ->
            mbyte rsegs m2 a = mbyte rsegs mc a /\ (writable_at rsegs mc a <-> writable_at rsegs m2 a)).
  { intros a Ha. pose proof RJ as (HM & _).
    pose proof FB as (FB1 & FB2 & _).
    unfold ARG_LINE_K, REC_CANONICAL_K, XMALLOC_K, ALLOC_STACK in Hlo.
    apply PF.
    - left. lia.
    - intros Ho. pose proof (mr_owned_low B _ LAWS Lc Ac mc mdc a HM Ho). lia.
    - intros Ho. pose proof (mr_owned_low B _ LAWS L2 A2 m2 md2 a PM Ho). lia.
    - unfold scratch_k. intros [H|H]; lia.
    - cbv beta. unfold CALL_OFF_NARGS, CALL_OFF_ARGS, REC_SC, G_REC, REC_SIZE, CALL_SIZE in *. lia. }
  pose proof BLK as (b1 & b2 & EB' & EB).
  assert (SI2 : sinv B API K S L A mem md O L2 A2 m2 md2 (rec_record Rp fn [canon x])
                  (Oc ++ [(q, Z.of_nat (length x) + 1)]) bc).
  { apply (sinv_arg B API SEGS ERRNO_LOW GFACT GOWN AX K S L A mem md O Lc Ac mc mdc Rp fn [] Oc bc ARG_LINE_K regs_c _
             L2 A2 regs2 m2 md2 (canon x) q (Z.of_nat (length x) + 1) SI ltac:(cbn [length]; lia) Hlo Hhi POST).
    - intros a Ha. cbn [length Z.of_nat]. unfold CALL_OFF_NARGS, CALL_OFF_ARGS in *. lia.
    - exact Hq0.
    - exact FB.
    - exact BLK.
    - exact UB.
    - exact BK.
    - exact RGN.
    - exact NA2.
    - exact AS2.
    - exact BP.
    - exact (canon_no0 x N0).
    - pose proof (canon_length x). lia.
    - pose proof (canon_length x). unfold LMAX in *. lia.
    - exact INI.
    - exact RES2.
    - exact RA2.
    - exact F182. }
  rewrite SEGS. apply (KONT L2 A2 regs2 m2 md2 q SI2); [| exact INI | exact PR2 | exact FK].
  rewrite <- (sb_shift_trans bc A Ac A2). rewrite <- (sb_shift_add (sb_shift bc A Ac) Lc Ac L2 A2 b1 b2 q _ EB' EB).
  reflexivity.
Qed.

End SivArg.

Section Main.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GOTG : ms_got_guard B = 0x22d40.
Hypothesis GRD : ms_guard B = 0x54730.
Hypothesis GFACT : forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis GOWN : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Hypothesis RIMG : forall a, in_globals frame_RELRO a ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CTX : ctx_owned B API.
Hypothesis SLACK : block_slack_present B API.
Hypothesis REC : record_contract B API.
Hypothesis ARGL : arg_line_contract B API.
Hypothesis SNP : snprintf_contract.
Hypothesis SSPN : strspn_contract.
Hypothesis SCSPN : strcspn_contract.
Hypothesis RSO : rec_shape_of_contract.
Hypothesis ARGS : forall fx' : YK11.FPState, @arg_s_contract fx' rc B API.
Hypothesis ANS : forall fx' : YK11.FPState, @answer_contract fx' rc B API.

Theorem sup_instance_verb_holds : sup_instance_verb_contract B API.
Proof using SEGS ERRNO_LOW GOTG GRD GFACT GOWN RIMG AX CTX SLACK REC ARGL SNP SSPN SCSPN RSO ARGS ANS.
  unfold sup_instance_verb_contract.
  intros L A regs mem md pl ledger line R O b PRE GA GM HLD SA GS GR RA FRM F18 RES ROOM.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC. pose proof wx_apart_rsegs as WX.
  pose proof ERRNO_LOW as EL.
  pose proof PRE as (PRK & HTS).
  change SUP_INSTANCE_VERB_K with 12432 in PRK, SA |- *.
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  rewrite SEGS in GS, GR, RA, F18, HWS |- *.
  pose proof (sinv_init B API 12432 L A regs mem md R O b PRK ltac:(lia) GR RA F18 RES) as SI0.
  pose proof GR as (Q0 & (_ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & HCODE & _) & _) & _).
  pose proof (rec_rep_calls_le _ _ _ _ _ _ _ _ GR) as H16.
  pose proof (dec_length ledger HLD) as DL.
  assert (LN : Z.of_nat (length line) <= LMAX) by (destruct SA as (_ & _ & HL & _); exact HL).
  change (sup_instance_verb_m R line ledger) with
    (rec_answer (rec_record R REC_INSTANCE_VERB [canon line; dec ledger]) (REC_INSTANCE_VERB, [canon line; dec ledger])
       (shape_of (first_word line)) true) in ROOM.
  assert (LT : (length (snd (rec_answer (rec_record R REC_INSTANCE_VERB [canon line; dec ledger])
                 (REC_INSTANCE_VERB, [canon line; dec ledger]) (shape_of (first_word line)) true)) <= 78)%nat).
  { pose proof (siv_stub_len R REC_INSTANCE_VERB [canon line; dec ledger] (shape_of (first_word line)) true HCODE) as H.
    destruct (shape_of_facts (first_word line)) as (_ & _ & L78 & _). lia. }
  unfold sup_instance_verb_sizes, sb_mallocs in ROOM. cbn [fold_left] in ROOM.
  destruct (rec_entry_bounds R H16) as (EB1 & EB2 & EB3).
  set (e := rec_entry G_REC REC_SC R) in *.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (ST0 : stk rsegs mem (bv_unsigned sp - 12432) (bv_unsigned sp)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (W : writable_at rsegs mem a) by (apply HWS; lia).
    split; [exact W|].
    destruct (writable_hi_present mem a ltac:(lia) W) as [bb E]. exists bb. unfold mrd, wa. rewrite E. reflexivity. }
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp. unfold SUP_INSTANCE_VERB.
    eapply siv_run0 with (lo := bv_unsigned sp - 12432); [exact ST0 | lia | lia]. }
  intros ms1 (can1 & (m1 & -> & MU1 & WM1 & FR1) & EQ1).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
  assert (E1_1 : getr R1 1 = Z_to_bv 64 0x169c4) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 48))
    by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_4 : getr R1 4 = reg_get regs 4) by (rewrite (getr_of_eqv _ _ 4 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_9 : getr R1 9 = Z_to_bv 64 pl) by (rewrite (getr_of_eqv _ _ 9 X1 eq_refl); simp_regs; exact GA).
  assert (E1_18 : getr R1 18 = Z_to_bv 64 ledger) by (rewrite (getr_of_eqv _ _ 18 X1 eq_refl); simp_regs; exact GM).
  assert (E1_10 : getr R1 10 = Z_to_bv 64 7) by (rewrite (getr_of_eqv _ _ 10 X1 eq_refl); simp_regs; reflexivity).
  assert (KR1 : siv_kept regs R1) by siv_kept_tac X1.
  assert (SP1 : spZ R1 = bv_unsigned sp - 48) by (unfold spZ; rewrite E1_2; apply unsigned_lit; lia).
  pose proof (sinv_stack B API SEGS GOWN AX 12432 (bv_unsigned sp) L A mem md O L A mem md R O b m1 _ SI0 MU1 WM1
                ltac:(intros a Ra Hm; cbn in Hm; lia)) as SI1.
  apply (sinv_record B API SEGS ERRNO_LOW AX REC 12432 (bv_unsigned sp) L A mem md O L A m1 md R O b R1
           REC_INSTANCE_VERB _ SI1).
  { rewrite E1_1. apply bv_eq. vm_compute. reflexivity. }
  { rewrite SP1. replace (bv_unsigned sp - 48) with (bv_unsigned sp + (-3) * 16) by ring. rewrite Z.mod_add by lia.
    exact HAL. }
  { rewrite SP1. unfold RECORD_K, ALLOC_STACK. lia. }
  { rewrite SP1. lia. }
  { rewrite E1_4. exact HTP. }
  { exact E1_10. }
  { unfold REC_FN_COUNT, REC_INSTANCE_VERB. lia. }
  intros L1 A1 regs_r m_r md_r O_r SIr BLEr RPr R10 KSTr.
  rewrite sb_shift_refl in BLEr.
  rewrite E1_1.
  pose proof SIr as (RJr & GRr & ONr & B1r & B2r & RAr & F18r & RESr).
  pose proof RJr as (HMr & _).
  destruct (mr_model _ _ LAWS _ _ _ _ HMr) as (Hhr & Hlr & _).
  assert (Er2 : getr regs_r 2 = Z_to_bv 64 (bv_unsigned sp - 48))
    by exact (eq_trans (RPr 2 ltac:(unfold callee_saved; lia)) E1_2).
  assert (Er4 : getr regs_r 4 = reg_get regs 4) by exact (eq_trans (RPr 4 ltac:(unfold callee_saved; lia)) E1_4).
  assert (Er9 : getr regs_r 9 = Z_to_bv 64 pl) by exact (eq_trans (RPr 9 ltac:(unfold callee_saved; lia)) E1_9).
  assert (Er18 : getr regs_r 18 = Z_to_bv 64 ledger)
    by exact (eq_trans (RPr 18 ltac:(unfold callee_saved; lia)) E1_18).
  assert (KRr : siv_kept regs regs_r) by exact (siv_kept_trans _ _ _ KR1 (siv_kept_of_pres _ _ RPr)).
  assert (FRr : rw_cells rsegs m_r (bv_unsigned sp - 32)
                  [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m1); [exact FR1|]. intros i Hi. cbn in Hi.
    destruct (KSTr (bv_unsigned sp - 32 + i)) as [Ea Eb]; [rewrite SP1; lia|]. split; [exact Ea | exact (proj1 Eb)]. }
  eapply evt_SR_canon; [ | exact Hhr | exact Hlr | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. eapply siv_run1. }
  intros ms2 (can2 & -> & EQ2).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ2 eq_refl eq_refl) as (R2 & -> & X2).
  assert (E2_1 : getr R2 1 = Z_to_bv 64 0x169d0) by (rewrite (getr_of_eqv _ _ 1 X2 eq_refl); simp_regs; reflexivity).
  assert (E2_2 : getr R2 2 = Z_to_bv 64 (bv_unsigned sp - 48))
    by (rewrite (getr_of_eqv _ _ 2 X2 eq_refl); simp_regs; exact Er2).
  assert (E2_4 : getr R2 4 = reg_get regs 4) by (rewrite (getr_of_eqv _ _ 4 X2 eq_refl); simp_regs; exact Er4).
  assert (E2_8 : getr R2 8 = Z_to_bv 64 e) by (rewrite (getr_of_eqv _ _ 8 X2 eq_refl); simp_regs; exact R10).
  assert (E2_9 : getr R2 9 = Z_to_bv 64 pl) by (rewrite (getr_of_eqv _ _ 9 X2 eq_refl); simp_regs; exact Er9).
  assert (E2_10 : getr R2 10 = Z_to_bv 64 e) by (rewrite (getr_of_eqv _ _ 10 X2 eq_refl); simp_regs; exact R10).
  assert (E2_11 : getr R2 11 = Z_to_bv 64 pl) by (rewrite (getr_of_eqv _ _ 11 X2 eq_refl); simp_regs; exact Er9).
  assert (E2_18 : getr R2 18 = Z_to_bv 64 ledger) by (rewrite (getr_of_eqv _ _ 18 X2 eq_refl); simp_regs; exact Er18).
  assert (KR2 : siv_kept regs_r R2) by siv_kept_tac X2.
  assert (SP2 : spZ R2 = bv_unsigned sp - 48) by (unfold spZ; rewrite E2_2; apply unsigned_lit; lia).
  apply (siv_arg_line B API SEGS ERRNO_LOW GOTG GRD GFACT GOWN AX SLACK ARGL 12432 (bv_unsigned sp) L A mem md O
           L1 A1 m_r md_r R REC_INSTANCE_VERB O_r b R2 pl line _ SIr RA SA).
  { rewrite E2_1. apply bv_eq. vm_compute. reflexivity. }
  { rewrite SP2. replace (bv_unsigned sp - 48) with (bv_unsigned sp + (-3) * 16) by ring. rewrite Z.mod_add by lia.
    exact HAL. }
  { rewrite SP2. unfold ARG_LINE_K, REC_CANONICAL_K, XMALLOC_K, ALLOC_STACK. lia. }
  { rewrite SP2. lia. }
  { rewrite E2_4. exact HTP. }
  { exact E2_10. }
  { exact E2_11. }
  { eapply room_slots_mono; [| | exact ROOM]; [apply siv_le_a; [exact BLEr | lia | lia] | unfold LMAX in *; lia]. }
  intros L3 A3 R3 m3 md3 p SI3 EQB3 INIT3 PR3 KST3.
  rewrite E2_1.
  pose proof SI3 as (RJ3 & GR3 & ON3 & B13 & B23 & RA3 & F183 & RES3).
  pose proof RJ3 as (HM3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSC3 & _).
  destruct (mr_model _ _ LAWS _ _ _ _ HM3) as (Hh3 & Hl3 & _).
  assert (E3_2 : getr R3 2 = Z_to_bv 64 (bv_unsigned sp - 48))
    by exact (eq_trans (PR3 2 ltac:(unfold callee_saved; lia)) E2_2).
  assert (E3_4 : getr R3 4 = reg_get regs 4) by exact (eq_trans (PR3 4 ltac:(unfold callee_saved; lia)) E2_4).
  assert (E3_8 : getr R3 8 = Z_to_bv 64 e) by exact (eq_trans (PR3 8 ltac:(unfold callee_saved; lia)) E2_8).
  assert (E3_9 : getr R3 9 = Z_to_bv 64 pl) by exact (eq_trans (PR3 9 ltac:(unfold callee_saved; lia)) E2_9).
  assert (E3_18 : getr R3 18 = Z_to_bv 64 ledger) by exact (eq_trans (PR3 18 ltac:(unfold callee_saved; lia)) E2_18).
  assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp - 32)
                  [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m_r); [exact FRr|]. intros i Hi. cbn in Hi.
    destruct (KST3 (bv_unsigned sp - 32 + i)) as [Ea Eb]; [rewrite SP2; lia|]. split; [exact Ea | exact (proj1 Eb)]. }
  pose proof F183 as (GG3 & canary & GW3).
  assert (GGb : bytes_at rsegs m3 snprintf_c.GOT_GUARD (Mem.le8 (Z_to_bv 64 snprintf_c.GUARD))).
  { destruct GG3 as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (GWb : bytes_at rsegs m3 snprintf_c.GUARD (Mem.le8 canary)).
  { destruct GW3 as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (STn : stk rsegs (normalize_cj rsegs m3) (bv_unsigned sp - 12432) (bv_unsigned sp - 32)).
  { apply stk_normalize_cj; [lia | lia | intros a Ha; rewrite <- SEGS; apply HSC3; left; lia]. }
  pose proof (bytes_at_normalize_cj_low rsegs m3 snprintf_c.GOT_GUARD (Mem.le8 (Z_to_bv 64 snprintf_c.GUARD)) RA3
    ltac:(rewrite Mem.length_le8; unfold snprintf_c.GOT_GUARD, TASK_SIZE; lia) GGb) as GGn.
  pose proof (bytes_at_normalize_cj_low rsegs m3 snprintf_c.GUARD (Mem.le8 canary) RA3
    ltac:(rewrite Mem.length_le8; unfold snprintf_c.GUARD, TASK_SIZE; lia) GWb) as GWn.
  assert (Q8 : reg_get R3 8 = Z_to_bv 64 e) by exact E3_8.
  assert (Q18 : reg_get R3 18 = Z_to_bv 64 ledger) by exact E3_18.
  assert (Q2 : reg_get R3 2 = Z_to_bv 64 (bv_unsigned sp - 48)) by exact E3_2.
  eapply evt_SR_canon; [ | exact Hh3 | exact Hl3 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite Q8, Q18, Q2.
    eapply (evt_normalize_cj rsegs); [exact WX | exact RA3 |].
    eapply (siv_run2 SNP) with (lo := bv_unsigned sp - 12432) (canary := canary).
    - exact HLD.
    - rewrite unsigned_lit by lia. replace (bv_unsigned sp - 48 + 16) with (bv_unsigned sp - 32) by ring. exact STn.
    - rewrite unsigned_lit by lia. unfold SNPRINTF_K. lia.
    - lia.
    - rewrite unsigned_lit by lia. lia.
    - exact FRM.
    - exact (mem_inv_cj_inv rsegs _ (mem_inv_cj_normalize rsegs m3)).
    - exact (mem_inv_cj_task rsegs _ (mem_inv_cj_normalize rsegs m3)).
    - rewrite unsigned_lit by lia. lia.
    - exact GGn.
    - exact GWn. }
  intros ms4 (can4 & (s4n & Q4 & REL4 & RO4) & EQ4).
  unfold siv_mid2 in Q4.
  destruct Q4 as (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F1 & fc1 & m4n & slack
    & -> & MU4n & WM4n & MI4n & FRM1 & FK1 & SL & BUF4n).
  destruct (ms_rel_cj_MS _ _ _ _ _ _ _ _ REL4) as [EC4 MR4r].
  revert EC4 MR4r RO4 EQ4. generalize (ms_mem can4) as m4. intros m4 EC4 MR4r RO4 EQ4. subst can4.
  pose proof (munch_rel_cj rsegs _ _ _ _ _ (mem_rel_cj_normalize rsegs m3 RA3) MR4r RO4 MU4n) as MU4.
  pose proof (wmono_rel_cj rsegs _ _ _ _ (mem_rel_cj_normalize rsegs m3 RA3) MR4r RO4 WM4n) as WM4.
  pose proof (bytes_at_rel_cj rsegs _ _ _ _ MR4r BUF4n) as BUF4.
  destruct (eqv_mkst_fx _ _ _ _ _ _ _ EQ4) as (R4 & -> & X4).
  clear MU4n WM4n MI4n BUF4n EQ4 MR4r.
  rewrite unsigned_lit in MU4, BUF4 by lia.
  assert (E4_1 : getr R4 1 = Z_to_bv 64 0x169f4) by (rewrite (getr_of_eqv _ _ 1 X4 eq_refl); simp_regs; reflexivity).
  assert (E4_2 : getr R4 2 = Z_to_bv 64 (bv_unsigned sp - 48))
    by (rewrite (getr_of_eqv _ _ 2 X4 eq_refl); simp_regs; reflexivity).
  assert (E4_4 : getr R4 4 = reg_get regs 4) by (rewrite (getr_of_eqv _ _ 4 X4 eq_refl); simp_regs; exact E3_4).
  assert (E4_8 : getr R4 8 = Z_to_bv 64 e) by (rewrite (getr_of_eqv _ _ 8 X4 eq_refl); simp_regs; reflexivity).
  assert (E4_9 : getr R4 9 = Z_to_bv 64 pl) by (rewrite (getr_of_eqv _ _ 9 X4 eq_refl); simp_regs; exact E3_9).
  assert (E4_10 : getr R4 10 = Z_to_bv 64 e) by (rewrite (getr_of_eqv _ _ 10 X4 eq_refl); simp_regs; reflexivity).
  assert (E4_11 : getr R4 11 = Z_to_bv 64 (bv_unsigned sp - 48))
    by (rewrite (getr_of_eqv _ _ 11 X4 eq_refl); simp_regs; reflexivity).
  assert (KR4 : siv_kept R3 R4) by siv_kept_tac X4.
  assert (SP4 : spZ R4 = bv_unsigned sp - 48) by (unfold spZ; rewrite E4_2; apply unsigned_lit; lia).
  pose proof (sinv_stack B API SEGS GOWN AX 12432 (bv_unsigned sp) L A mem md O L3 A3 m3 md3 _ _ b m4 _ SI3 MU4 WM4
                ltac:(intros a Ra Hm; cbn in Hm; lia)) as SI4.
  assert (FR4 : rw_cells rsegs m4 (bv_unsigned sp - 32)
                  [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_out rsegs _ m3 m4 _ _ FR3 MU4). intros i Hi. cbn in Hi. split; [lia|]. cbn [outside].
    split; [lia | exact I]. }
  apply (sinv_arg_sn (fx := mkFP F1 fc1) B API SEGS ERRNO_LOW GFACT GOWN AX (ARGS _) 12432 (bv_unsigned sp) L A mem md O
           L3 A3 m4 md3 R REC_INSTANCE_VERB [canon line] (O_r ++ [(p, Z.of_nat (length line) + 1)]) b R4
           (bv_unsigned sp - 48) (Some (dec ledger)) _ SI4).
  { cbn [length]. lia. }
  { rewrite E4_1. apply bv_eq. vm_compute. reflexivity. }
  { rewrite SP4. replace (bv_unsigned sp - 48) with (bv_unsigned sp + (-3) * 16) by ring. rewrite Z.mod_add by lia.
    exact HAL. }
  { rewrite SP4. unfold ARG_S_K, XMALLOC_K, ALLOC_STACK. lia. }
  { rewrite SP4. lia. }
  { rewrite E4_4. exact HTP. }
  { exact E4_10. }
  { exact E4_11. }
  { cbn [arg_s_src]. rewrite SP4, SEGS.
    split; [lia|]. split; [apply dec_no0|]. split; [unfold LMAX; lia|].
    exists slack. split; [exact BUF4|].
    split; [rewrite SL; pose proof (siv_mod8 (bv_unsigned sp) (Z.of_nat (length (dec ledger))) HAL ltac:(lia)); lia|].
    split; [right; lia|]. left. split; lia. }
  { cbn [sarg]. eapply room_slots_mono; [| | exact ROOM]; [| unfold LMAX; lia].
    rewrite EQB3. apply siv_le_b; [exact BLEr | lia]. }
  intros L5 A5 R5 m5 md5 p2 SI5 EQB5 INIT5 PR5 KST5.
  rewrite E4_1.
  pose proof SI5 as (RJ5 & GR5 & ON5 & B15 & B25 & RA5 & F185 & RES5).
  pose proof RJ5 as (HM5 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSC5 & _).
  destruct (mr_model _ _ LAWS _ _ _ _ HM5) as (Hh5 & Hl5 & _).
  assert (FR5 : rw_cells rsegs m5 (bv_unsigned sp - 32)
                  [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m4); [exact FR4|]. intros i Hi. cbn in Hi.
    destruct (KST5 (bv_unsigned sp - 32 + i)) as [Ea Eb]; [rewrite SP4; lia|]. split; [exact Ea | exact (proj1 Eb)]. }
  assert (E5_2 : getr R5 2 = Z_to_bv 64 (bv_unsigned sp - 48))
    by exact (eq_trans (PR5 2 ltac:(unfold callee_saved; lia)) E4_2).
  assert (E5_4 : getr R5 4 = reg_get regs 4) by exact (eq_trans (PR5 4 ltac:(unfold callee_saved; lia)) E4_4).
  assert (E5_8 : getr R5 8 = Z_to_bv 64 e) by exact (eq_trans (PR5 8 ltac:(unfold callee_saved; lia)) E4_8).
  assert (E5_9 : getr R5 9 = Z_to_bv 64 pl) by exact (eq_trans (PR5 9 ltac:(unfold callee_saved; lia)) E4_9).
  destruct (siv_str B API SEGS ERRNO_LOW SLACK 12432 (bv_unsigned sp) L A mem md O L5 A5 m5 md5 _ _ b pl line SI5 RA SA)
    as (slack5 & PR0 & Hp0 & BS5 & N0 & LX5 & ALN5 & DJ5 & HOME5 & NRA5).
  rewrite length_app in DJ5. cbn [length] in DJ5.
  assert (LB5 : bytes_at rsegs m5 pl (line ++ [Z_to_bv 8 0])).
  { replace (line ++ Z_to_bv 8 0 :: slack5) with ((line ++ [Z_to_bv 8 0]) ++ slack5) in BS5
      by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app in BS5. exact (proj1 BS5). }
  pose proof F185 as (GG5 & can5 & GW5).
  apply cells_c8 in GG5. apply cells_c8 in GW5.
  assert (STn5 : stk rsegs (normalize rsegs m5) (bv_unsigned sp - 12432) (bv_unsigned sp - 48)).
  { apply stk_norm; [lia | lia |]. intros a Ha. rewrite <- SEGS. apply HSC5. left. lia. }
  pose proof (bytes_at_normalize rsegs m5 _ _ RA5
                (siv_rjr_shapes B API SEGS RIMG 12432 (bv_unsigned sp) O L A mem md L5 A5 m5 md5 RJ5 GS)) as GSn.
  pose proof (bytes_at_normalize rsegs m5 _ _ RA5 GG5) as GGn5.
  pose proof (bytes_at_normalize rsegs m5 _ _ RA5 GW5) as GWn5.
  pose proof (bytes_at_normalize rsegs m5 _ _ RA5 LB5) as LBn.
  assert (Q52 : reg_get R5 2 = Z_to_bv 64 (bv_unsigned sp - 48)) by exact E5_2.
  assert (Q59 : reg_get R5 9 = Z_to_bv 64 pl) by exact E5_9.
  eapply evt_SR_canon; [ | exact Hh5 | exact Hl5 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite Q52, Q59.
    eapply (evt_normalize rsegs); [exact WX | exact RA5 |].
    eapply (siv_after SSPN SCSPN RSO) with (lo := bv_unsigned sp - 12432) (can := can5).
    - rewrite unsigned_lit by lia. exact STn5.
    - rewrite unsigned_lit by lia. lia.
    - lia.
    - exact GSn.
    - apply mem_inv_normalize.
    - exact GGn5.
    - exact GWn5.
    - exact LBn.
    - exact N0.
    - exact Hp0.
    - rewrite unsigned_lit by lia. lia. }
  intros ms6 (can6 & (s6n & Q6 & REL6 & RO6) & EQ6).
  destruct Q6 as (m6n & u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & -> & MU6n & WM6n).
  destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL6) as [EC6 MR6r].
  revert EC6 MR6r RO6 EQ6. generalize (ms_mem can6) as m6. intros m6 EC6 MR6r RO6 EQ6. subst can6.
  pose proof (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs m5 RA5) MR6r RO6 MU6n) as MU6.
  pose proof (wmono_rel rsegs _ _ _ _ (mem_rel_normalize rsegs m5 RA5) MR6r RO6 WM6n) as WM6.
  clear MU6n WM6n MR6r.
  destruct (eqv_mkst_fx _ _ _ _ _ _ _ EQ6) as (R6 & -> & X6). clear EQ6.
  rewrite unsigned_lit in MU6 by lia.
  assert (E6_1 : getr R6 1 = Z_to_bv 64 0x16a48) by (rewrite (getr_of_eqv _ _ 1 X6 eq_refl); simp_regs; reflexivity).
  assert (E6_2 : getr R6 2 = Z_to_bv 64 (bv_unsigned sp - 48))
    by (rewrite (getr_of_eqv _ _ 2 X6 eq_refl); simp_regs; reflexivity).
  assert (E6_4 : getr R6 4 = reg_get regs 4) by (rewrite (getr_of_eqv _ _ 4 X6 eq_refl); simp_regs; exact E5_4).
  assert (E6_10 : getr R6 10 = Z_to_bv 64 e) by (rewrite (getr_of_eqv _ _ 10 X6 eq_refl); simp_regs; exact E5_8).
  assert (E6_11 : getr R6 11 = Z_to_bv 64 (shape_find shape_rows (first_word line)))
    by (rewrite (getr_of_eqv _ _ 11 X6 eq_refl); simp_regs; reflexivity).
  assert (E6_12 : getr R6 12 = Z_to_bv 64 1) by (rewrite (getr_of_eqv _ _ 12 X6 eq_refl); simp_regs; reflexivity).
  assert (KR6 : siv_kept R5 R6) by siv_kept_tac X6.
  assert (SP6 : spZ R6 = bv_unsigned sp - 48) by (unfold spZ; rewrite E6_2; apply unsigned_lit; lia).
  pose proof (sinv_stack B API SEGS GOWN AX 12432 (bv_unsigned sp) L A mem md O L5 A5 m5 md5 _ _ b m6 _ SI5 MU6 WM6
                ltac:(intros a Ra Hm; cbn in Hm; lia)) as SI6.
  pose proof SI6 as (_ & _ & _ & _ & _ & RA6 & _).
  assert (FR6 : rw_cells rsegs m6 (bv_unsigned sp - 32)
                  [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_out rsegs _ m5 m6 _ _ FR5 MU6). intros i Hi. cbn in Hi. split; [lia|]. cbn [outside].
    split; [lia | exact I]. }
  assert (BLE5 : sb_le (sb_shift b A A5)
                   (sb_malloc (sb_malloc b (Z.of_nat (length line) + 1)) (Z.of_nat (length (dec ledger)) + 1))).
  { rewrite EQB5, EQB3. apply sb_malloc_mono, sb_malloc_mono. exact BLEr. }
  assert (AK : ANSWER_K = 12384) by reflexivity.
  eapply SR_bind.
  { apply (siv_answer_call (fx := mkFP F1 fc1) B API SEGS AX ERRNO_LOW (ANS _) SLACK 12432 (bv_unsigned sp) L A mem md O
             L5 A5 R6 m6 md5 (rec_record R REC_INSTANCE_VERB [canon line; dec ledger])
             ((O_r ++ [(p, Z.of_nat (length line) + 1)]) ++ [(p2, Z.of_nat (length (dec ledger)) + 1)]) b
             (sb_malloc (sb_malloc b (Z.of_nat (length line) + 1)) (Z.of_nat (length (dec ledger)) + 1))
             e (shape_find shape_rows (first_word line)) (REC_INSTANCE_VERB, [canon line; dec ledger])
             (shape_of (first_word line)) true SI6).
    - rewrite E6_1. apply bv_eq. vm_compute. reflexivity.
    - rewrite SP6. replace (bv_unsigned sp - 48) with (bv_unsigned sp + (-3) * 16) by ring. rewrite Z.mod_add by lia.
      exact HAL.
    - rewrite SP6, AK. lia.
    - rewrite SP6. lia.
    - rewrite SP6. lia.
    - rewrite E6_4. exact HTP.
    - exact E6_10.
    - exact E6_11.
    - rewrite E6_12. reflexivity.
    - intros _. apply siv_ans_shape. exact RA6.
    - intros _ _. exact (ans_entry_record R REC_INSTANCE_VERB [canon line; dec ledger] H16).
    - cbn [fp_csr]. exact FRM1.
    - exact BLE5.
    - eapply room_slots_mono; [| | exact ROOM]; [| unfold LMAX; lia].
      apply siv_le_c. exact BLE5. }
  intros c7 MID. unfold siv_ans_mid in MID.
  destruct MID as (fx' & L' & A' & R7 & m7 & md7 & O' & q & -> & FPK & RJ7 & PR7 & KST7 & A07 & GR7 & ON7 & BL7 & INq
    & FRq & NIq & BYq & OK7 & AP7 & RA7 & F187 & INIT7 & RG7 & SB7 & RS7).
  pose proof RJ7 as (HM7 & _).
  destruct (mr_model _ _ LAWS _ _ _ _ HM7) as (Hh7 & Hl7 & _).
  assert (FR7 : rw_cells rsegs m7 (bv_unsigned sp - 32)
                  [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m6); [exact FR6|]. intros i Hi. cbn in Hi.
    destruct (KST7 (bv_unsigned sp - 32 + i)) as [Ea Eb]; [rewrite SP6; lia|]. split; [exact Ea | exact (proj1 Eb)]. }
  assert (Q72 : reg_get R7 2 = Z_to_bv 64 (bv_unsigned sp + -48))
    by exact (eq_trans (PR7 2 ltac:(unfold callee_saved; lia)) E6_2).
  rewrite E6_1.
  eapply evt_SR_canon; [ | exact Hh7 | exact Hl7 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite Q72.
    eapply siv_run4; [exact FR7 | lia]. }
  intros ms8 (can8 & Q8' & EQ8). subst can8.
  destruct (eqv_mkst_fx _ _ _ _ _ _ _ EQ8) as (R8 & -> & X8). clear EQ8.
  assert (KR8 : siv_kept R7 R8) by siv_kept_tac X8.
  assert (RP : regs_preserved regs R8).
  { apply siv_pres.
    - apply (siv_kept_trans _ _ _ KRr). apply (siv_kept_trans _ _ _ KR2).
      apply (siv_kept_trans _ _ _ (siv_kept_of_pres _ _ PR3)). apply (siv_kept_trans _ _ _ KR4).
      apply (siv_kept_trans _ _ _ (siv_kept_of_pres _ _ PR5)). apply (siv_kept_trans _ _ _ KR6).
      exact (siv_kept_trans _ _ _ (siv_kept_of_pres _ _ PR7) KR8).
    - rewrite (getr_of_eqv _ _ (Z_to_bv 5 2) X8 eq_refl). simp_regs. first [reflexivity | unfold getr; reflexivity].
    - rewrite (getr_of_eqv _ _ (Z_to_bv 5 8) X8 eq_refl). simp_regs. first [reflexivity | unfold getr; reflexivity].
    - rewrite (getr_of_eqv _ _ (Z_to_bv 5 9) X8 eq_refl). simp_regs. first [reflexivity | unfold getr; reflexivity].
    - rewrite (getr_of_eqv _ _ (Z_to_bv 5 18) X8 eq_refl). simp_regs. first [reflexivity | unfold getr; reflexivity]. }
  assert (E8_10 : getr R8 10 = Z_to_bv 64 q) by (rewrite (getr_of_eqv _ _ 10 X8 eq_refl); simp_regs; exact A07).
  assert (RPC : ret_pc (reg_get regs 1) = getr regs 1) by exact (ret_pc_of_ok _ HRA).
  apply SR_ret. cbv beta. unfold sup_instance_verb_ret. rewrite SEGS.
  exists (mkFP (@fp_regs fx') (@fp_csr fx')), L', A', R8, m7, md7, (fst (sup_instance_verb_m R line ledger)), O',
    (snd (sup_instance_verb_m R line ledger)), q.
  split; [apply surjective_pairing|].
  split; [rewrite RPC; reflexivity|].
  split.
  { destruct FPK as [FZ' FK']. split; [exact FZ'|]. intros r Hr. cbn [fp_regs]. rewrite (FK' r Hr). cbn [fp_regs].
    apply FK1. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
    unfold fs_saved in Hr. rewrite Z.mod_small by lia. lia. }
  split.
  { apply (rjr_final B (aa_MR API) CTX 12432 rec_area (fun pn => In pn O) (fun a => In a (map fst O)) L A regs mem md
             L' A' R8 m7 md7 PRK RJ7 RP).
    intros a0 k0 G. exact (in_map fst O (a0, k0) G). }
  split; [exact E8_10|]. split; [exact GR7|]. split; [exact ON7|]. split; [exact BL7|]. split; [exact INq|].
  split; [exact FRq|]. split; [exact NIq|]. split; [exact BYq|]. split; [exact OK7|].
  split.
  { change (snd (sup_instance_verb_m R line ledger)) with
      (snd (rec_answer (rec_record R REC_INSTANCE_VERB [canon line; dec ledger])
              (REC_INSTANCE_VERB, [canon line; dec ledger]) (shape_of (first_word line)) true)).
    intros p0 k0 H1 H2. pose proof (AP7 p0 k0 H1 H2). lia. }
  split; [exact (siv_rjr_shapes B API SEGS RIMG 12432 (bv_unsigned sp) O L A mem md L' A' m7 md7 RJ7 GS)|].
  split; [exact RA7|]. split; [exact F187|]. split; [exact INIT7|]. split; [exact RG7|].
  split; [|exact RS7].
  unfold sup_instance_verb_sizes, sb_mallocs. cbn [fold_left]. exact SB7.
Qed.

End Main.
