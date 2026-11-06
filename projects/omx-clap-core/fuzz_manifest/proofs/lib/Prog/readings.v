From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import ManifestModel ManifestMem LibcNeeds_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import printf_facts_c snprintf_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestB.
Import ListNotations.
Open Scope Z_scope.

Definition rd_cells (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (junk : list byte) : list cell :=
  [CB 72 junk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma rd_epi : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 r x26 x27 t3 t4 t5 t6 : word)
    (m : word -> option byte) (lo : Z) (junk : list byte),
  176 <= bv_unsigned sp ->
  rw_cells rsegs m (bv_unsigned sp - 176) (rd_cells ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 junk) ->
  stk rsegs m lo (bv_unsigned sp - 176) -> lo <= bv_unsigned sp - 176 ->
  evt rsegs
    (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 r a1 a2 a3 a4 a5 a6 a7
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (ret_pc ra) fc None m (seg_rom rsegs) /\ stk rsegs m lo (bv_unsigned sp))
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp - 176)) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
             x18 x19 x20 x21 x22 x23 x24 r x26 x27 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13f5c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
    x18 x19 x20 x21 x22 x23 x24 r x26 x27 t3 t4 t5 t6 m lo junk HS FR ST HLO.
  unfold rd_cells in FR.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  assert (SPU : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 176)) = bv_unsigned sp - 176) by (apply unsigned_lit; lia).
  do 15 zstep.
  replace (bv_unsigned sp - 176 + 176) with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned.
  release_frame FR ST (bv_unsigned sp).
  zstep.
  apply evt_done. split; [reflexivity | exact ST].
Qed.

Definition rd_ret (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (r : word) (lo : Z) (W : list ivl) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 r a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch W m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp).

Definition rd_call (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (ra1 x8 x9 a0 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word) (pc lo : Z) (m : word -> option byte)
    : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (junk : list byte)
                    (m' : word -> option byte),
    ms' = MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp - 176)) gp tp t0' t1' t2' x8 x9 a0 a1' a2' a3' a4' a5' a6' a7'
                  x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6')
             F (Z_to_bv 64 pc) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp - 176, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
    stk rsegs m' lo (bv_unsigned sp - 176) /\
    rw_cells rsegs m' (bv_unsigned sp - 176) (rd_cells ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 junk).

Lemma rd_pro : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (ub us : list byte),
  LibcNeeds_c.strlen_contract ->
  cstr_at m (bv_unsigned a1) ub us -> mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp) -> lo + 176 <= bv_unsigned sp ->
  off_stack sp 176 (bv_unsigned a1) (Z.of_nat (length ub + 1 + length us)) ->
  (length ub <= 255)%nat ->
  evt rsegs
    (fun ms' =>
       (ub = [] /\ rd_ret ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 0) lo
                     [(bv_unsigned sp - 176, bv_unsigned sp)] m ms') \/
       (ub <> [] /\ rd_call ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                     (Z_to_bv 64 0x13c9c) a2 a1 (Z_to_bv 64 (Z.of_nat (length ub) + 3)) a0
                     (Z_to_bv 64 (Z.of_nat (length ub))) s4 (Z_to_bv 64 (Z.of_nat (length ub) + 3)) s6 s7 s8 s9 s10 s11
                     0x13a88 lo m ms'))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13c3c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    ub us STRLEN CU MI ST LO OU UL.
  unfold off_stack in OU. destruct CU as [BA [NZ AL]].
  pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (proj1 ST) as LO0.
  carve_frame 176%nat ST.
  do 19 zstep.
  set (j := firstn 72 _) in *.
  assert (SPU : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -176)) = bv_unsigned sp + -176) by (apply unsigned_lit; lia).
  eapply evt_cut.
  { eapply STRLEN with (bs := ub) (slack := us) (lo := lo);
      [ split; [exact BA | split; assumption] | exact MI | rewrite SPU; exact ST ]. }
  intros ms' POST.
  destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 &
    E & MUc & WMc & MIc & STc & Ra0).
  subst ms' a0'. rewrite SPU in MUc, STc.
  replace (ret_pc (Z_to_bv 64 81032)) with (Z_to_bv 64 81032) by (apply bv_eq; vm_compute; reflexivity).
  transport_after_call rsegs m0 m2 MUc WMc.
  clear SPU MUc WMc MI.
  assert (LU : 0 <= Z.of_nat (length ub) < 2 ^ 64) by lia.
  zstep.
  if_cases HC.
  - zify_cond HC.
    assert (UB : ub = []) by (destruct ub; [reflexivity | cbn in HC; lia]).
    zstep.
    replace (bv_unsigned sp + -176) with (bv_unsigned sp - 176) in * by lia.
    eapply evt_cut.
    { eapply rd_epi with (lo := lo); [lia | exact FR | exact STc | lia]. }
    intros ms' [-> STf]. apply evt_done. left. split; [exact UB|].
    unfold rd_ret. do 15 eexists. split; [reflexivity|].
    split; [replace (bv_unsigned sp - 176) with (bv_unsigned sp + -176) by lia; exact MU|].
    split; [exact WM|]. split; [exact MIc | exact STf].
  - zify_cond HC.
    do 4 zstep.
    replace (bv_unsigned sp + -176) with (bv_unsigned sp - 176) in * by lia.
    apply evt_done. right. split; [destruct ub; [cbn in HC; lia | discriminate]|].
    unfold rd_call. do 16 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MIc|]. split; [exact STc | exact FR].
Qed.

Lemma rd_fail : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (x1 t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
    (m : word -> option byte) (lo : Z) (junk : list byte),
  176 <= bv_unsigned sp ->
  rw_cells rsegs m (bv_unsigned sp - 176) (rd_cells ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 junk) ->
  stk rsegs m lo (bv_unsigned sp - 176) -> lo <= bv_unsigned sp - 176 ->
  evt rsegs
    (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (ret_pc ra) fc None m (seg_rom rsegs) /\ stk rsegs m lo (bv_unsigned sp))
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp - 176)) gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13c9c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc x1 t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7
    x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 m lo junk HS FR ST HLO.
  zstep.
  if_true. zstep.
  eapply evt_cut; [eapply rd_epi with (lo := lo); [exact HS | exact FR | exact ST | exact HLO] |].
  intros ms' H. apply evt_done. exact H.
Qed.

Definition rd_found (txt : word) (tb ub : list byte) : word :=
  match find_sub (zbytes tb) (60 :: zbytes ub ++ [62]) with
  | Some i => Z_to_bv 64 (bv_unsigned txt + Z.of_nat i)
  | None => Z_to_bv 64 0
  end.

Lemma zbytes_z8 : forall l : list Z, Forall (fun c => 0 <= c < 256) l -> map bv_unsigned (map (Z_to_bv 8) l) = l.
Proof.
  induction l as [|c l IH]; intros H; [reflexivity|]. inversion H as [|? ? Hc Hl]; subst.
  cbn [map]. rewrite IH by exact Hl. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small. exact Hc.
Qed.

Lemma z8_zbytes : forall bs : list byte, map (Z_to_bv 8) (zbytes bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [zbytes map] in *. unfold zbytes in IH. rewrite IH. f_equal.
  apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma zbytes_range : forall bs : list byte, Forall (fun c => 0 <= c < 256) (zbytes bs).
Proof.
  intros bs. unfold zbytes. apply Forall_map. apply Forall_forall. intros b _.
  pose proof (bv_unsigned_in_range 8 b) as R. exact R.
Qed.

Lemma zbytes_nz : forall bs : list byte, Forall (fun b => bv_unsigned b <> 0) bs -> Forall (fun c => 0 < c < 256) (zbytes bs).
Proof.
  intros bs H. unfold zbytes. apply Forall_map. eapply Forall_impl; [|exact H].
  intros b Hb. cbv beta. pose proof (bv_unsigned_in_range 8 b) as R.
  assert (M : bv_modulus 8 = 256) by reflexivity. rewrite M in R. destruct R as [R1 R2].
  split; [apply Z.le_neq; split; [exact R1 | intro E; apply Hb; symmetry; exact E] | exact R2].
Qed.

Lemma img_cover : forall x, 0x10000 <= x < 0x50000 ->
  exists s, In s (segments_reserved rsegs) /\ bv_unsigned (fst s) <= x < bv_unsigned (fst s) + bv_unsigned (snd s).
Proof.
  intros x Hx.
  assert (C : forall lo len, existsb (fun s : word * word => (bv_unsigned (fst s) <=? lo) &&
                (lo + len <=? bv_unsigned (fst s) + bv_unsigned (snd s))) (segments_reserved rsegs) = true ->
              lo <= x < lo + len ->
              exists s, In s (segments_reserved rsegs) /\ bv_unsigned (fst s) <= x < bv_unsigned (fst s) + bv_unsigned (snd s)).
  { intros lo len H Hr. apply existsb_exists in H as (s0 & Hs & Hb). apply andb_prop in Hb as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2. exists s0. split; [exact Hs | lia]. }
  destruct (Z_lt_le_dec x 0x12000); [apply (C 0x10000 0x2000); [vm_compute; reflexivity | lia]|].
  destruct (Z_lt_le_dec x 0x1e000); [apply (C 0x12000 0xc000); [vm_compute; reflexivity | lia]|].
  destruct (Z_lt_le_dec x 0x1f000); [apply (C 0x1e000 0x1000); [vm_compute; reflexivity | lia]|].
  apply (C 0x1f000 0x31000); [vm_compute; reflexivity | lia].
Qed.

Lemma img_free_disj : forall D n a k, pf_img_free D n -> 0x10000 <= a -> a + k <= 0x50000 -> 0 < n -> 0 < k ->
  D + n <= a \/ a + k <= D.
Proof.
  intros D n a k H Ha Hk Hn Hk0. destruct (Z_le_gt_dec (D + n) a) as [Q|Q]; [left; exact Q|].
  destruct (Z_le_gt_dec (a + k) D) as [Q2|Q2]; [right; exact Q2|]. exfalso.
  destruct (img_cover (Z.max a D) ltac:(lia)) as (s0 & Hs & Hr). apply (H (Z.max a D - D) ltac:(lia) s0 Hs).
  replace (D + (Z.max a D - D)) with (Z.max a D) by lia. exact Hr.
Qed.

Lemma rd_mid : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (x1 t0 t1 t2 rp uri w a1 a2 a3 a4 a5 a6 a7 txt un x20 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 canary : word)
    (m : word -> option byte) (lo : Z) (junk wj ns tb ts ub us : list byte),
  snprintf_contract -> LibcNeeds_c.strstr_contract ->
  176 <= bv_unsigned sp -> bv_unsigned sp < 2 ^ 63 ->
  rw_cells rsegs m (bv_unsigned sp - 176) (rd_cells ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 junk) ->
  stk rsegs m lo (bv_unsigned sp - 176) -> lo + SNPRINTF_K <= bv_unsigned sp - 176 -> IMG_END <= lo ->
  mem_inv rsegs m -> MemNorm.task_mem rsegs m -> frm0 fc ->
  cstr_at m (bv_unsigned txt) tb ts -> cstr_at m (bv_unsigned uri) ub us -> ub <> [] -> (length ub <= 255)%nat ->
  bytes_at rsegs m ManifestB.FMT_WHOLE_STR (map (Z_to_bv 8) (ManifestB.fmt_whole ++ [0])) ->
  rw_cells rsegs m (bv_unsigned w) [CB (length ub + 3) wj] ->
  bytes_at rsegs m (bv_unsigned w + Z.of_nat (length ub) + 3) ns ->
  (- (bv_unsigned w + Z.of_nat (length ub) + 3)) mod 8 <= Z.of_nat (length ns) ->
  0 < bv_unsigned w -> pf_img_free (bv_unsigned w) (Z.of_nat (length ub) + 3) ->
  bv_unsigned w + Z.of_nat (length ub) + 3 + Z.of_nat (length ns) <= lo ->
  bv_unsigned txt + Z.of_nat (length tb + 1 + length ts) <= lo \/ bv_unsigned sp <= bv_unsigned txt ->
  bv_unsigned uri + Z.of_nat (length ub + 1 + length us) <= lo \/ bv_unsigned sp <= bv_unsigned uri ->
  bv_unsigned uri + Z.of_nat (length ub + 1 + length us) <= bv_unsigned w \/
    bv_unsigned w + Z.of_nat (length ub) + 3 <= bv_unsigned uri ->
  bv_unsigned txt + Z.of_nat (length tb + 1 + length ts) <= bv_unsigned w \/
    bv_unsigned w + Z.of_nat (length ub) + 3 <= bv_unsigned txt ->
  0 < bv_unsigned uri -> 0 < bv_unsigned txt ->
  bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) -> bytes_at rsegs m GUARD (le8 canary) ->
  evt rsegs
    (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32)
                       (m' : word -> option byte),
       ms' = MS (mkR (Z_to_bv 64 0x13cd4) (Z_to_bv 64 (bv_unsigned sp - 176)) gp tp t0' t1' t2' rp uri w
                     a1' a2' a3' a4' a5' a6' a7' txt un w (rd_found txt tb ub) x22 x23 x24 x25 x26 x27 t3' t4' t5' t6')
                F' (Z_to_bv 64 0x13b54) fc' None m' (seg_rom rsegs) /\
       munch [(lo, bv_unsigned sp - 176); (bv_unsigned w, bv_unsigned w + Z.of_nat (length ub) + 3)] m m' /\
       wmono rsegs m m' /\ mem_inv rsegs m' /\ frm0 fc' /\ stk rsegs m' lo (bv_unsigned sp - 176) /\
       rw_cells rsegs m' (bv_unsigned sp - 176) (rd_cells ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 junk))
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp - 176)) gp tp t0 t1 t2 rp uri w a1 a2 a3 a4 a5 a6 a7
             txt un x20 (Z_to_bv 64 (Z.of_nat (length ub) + 3)) x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13c9c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc x1 t0 t1 t2 rp uri w a1 a2 a3 a4 a5 a6 a7
    txt un x20 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 canary m lo junk wj ns tb ts ub us
    SNP STRS HS HS63 FR ST LO IL MI TM FRM CT CU UNE UL FMT WB WS WA W0 WI WL TO UO UW TW U0 T0 GG GD.
  destruct CT as [TB [TNZ TAL]]. destruct CU as [UB [UNZ UAL]].
  pose proof (bv_unsigned_in_range 64 w) as Rw. unfold bv_modulus in Rw.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  unfold SNPRINTF_K, IMG_END, RO_LO in *.
  zstep.
  if_cases HC; [exfalso; zify_cond HC; lia|].
  do 7 zstep.
  assert (SPU : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 176)) = bv_unsigned sp - 176) by (apply unsigned_lit; lia).
  assert (NU : bv_unsigned (Z_to_bv 64 (Z.of_nat (length ub) + 3)) = Z.of_nat (length ub) + 3)
    by (apply unsigned_lit; lia).
  set (T := 60 :: zbytes ub ++ [62]).
  assert (LT : length T = (length ub + 2)%nat) by (unfold T, zbytes; cbn [length]; rewrite length_app, length_map; cbn [length]; lia).
  assert (TFW : firstn (Z.to_nat (Z.of_nat (length ub) + 3 - 1)) T = T) by (apply firstn_all2; lia).
  assert (MT : map (Z_to_bv 8) T = Z_to_bv 8 60 :: ub ++ [Z_to_bv 8 62]).
  { unfold T. cbn [map]. rewrite map_app, z8_zbytes. reflexivity. }
  assert (RT : Forall (fun c => 0 <= c < 256) T).
  { unfold T. constructor; [lia|]. apply Forall_app. split; [apply zbytes_range | constructor; [lia | constructor]]. }
  eapply evt_cut.
  { eapply SNP with (lo := lo) (canary := canary) (fmt := ManifestB.fmt_whole) (ps := [PLit 60; Ps; PLit 62])
      (args := [APtr (zbytes ub)]) (T := T) (junk := wj); cbv zeta; rewrite ?SPU, ?NU.
    - rewrite unsigned_lit by lia. exact FMT.
    - rewrite unsigned_lit by lia. unfold RO_LO. lia.
    - rewrite unsigned_lit by lia. unfold RO_END. cbn. lia.
    - reflexivity.
    - cbn [pf_args_ok]. split; [|exact I]. cbn [pf_arg_ok]. split; [apply zbytes_nz; exact UNZ|].
      exists us. unfold pf_bytes. rewrite map_app, z8_zbytes. cbn [map].
      unfold zbytes. rewrite length_map. rewrite <- app_assoc. cbn [app].
      split; [exact UB|]. split; [exact UAL|]. split; [exact U0|].
      split; [lia | lia].
    - reflexivity.
    - replace (Z.to_nat (Z.of_nat (length ub) + 3)) with (length ub + 3)%nat by lia. exact WB.
    - lia.
    - rewrite LT. lia.
    - lia.
    - left. lia.
    - exact WI.
    - exact ST.
    - unfold SNPRINTF_K. lia.
    - unfold IMG_END. lia.
    - lia.
    - exact FRM.
    - exact MI.
    - exact TM.
    - exact GG.
    - exact GD. }
  intros ms' PO. unfold printf_post in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & Ft & fc' & m2 &
    E & MU2 & WM2 & MI2 & TM2 & FRM2 & FEQ & ST2 & BW).
  subst ms'. rewrite NU, TFW, LT in *.
  replace (ret_pc (Z_to_bv 64 81084)) with (Z_to_bv 64 81084) by (apply bv_eq; vm_compute; reflexivity).
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp - 176) (rd_cells ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 junk)).
  { eapply rw_cells_transport; [exact FR | exact MU2 | exact WM2 | unfold rd_cells; cbn; lia]. }
  assert (TB2 : bytes_at rsegs m2 (bv_unsigned txt) (tb ++ Z_to_bv 8 0 :: ts)).
  { eapply bytes_at_transport; [exact TB | exact MU2 | rewrite length_app; cbn [length disjoint_from]; lia]. }
  assert (WS2 : bytes_at rsegs m2 (bv_unsigned w + Z.of_nat (length ub) + 3) ns).
  { eapply bytes_at_transport; [exact WS | exact MU2 | cbn [disjoint_from]; lia]. }
  assert (GG2 : bytes_at rsegs m2 0x1e0b8 (le8 (Z_to_bv 64 0x4f6c8))).
  { unfold GOT_GUARD, GUARD in GG. pose proof (img_free_disj _ _ 0x1e0b8 8 WI ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    eapply bytes_at_transport; [exact GG | exact MU2 | rewrite length_le8; cbn [disjoint_from]; lia]. }
  assert (GD2 : bytes_at rsegs m2 0x4f6c8 (le8 canary)).
  { unfold GUARD in GD. pose proof (img_free_disj _ _ 0x4f6c8 8 WI ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    eapply bytes_at_transport; [exact GD | exact MU2 | rewrite length_le8; cbn [disjoint_from]; lia]. }
  clear FR TB WS ST UB MI WB GG GD FMT.
  do 3 zstep.
  assert (NB : bytes_at rsegs m2 (bv_unsigned w) (map (Z_to_bv 8) T ++ Z_to_bv 8 0 :: ns)).
  { replace (map (Z_to_bv 8) T ++ Z_to_bv 8 0 :: ns) with (pf_bytes (T ++ [0]) ++ ns)
      by (unfold pf_bytes; rewrite map_app, <- app_assoc; reflexivity).
    apply bytes_at_app. split; [exact BW|].
    unfold pf_bytes. rewrite length_map, length_app, LT. cbn [length].
    replace (bv_unsigned w + Z.of_nat (length ub + 2 + 1)) with (bv_unsigned w + Z.of_nat (length ub) + 3) by lia.
    exact WS2. }
  assert (NZB : Forall (fun b => bv_unsigned b <> 0) (map (Z_to_bv 8) T)).
  { rewrite MT. constructor; [apply (proj1 (Z.eqb_neq _ _)); vm_compute; reflexivity|].
    apply Forall_app. split; [exact UNZ | constructor; [apply (proj1 (Z.eqb_neq _ _)); vm_compute; reflexivity | constructor]]. }
  eapply evt_cut.
  { eapply STRS with (hb := tb) (hs := ts) (nb := map (Z_to_bv 8) T) (ns := ns) (lo := lo); rewrite ?SPU.
    - split; [exact TB2 | split; assumption].
    - split; [exact NB|]. split; [exact NZB|]. rewrite length_map, LT.
      replace (bv_unsigned w + Z.of_nat (length ub + 2) + 1) with (bv_unsigned w + Z.of_nat (length ub) + 3) by lia.
      exact WA.
    - rewrite MT. discriminate.
    - lia.
    - exact GG2.
    - exists canary. exact GD2.
    - unfold STRSTR_K. lia.
    - unfold STRSTR_K. lia.
    - exact MI2.
    - rewrite SPU in ST2. exact ST2.
    - unfold STRSTR_K. lia.
    - unfold off_stack, STRSTR_K. rewrite SPU. lia.
    - unfold off_stack, STRSTR_K. rewrite SPU, length_map, LT. lia. }
  intros ms' PO. unfold kret in PO. rewrite SPU in PO.
  destruct PO as (t0'' & t1'' & t2'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' &
    m3 & E & MU3 & WM3 & MI3 & ST3 & R3).
  unfold zbytes at 2 in R3. rewrite (zbytes_z8 T RT) in R3.
  subst ms' a0''.
  replace (ret_pc (Z_to_bv 64 81096)) with (Z_to_bv 64 81096) by (apply bv_eq; vm_compute; reflexivity).
  assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp - 176) (rd_cells ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 junk)).
  { eapply rw_cells_transport; [exact FR2 | exact MU3 | exact WM3 | unfold rd_cells, STRSTR_K; cbn; lia]. }
  do 3 zstep.
  apply evt_done. do 17 eexists. split.
  { unfold rd_found. fold T. reflexivity. }
  split.
  { eapply munch_trans; [eapply munch_weaken; [|exact MU2] | eapply munch_weaken; [|exact MU3]];
      intros x Hx; cbn in *; unfold STRSTR_K in *; lia. }
  split; [exact (wmono_trans rsegs _ _ _ WM2 WM3)|].
  split; [exact MI3|]. split; [exact FRM2|]. split; [exact ST3 | exact FR3].
Qed.

Lemma rd_hit : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
    (m : word -> option byte) (lo : Z) (junk : list byte),
  176 <= bv_unsigned sp -> bv_unsigned x21 <> 0 ->
  rw_cells rsegs m (bv_unsigned sp - 176) (rd_cells ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 junk) ->
  stk rsegs m lo (bv_unsigned sp - 176) -> lo <= bv_unsigned sp - 176 ->
  evt rsegs
    (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (ret_pc ra) fc None m (seg_rom rsegs) /\ stk rsegs m lo (bv_unsigned sp))
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp - 176)) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13cd4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
    x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 m lo junk HS NZ FR ST HLO.
  zstep.
  if_cases HC; [exfalso; zify_cond HC; lia|].
  do 2 zstep.
  eapply evt_cut; [eapply rd_epi with (lo := lo); [exact HS | exact FR | exact ST | exact HLO] |].
  intros ms' H. apply evt_done. exact H.
Qed.

Lemma rd_miss : forall (P : machine_state -> Prop) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (x1 x2 x3 x4 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word),
  bv_unsigned x21 = 0 ->
  evt rsegs P (MS (mkR x1 x2 x3 x4 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13ce0) fc None m (seg_rom rsegs)) ->
  evt rsegs P (MS (mkR x1 x2 x3 x4 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13cd4) fc None m (seg_rom rsegs)).
Proof.
  intros P F fc m x1 x2 x3 x4 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 H0 HE.
  zstep.
  if_cases HC; [exact HE|]. exfalso. zify_cond HC. lia.
Qed.

Fixpoint ftri (l : list (Z * Z * bool)) (a n : Z) : option bool :=
  match l with
  | [] => None
  | (b, s, w) :: r => if (b <=? a) && (a + n <=? b + s) then Some w else ftri r a n
  end.

Lemma ftri_spec : forall segs a n,
  option_map seg_writable (find_segment segs a n) =
  ftri (map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_writable s)) segs) a n.
Proof.
  induction segs as [|s segs IH]; intros a n; [reflexivity|].
  cbn [find_segment map ftri]. destruct ((Z.of_N (seg_base s) <=? a) && (a + n <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)));
    [reflexivity | apply IH].
Qed.

Lemma rsegs_tri : map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_writable s)) rsegs =
  [(65536, 8192, false); (73728, 49152, false); (122880, 4096, true); (126976, 200704, true)].
Proof. vm_compute. reflexivity. Qed.

Lemma ro_addr_spec : forall a, 0 <= a < 2 ^ 64 -> (ro_addr rsegs (Z_to_bv 64 a) = true <-> 65536 <= a < 122880).
Proof.
  intros a Ha. unfold ro_addr. rewrite unsigned_lit by lia.
  assert (E : match find_segment rsegs a 1 with Some seg => negb (seg_writable seg) | None => false end =
              match option_map seg_writable (find_segment rsegs a 1) with Some w => negb w | None => false end)
    by (destruct (find_segment rsegs a 1); reflexivity).
  rewrite E, ftri_spec, rsegs_tri. cbn [ftri].
  destruct (Z.leb_spec 65536 a); destruct (Z.leb_spec (a + 1) (65536 + 8192));
  destruct (Z.leb_spec 73728 a); destruct (Z.leb_spec (a + 1) (73728 + 49152));
  destruct (Z.leb_spec 122880 a); destruct (Z.leb_spec (a + 1) (122880 + 4096));
  destruct (Z.leb_spec 126976 a); destruct (Z.leb_spec (a + 1) (126976 + 200704));
  cbn [andb negb]; split; intros HH; try discriminate; try reflexivity; lia.
Qed.

Lemma ro_slack : forall a j, 0 <= a < 2 ^ 64 -> ro_addr rsegs (Z_to_bv 64 a) = true -> a <= j < 8 * ((a + 8) / 8) ->
  ro_addr rsegs (Z_to_bv 64 j) = true.
Proof.
  intros a j Ha H Hj. apply ro_addr_spec in H; [|exact Ha].
  apply ro_addr_spec; Z.div_mod_to_equations; lia.
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import Regs6ss.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import Ledger ManifestB names_c readings_c KindB.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import fuzz_malloc_c fuzz_free_c names has_prefixed_model.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require strlen_c LibcAdapt readings_scan_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YN03.
Local Open Scope Z_scope.

Lemma bytes_keep : forall m m' a bs, bytes_at rsegs m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> mbyte rsegs m' (a + i) = mbyte rsegs m (a + i)) ->
  bytes_at rsegs m' a bs.
Proof.
  intros m m' a bs (Ha & Hl & Hb) H. split; [lia|]. split; [lia|]. intros i Hi.
  rewrite <- (Hb i Hi). exact (H (Z.of_nat i) ltac:(lia)).
Qed.

Lemma present_bytes : forall m a (k : nat), 0 <= a -> a + Z.of_nat k <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat k -> exists b, m (Z_to_bv 64 (a + i)) = Some b) ->
  exists bs, length bs = k /\ bytes_at rsegs m a bs.
Proof.
  intros m a k Ha Hk H.
  assert (G : forall j, (j <= k)%nat -> exists bs, length bs = j /\
                forall i, (i < j)%nat -> mrd rsegs m (wa (a + Z.of_nat i)) = nth_error bs i).
  { induction j as [|j IH]; intros Hj.
    - exists []. split; [reflexivity|]. intros i Hi; lia.
    - destruct (IH ltac:(lia)) as (bs & Hlen & Hbs).
      destruct (H (Z.of_nat j) ltac:(lia)) as (b & Hb).
      exists (bs ++ [b]). split; [rewrite length_app; cbn; lia|].
      intros i Hi. destruct (Nat.eqb_spec i j).
      + subst i. rewrite nth_error_app2 by lia. rewrite Hlen, Nat.sub_diag. cbn. unfold mrd, wa. rewrite Hb. reflexivity.
      + rewrite nth_error_app1 by lia. apply Hbs. lia. }
  destruct (G k ltac:(lia)) as (bs & Hlen & Hbs). exists bs. split; [exact Hlen|].
  split; [lia|]. split; [lia|]. intros i Hi. apply Hbs. lia.
Qed.

Lemma pw_app : forall {T} (R : T -> T -> Prop) l1 l2, pairwise R (l1 ++ l2) ->
  (forall x y, In x l1 -> In y l2 -> R x y) /\ pairwise R l2.
Proof.
  intros T R l1 l2. induction l1 as [|z l1 IH]; intros H; cbn in H.
  - split; [intros x y [] | exact H].
  - destruct H as [H1 H2]. destruct (IH H2) as [IH1 IH2]. split; [|exact IH2].
    intros x y [<-|Hx] Hy; [apply H1; apply in_or_app; right; exact Hy | exact (IH1 x y Hx Hy)].
Qed.

Lemma pw_in : forall (l : list (Z * Z)) x y, pairwise ranges_disjoint l -> In x l -> In y l -> x <> y ->
  ranges_disjoint x y.
Proof.
  induction l as [|z l IH]; intros x y H Hx Hy Hn; [destruct Hx|].
  destruct H as [H1 H2]. destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy].
  - contradiction.
  - apply H1. exact Hy.
  - pose proof (H1 x Hx) as D. unfold ranges_disjoint in *. lia.
  - exact (IH x y H2 Hx Hy Hn).
Qed.

Lemma rd_notin : forall (b1 b2 : list (Z * Z)) x, pairwise ranges_disjoint (b1 ++ x :: b2) -> 0 < snd x ->
  ~ In x (b1 ++ b2).
Proof.
  intros b1 b2 x H Hp Hin. destruct (pw_app _ _ _ H) as [H1 H2].
  apply in_app_or in Hin as [Hin|Hin].
  - pose proof (H1 x x Hin (or_introl eq_refl)) as D. unfold ranges_disjoint in D. lia.
  - destruct H2 as [H3 _]. pose proof (H3 x Hin) as D. unfold ranges_disjoint in D. lia.
Qed.

Lemma rd_split_eq : forall (b1 b2 c1 c2 : list (Z * Z)) x, ~ In x (b1 ++ b2) ->
  b1 ++ x :: b2 = c1 ++ x :: c2 -> b1 ++ b2 = c1 ++ c2.
Proof.
  induction b1 as [|y b1 IH]; intros b2 c1 c2 x Hn E; destruct c1 as [|z c1]; cbn in *.
  - injection E as E. exact E.
  - injection E as Exz E. subst z. exfalso. apply Hn. rewrite E. apply in_or_app. right. left. reflexivity.
  - injection E as Eyx E. subst y. exfalso. apply Hn. left. reflexivity.
  - injection E as Eyz E. subst z. f_equal. apply (IH b2 c1 c2 x); [intros H; apply Hn; right; exact H | exact E].
Qed.

Lemma rd_lam_eq : forall (Lam l1 l2 : list (Z * Z)) x, NoDup (map fst (x :: Lam)) -> x :: Lam = l1 ++ x :: l2 ->
  l1 ++ l2 = Lam.
Proof.
  intros Lam l1 l2 x ND E. destruct l1 as [|y l1]; cbn in E.
  - injection E as E. exact (eq_sym E).
  - injection E as Exy E. subst y. exfalso. cbn [map] in ND. inversion ND as [|? ? Hn _]. apply Hn.
    apply list_elem_of_In. rewrite E, map_app. apply in_or_app. right. left. reflexivity.
Qed.

Lemma rd_whole_find : forall t u, find_sub t (60 :: u ++ [62]) = None <-> whole t u = false.
Proof.
  intros t u. set (nd := 60 :: u ++ [62]).
  assert (LN : length nd = (length u + 2)%nat) by (unfold nd; cbn [length]; rewrite length_app; cbn; lia).
  assert (EQ : forall k, mt t nd k = true <-> whole_at t u k = true /\ (k <= length t)%nat).
  { intros k. unfold mt, whole_at. rewrite LN. split.
    - intros H. apply andb_true_iff in H as [H1 H2]. apply Nat.leb_le in H1. split; [exact H2 | lia].
    - intros [H1 H2]. apply andb_true_iff. split; [|exact H1]. apply Nat.leb_le.
      apply zl_eqb_eq in H1. apply (f_equal (@length Z)) in H1. rewrite length_firstn, length_skipn in H1.
      fold nd in H1. rewrite LN in H1. lia. }
  split.
  - intros H. pose proof (find_sub_none _ _ H) as N. unfold whole.
    apply not_true_iff_false. intros Hx. apply existsb_exists in Hx as (k & Hk & Hw). rewrite in_seq in Hk.
    assert (Kt : (k <= length t)%nat) by (destruct Hk as [_ Hk]; cbn in Hk; lia).
    specialize (N k). rewrite (proj2 (EQ k) (conj Hw Kt)) in N. discriminate.
  - intros H. destruct (find_sub t nd) as [k|] eqn:E; [|reflexivity]. exfalso.
    destruct (find_sub_some _ _ _ E) as [Hm _]. apply EQ in Hm as [Hw Hk].
    unfold whole in H. apply not_true_iff_false in H. apply H. apply existsb_exists. exists k.
    split; [apply in_seq; lia | exact Hw].
Qed.

Lemma rd_vm_compose : forall v1 v2 md, with_vmmaps v2 (with_vmmaps v1 md) = with_vmmaps v2 md.
Proof. reflexivity. Qed.

Lemma rd_vm_self : forall md, md = with_vmmaps (m_vmmaps md) md.
Proof. intros [fd [mp lz mt0] io fs pr lim tm]. reflexivity. Qed.

Lemma rd_ftri_img : forall x, ftri [(65536, 8192, false); (73728, 49152, false); (122880, 4096, true); (126976, 200704, true)] x 1 <> None ->
  0x10000 <= x < 0x50000.
Proof.
  intros x H. cbn [ftri] in H.
  destruct (Z.leb_spec 65536 x); destruct (Z.leb_spec (x + 1) (65536 + 8192));
  destruct (Z.leb_spec 73728 x); destruct (Z.leb_spec (x + 1) (73728 + 49152));
  destruct (Z.leb_spec 122880 x); destruct (Z.leb_spec (x + 1) (122880 + 4096));
  destruct (Z.leb_spec 126976 x); destruct (Z.leb_spec (x + 1) (126976 + 200704));
  cbn [andb] in H; first [lia | exfalso; apply H; reflexivity].
Qed.

Section RB.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.
Hypothesis SEG : ms_segs B = rsegs.

Lemma rd_img_all : forall x, 0x10000 <= x < 0x50000 -> in_img B x.
Proof.
  intros x Hx.
  destruct (Z_lt_le_dec x 0x12000);
    [apply (YN03.covered_sound B 0x10000 0x2000); [unfold YN03.covered; rewrite SEG; vm_compute; reflexivity | lia]|].
  destruct (Z_lt_le_dec x 0x1e000);
    [apply (YN03.covered_sound B 0x12000 0xc000); [unfold YN03.covered; rewrite SEG; vm_compute; reflexivity | lia]|].
  destruct (Z_lt_le_dec x 0x1f000);
    [apply (YN03.covered_sound B 0x1e000 0x1000); [unfold YN03.covered; rewrite SEG; vm_compute; reflexivity | lia]|].
  apply (YN03.covered_sound B 0x1f000 0x31000); [unfold YN03.covered; rewrite SEG; vm_compute; reflexivity | lia].
Qed.

Lemma rd_wr_present : forall m x, 0 <= x < 2 ^ 64 -> ~ in_img B x -> writable_at (ms_segs B) m x -> present m x.
Proof.
  intros m x Hx Hi Hw. unfold writable_at, wview in Hw.
  destruct (m (Z_to_bv 64 x)) as [b|] eqn:E; [exists b; exact E|].
  rewrite unsigned_lit in Hw by lia. rewrite SEG in Hw.
  destruct (find_segment rsegs x 1) as [seg|] eqn:F; [|contradiction].
  exfalso. apply Hi. apply rd_img_all. apply rd_ftri_img.
  rewrite <- rsegs_tri, <- ftri_spec, F. discriminate.
Qed.

Lemma rd_guard_wr : forall mem x, (0x1e0b8 <= x < 0x1e0c0 \/ 0x4f6c8 <= x < 0x4f6d0) ->
  writable_at (ms_segs B) mem x.
Proof.
  intros mem x [Hx|Hx].
  - refine (proj1 (YN03.rw_check_sound B 8 0x1e0b8 _ _ _ mem x _));
      [unfold YN03.rw_check; rewrite SEG; vm_compute; reflexivity | lia | lia | cbn; lia].
  - refine (proj1 (YN03.rw_check_sound B 8 0x4f6c8 _ _ _ mem x _));
      [unfold YN03.rw_check; rewrite SEG; vm_compute; reflexivity | lia | lia | cbn; lia].
Qed.

Hypothesis AX : AllocExtra B MR.
Hypothesis GS : guard_syms B.

Lemma rd_guards : forall L A m md, MR L A m md ->
  exists canary, rw_cells rsegs m GOT_GUARD [C8 (Z_to_bv 64 GUARD)] /\ rw_cells rsegs m GUARD [C8 canary].
Proof.
  intros L A m md HM. destruct (ax_statics AX L A m md HM) as (W1 & (g & Hg & W2) & _).
  destruct GS as [G1 G2]. rewrite G1, G2 in W1. rewrite G2 in W2. rewrite SEG in W1, W2.
  exists (Z_to_bv 64 g). unfold GOT_GUARD, GUARD.
  split; (split; [split; [exact (conj I I) | cbn [cells_bytes cbytes]; rewrite app_nil_r] |]).
  - apply word_mem_bytes; [lia | lia | lia | exact W1].
  - cbn [cells_size csize]. split; [lia|]. split; [lia|]. intros i Hi.
    pose proof (rd_guard_wr m (0x1e0b8 + i) ltac:(lia)) as Wr. rewrite SEG in Wr. exact Wr.
  - apply word_mem_bytes; [lia | lia | lia | exact W2].
  - cbn [cells_size csize]. split; [lia|]. split; [lia|]. intros i Hi.
    pose proof (rd_guard_wr m (0x4f6c8 + i) ltac:(lia)) as Wr. rewrite SEG in Wr. exact Wr.
Qed.

End RB.

Lemma rw_cells_norm : forall m A cs, ro_agree rsegs m -> rw_cells rsegs m A cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> ro_addr rsegs (wa (A + i)) = false) ->
  rw_cells rsegs (normalize rsegs m) A cs.
Proof.
  intros m A cs Hro [[Hw Hb] Hwr] Hf. split; [split; [exact Hw | apply bytes_at_normalize; assumption] |].
  apply (wr_at_norm rsegs m (normalize rsegs m)); [apply mem_rel_normalize; exact Hro | exact Hwr | exact Hf].
Qed.

Lemma rw_cells_back : forall m m0 A cs, mem_rel rsegs m m0 -> rw_cells rsegs m0 A cs -> rw_cells rsegs m A cs.
Proof.
  intros m m0 A cs HR [[Hw Hb] Hwr]. split; [split; [exact Hw | exact (proj2 (bytes_at_rel rsegs m m0 A _ HR) Hb)] |].
  exact (wr_at_rel rsegs m m0 A _ HR Hwr).
Qed.

Lemma stk_norm : forall m lo hi, ro_agree rsegs m -> stk rsegs m lo hi ->
  (forall a, lo <= a < hi -> ro_addr rsegs (wa a) = false) -> stk rsegs (normalize rsegs m) lo hi.
Proof.
  intros m lo hi Hro (H1 & H2 & H) Hf. split; [lia|]. split; [lia|]. intros a Ha. destruct (H a Ha) as [Hw (b & Hb)].
  pose proof (mem_rel_normalize rsegs m Hro) as HR. split.
  - rewrite (wview_rel_rw rsegs m (normalize rsegs m) (wa a) HR (Hf a Ha)). exact Hw.
  - exists b. rewrite <- (mrd_rel rsegs m (normalize rsegs m) (wa a) HR). exact Hb.
Qed.

Lemma stk_back : forall m m0 lo hi, mem_rel rsegs m m0 -> stk rsegs m0 lo hi -> stk rsegs m lo hi.
Proof.
  intros m m0 lo hi HR (H1 & H2 & H). split; [lia|]. split; [lia|]. intros a Ha. destruct (H a Ha) as [Hw (b & Hb)].
  split.
  - rewrite <- (wview_rel_rw rsegs m m0 (wa a) HR (ro_false_of_wview rsegs m m0 (wa a) HR Hw)). exact Hw.
  - exists b. rewrite (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma cstr_norm : forall m s tb ts, ro_agree rsegs m -> cstr_at m s tb ts -> cstr_at (normalize rsegs m) s tb ts.
Proof. intros m s tb ts Hro (Hb & Hn & Ha). split; [apply bytes_at_normalize; assumption | split; assumption]. Qed.

Lemma ms_rel_MS : forall s R F pc fc rv m0 ro, ms_rel rsegs s (MS R F pc fc rv m0 ro) ->
  s = MS R F pc fc rv (ms_mem s) ro /\ mem_rel rsegs (ms_mem s) m0.
Proof.
  intros [R' F' pc' svc' rv' fc' m' ro'] R F pc fc rv m0 ro (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  cbn in *. subst. split; [reflexivity | exact H8].
Qed.

Lemma ro_false_hi : forall x, 0x50000 <= x < 2 ^ 64 -> ro_addr rsegs (wa x) = false.
Proof.
  intros x Hx. destruct (ro_addr rsegs (wa x)) eqn:E; [|reflexivity].
  pose proof (ro_low (wa x) E) as Lw. rewrite wa_unsigned in Lw by lia. lia.
Qed.

Lemma rd_rp_final : forall regs R' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
  xregs_eqv (mkR (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) t0 t1 t2
     (reg_get regs 8) (reg_get regs 9) a0 a1 a2 a3 a4 a5 a6 a7 (reg_get regs 18) (reg_get regs 19)
     (reg_get regs 20) (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24)
     (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) t3 t4 t5 t6) R' ->
  regs_preserved regs R'.
Proof.
  intros regs R' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 XR r Hr. rewrite <- (getr_eqv _ _ XR (Z_to_bv 5 r)).
  unfold callee_saved in Hr.
  assert (HC : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
               r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct HC as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]];
    reflexivity.
Qed.

Section Q.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.
Hypothesis SEG : ms_segs B = rsegs.
Hypothesis SF : statics_free B MR.
Hypothesis SFA : statics_facts B.
Hypothesis CTX : ManifestB.ctx_owned B MR.
Hypothesis AX : AllocExtra B MR.
Hypothesis BSP : block_slack_present B API.

Lemma rd_not_owned_mid : forall L A m md L1 A1 m1 md1 a, MR L A m md -> MR L1 A1 m1 md1 ->
  (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ owned B L A a -> ~ owned B L1 A1 a.
Proof.
  intros L A m md L1 A1 m1 md1 a HM HM1 Hr Hn Ho. destruct Hr as [Hr|Hr].
  - pose proof (mr_owned_low _ _ (aa_laws API) L1 A1 m1 md1 a HM1 Ho). lia.
  - destruct Ho as [Ho|Ho].
    + exact (Hn (CTX L A m md a HM (ax_img AX L1 A1 m1 md1 a HM1 Hr Ho))).
    + exact (Hn (or_intror Ho)).
Qed.

Lemma rd_block_facts : forall L A m md a k i, MR L A m md -> In (a, k) (blocks L A) -> 0 <= i < k ->
  present m (a + i) /\ 4096 <= a /\ a + k <= alloc_ceiling /\ ~ owned B L A (a + i) /\ ~ in_img B (a + i).
Proof.
  intros L A m md a k i HM Hin Hi. destruct (in_blocks L A a k Hin) as (p & Hp & ->).
  destruct (mr_blocks _ _ (aa_laws API) L A m md p k i HM Hp Hi) as (P & H1 & H2 & H3).
  split; [exact P|]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  exact (ax_blocks_img AX L A m md p k i HM Hp Hi).
Qed.

Lemma rd_pw : forall L A m md, MR L A m md -> pairwise ranges_disjoint (blocks L A).
Proof. intros L A m md HM. exact (mr_blocks_disjoint _ _ (aa_laws API) L A m md HM). Qed.

Lemma rd_newblock_disj : forall (b1 b2 : list (Z * Z)) x a k, pairwise ranges_disjoint (b1 ++ x :: b2) ->
  0 < snd x -> In (a, k) (b1 ++ b2) -> ranges_disjoint (a, k) x.
Proof.
  intros b1 b2 x a k Hp Hx Hin.
  assert (Nx : (a, k) <> x) by (intros E; subst x; exact (rd_notin b1 b2 (a, k) Hp Hx Hin)).
  apply (pw_in (b1 ++ x :: b2)); [exact Hp | | apply in_or_app; right; left; reflexivity | exact Nx].
  apply in_app_or in Hin as [H|H]; apply in_or_app; [left; exact H | right; right; exact H].
Qed.

Lemma rd_MR_write : forall L A m md m' lo hi w n,
  MR L A m md -> In (w - 16, n + 16) (blocks L A) -> 0 <= n -> alloc_ceiling <= lo ->
  munch [(lo, hi); (w, w + n)] m m' -> wmono (ms_segs B) m m' -> MR L A m' md.
Proof.
  intros L A m md m' lo hi w n HM Hin Hn Hlo MU WM.
  pose proof alloc_ceiling_val as Hacv. pose proof alloc_ceiling_lt as Hlt.
  destruct (mr_model _ _ (aa_laws API) L A m md HM) as (Hh & Hl & Hm).
  pose proof (rd_block_facts L A m md (w - 16) (n + 16) 0 HM Hin ltac:(lia)) as (_ & W1 & W2 & _ & _).
  assert (OW : forall a, owned B L A a -> 0 <= a < alloc_ceiling /\ outside [(lo, hi); (w, w + n)] a).
  { intros a Ho. pose proof (mr_owned_low _ _ (aa_laws API) L A m md a HM Ho) as Ha. split; [exact Ha|].
    cbn. split; [lia|]. split; [|exact I]. intros Hb.
    pose proof (rd_block_facts L A m md (w - 16) (n + 16) (a - (w - 16)) HM Hin ltac:(lia)) as (_ & _ & _ & No & _).
    apply No. replace (w - 16 + (a - (w - 16))) with a by lia. exact Ho. }
  eapply (mr_frame _ _ (aa_laws API) L A m m' md md HM).
  - intros a Ho. destruct (OW a Ho) as [Ha Hout]. apply (KindB.mbyte_munch _ [(lo, hi); (w, w + n)] m m'); [exact MU | lia | exact Hout].
  - intros a Ho Hp. destruct (OW a Ho) as [Ha Hout]. apply (present_munch [(lo, hi); (w, w + n)] m m'); [exact MU | lia | exact Hout | exact Hp].
  - intros p k i Hp Hi.
    destruct (mr_blocks _ _ (aa_laws API) L A m md p k i HM Hp Hi) as (P & H1 & H2 & H3).
    destruct (outside_dec [(lo, hi); (w, w + n)] (ptr_addr L p + i)) as [Hout|Hin2].
    + apply (present_munch [(lo, hi); (w, w + n)] m m'); [exact MU | lia | exact Hout | exact P].
    + assert (Hb : w <= ptr_addr L p + i < w + n).
      { destruct (Z_lt_le_dec (ptr_addr L p + i) w) as [Q1|Q1];
          [exfalso; apply Hin2; cbn [outside]; split; [lia | split; [lia | exact I]]|].
        destruct (Z_lt_le_dec (ptr_addr L p + i) (w + n)) as [Q2|Q2]; [lia|].
        exfalso; apply Hin2; cbn [outside]; split; [lia | split; [lia | exact I]]. }
      apply (rd_wr_present B SEG m' (ptr_addr L p + i)); [lia | |].
      * pose proof (rd_block_facts L A m md (w - 16) (n + 16) (ptr_addr L p + i - (w - 16)) HM Hin ltac:(lia))
          as (_ & _ & _ & _ & Ni).
        replace (w - 16 + (ptr_addr L p + i - (w - 16))) with (ptr_addr L p + i) in Ni by lia. exact Ni.
      * apply WM. apply (present_writable B). exact P.
  - reflexivity.
  - exact Hh.
  - exact Hl.
  - exact Hm.
Qed.

Lemma rd_ledger_write : forall L A m md m' lo hi w n Lam peak cnt fail,
  MR L A m md -> ledger B L A m ((w, n) :: Lam) peak cnt fail -> In (w - 16, n + 16) (blocks L A) -> 0 <= n ->
  alloc_ceiling <= lo -> munch [(lo, hi); (w, w + n)] m m' -> ledger B L A m' ((w, n) :: Lam) peak cnt fail.
Proof.
  intros L A m md m' lo hi w n Lam peak cnt fail HM (AW & R1 & R2 & R3 & ND & FB) Hin Hn Hlo MU.
  pose proof alloc_ceiling_val as Hacv. pose proof alloc_ceiling_lt as Hlt.
  pose proof (rd_block_facts L A m md (w - 16) (n + 16) 0 HM Hin ltac:(lia)) as (_ & W1 & W2 & _ & _).
  assert (NB : forall x, in_img B x -> ~ (w <= x < w + n)).
  { intros x Hx Hb. pose proof (rd_block_facts L A m md (w - 16) (n + 16) (x - (w - 16)) HM Hin ltac:(lia))
      as (_ & _ & _ & _ & Ni). apply Ni. replace (w - 16 + (x - (w - 16))) with x by lia. exact Hx. }
  assert (ST : forall a, alloc_statics a -> outside [(lo, hi); (w, w + n)] a /\ 0 <= a < 0x50000).
  { intros a Ha. pose proof (proj1 (SFA a Ha)) as Hi. pose proof (in_img_low B SEG a Hi) as Hlow.
    unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Ha.
    split; [cbn; split; [lia|]; split; [exact (NB a Hi) | exact I] | lia]. }
  destruct AW as (A1 & A2 & A3 & A4).
  split.
  { unfold alloc_words, G_LIVE, G_PEAK, G_COUNT, G_FAIL in *.
    split; [|split; [|split]]; (eapply word_mem_munch; [exact MU | lia | lia | | eassumption]);
      intros x Hx; apply (ST x); unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL; lia. }
  split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact ND|].
  eapply Forall_impl; [|exact FB]. intros [a k] (Hk & Hin2 & Hw & Hi). cbn [fst snd] in *.
  split; [exact Hk|]. split; [exact Hin2|]. split; [|exact Hi].
  pose proof (rd_block_facts L A m md (a - 16) (k + 16) 0 HM Hin2 ltac:(lia)) as (_ & B1 & B2 & _ & _).
  assert (D : a = w \/ a - 16 + (k + 16) <= w - 16 \/ w - 16 + (n + 16) <= a - 16).
  { destruct (Z.eq_dec a w) as [E|E]; [left; exact E|right].
    pose proof (rd_pw L A m md HM) as PW.
    assert (Nxy : (a - 16, k + 16) <> (w - 16, n + 16)) by (intros Hxy; injection Hxy; lia).
    pose proof (pw_in _ _ _ PW Hin2 Hin Nxy) as Dj. unfold ranges_disjoint in Dj. cbn [fst snd] in Dj. lia. }
  eapply word_mem_munch; [exact MU | lia | lia | | exact Hw].
  intros x Hx. cbn. split; [lia|]. split; [lia | exact I].
Qed.


Lemma rd_inner : forall L A regs1 m1 md L1 A1 regs2 m2 md1 m3 regs3 L4 A4 regs4 m4 md2 w n b1 b2 c1 c2,
  MR L A m1 md ->
  alloc_ceiling + (ALLOC_STACK + 32) <= spZ regs1 -> spZ regs1 < 2 ^ 63 -> spZ regs3 = spZ regs1 ->
  call_post_k B MR (ALLOC_STACK + 32) L A regs1 m1 md (alloc_writes w) L1 A1 regs2 m2 md1 ->
  keeps B L A m1 m2 0 -> guard_kept B m1 m2 ->
  0 <= n -> (forall i, 0 <= i < n + 16 -> ~ in_img B (w - 16 + i)) ->
  blocks L1 A1 = b1 ++ (w - 16, n + 16) :: b2 -> blocks L A = b1 ++ b2 ->
  munch [(spZ regs1 - (ALLOC_STACK + 32), spZ regs1); (w, w + n)] m2 m3 -> wmono (ms_segs B) m2 m3 ->
  MR L1 A1 m3 md1 ->
  call_post_k B MR ALLOC_STACK L1 A1 regs3 m3 md1 (free_writes w n) L4 A4 regs4 m4 md2 ->
  keeps B L1 A1 m3 m4 (w - 16) -> guard_kept B m3 m4 ->
  blocks L1 A1 = c1 ++ (w - 16, n + 16) :: c2 -> blocks L4 A4 = c1 ++ c2 ->
  ro_agree (ms_segs B) m4 ->
  bpost B MR (ALLOC_STACK + 32) stat_writes L A regs1 m1 md L4 A4 regs1 m4 md2.
Proof.
  intros L A regs1 m1 md L1 A1 regs2 m2 md1 m3 regs3 L4 A4 regs4 m4 md2 w n b1 b2 c1 c2
    HM Hac H63 Hsp3 CP1 KP1 GK1 Hn NI E1 E2 MU WM HM3 CP2 KP2 GK2 F1 F2 RA4.
  pose proof alloc_ceiling_val as Hacv. pose proof alloc_ceiling_lt as Hlt.
  destruct CP1 as (HM2 & HWF2 & HBD2 & _ & _ & _ & (v1 & Hmd1) & Hfr1 & _ & Hsc1).
  destruct CP2 as (HM4 & HWF4 & HBD4 & _ & _ & _ & (v2 & Hmd2) & Hfr2 & _ & Hsc2).
  set (x := (w - 16, n + 16)) in *.
  pose proof (rd_pw L1 A1 m2 md1 HM2) as PW. rewrite E1 in PW.
  assert (NIN : ~ In x (b1 ++ b2)) by (apply (rd_notin b1 b2 x PW); unfold x; cbn; lia).
  assert (INX : In x (blocks L1 A1)) by (rewrite E1; apply in_or_app; right; left; reflexivity).
  assert (INL : forall y, In y (blocks L A) -> In y (blocks L1 A1)).
  { intros y Hy. rewrite E2 in Hy. rewrite E1. apply in_app_or in Hy as [H|H]; apply in_or_app; [left; exact H | right; right; exact H]. }
  pose proof (rd_block_facts L1 A1 m2 md1 (w - 16) (n + 16) 0 HM2 INX ltac:(lia)) as (_ & W1 & W2 & _ & _).
  assert (DJ : forall a k, In (a, k) (blocks L A) -> a + k <= w - 16 \/ w + n <= a).
  { intros a k Hin. rewrite E2 in Hin. pose proof (rd_newblock_disj b1 b2 x a k PW ltac:(unfold x; cbn; lia) Hin) as D.
    unfold ranges_disjoint, x in D. cbn [fst snd] in D. lia. }
  assert (NB : forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ (w - 16 <= a < w + n)).
  { intros a [Hr|Hr] Hb; [lia|]. apply (NI (a - (w - 16))); [lia|]. replace (w - 16 + (a - (w - 16))) with a by lia. exact Hr. }
  assert (SW : forall a, stat_writes a -> 0 <= a < alloc_ceiling).
  { intros a Ha. unfold stat_writes, G_LIVE, G_COUNT, G_FAIL in Ha. lia. }
  assert (WN : forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ stat_writes a -> ~ alloc_writes w a).
  { intros a Hr Hs [Ha|[_ Ha]]; [apply Hs; unfold stat_writes, alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in *; lia|].
    exact (NB a Hr ltac:(lia)). }
  split; [exact HM4|]. split; [exact HWF4|]. split; [exact HBD4|].
  split; [intros r _; reflexivity|].
  split; [exists v2; rewrite Hmd2, Hmd1; reflexivity|].
  split; [rewrite F2, E2; symmetry; apply (rd_split_eq b1 b2 c1 c2 x NIN); rewrite <- E1, <- F1; reflexivity|].
  split.
  { intros a k i Hin Hi.
    pose proof (rd_block_facts L A m1 md a k i HM Hin Hi) as (_ & B1 & B2 & _ & _).
    pose proof (DJ a k Hin) as D.
    rewrite (KP2 a k i (INL _ Hin) ltac:(lia) Hi).
    rewrite (KindB.mbyte_munch _ [(spZ regs1 - (ALLOC_STACK + 32), spZ regs1); (w, w + n)] m2 m3 (a + i) MU ltac:(lia)).
    - exact (KP1 a k i Hin ltac:(lia) Hi).
    - cbn [outside]. unfold ALLOC_STACK in *. split; [lia|]. split; [lia | exact I]. }
  split.
  { intros a Hr HnA HnA' Hsc0 HnE.
    assert (Ha64 : 0 <= a < 2 ^ 64) by (destruct Hr as [Hr|Hr]; [lia | pose proof (in_img_low B SEG a Hr); lia]).
    pose proof (rd_not_owned_mid L A m1 md L1 A1 m2 md1 a HM HM2 Hr HnA) as Hn1.
    assert (O3 : outside [(spZ regs1 - (ALLOC_STACK + 32), spZ regs1); (w, w + n)] a).
    { cbn [outside]. split; [intros Hs; apply Hsc0; left; exact Hs|]. split; [|exact I].
      intros Hb. exact (NB a Hr ltac:(lia)). }
    assert (HnS3 : ~ scratch_k B ALLOC_STACK regs3 a).
    { intros [Hs|Hs]; apply Hsc0; [left; unfold spZ in *; rewrite Hsp3 in Hs; unfold ALLOC_STACK in *; lia | right; exact Hs]. }
    assert (HnW3 : ~ free_writes w n a).
    { intros [Hs|[_ Hb]]; [apply HnE; unfold stat_writes, G_LIVE, G_COUNT, G_FAIL in *; lia | exact (NB a Hr Hb)]. }
    destruct (Hfr1 a Hr HnA Hn1 Hsc0 (WN a Hr HnE)) as [Hm1 Hw1].
    destruct (Hfr2 a Hr Hn1 HnA' HnS3 HnW3) as [Hm3 Hw3].
    split.
    - rewrite Hm3, (KindB.mbyte_munch _ _ m2 m3 a MU Ha64 O3), Hm1. reflexivity.
    - rewrite Hw1, (KindB.writable_munch _ _ m2 m3 a MU Ha64 O3). exact Hw3. }
  split.
  { intros a Hs.
    assert (D : scratch_k B ALLOC_STACK regs3 a \/ ~ scratch_k B ALLOC_STACK regs3 a).
    { unfold scratch_k. destruct (Z.le_gt_cases (spZ regs3 - ALLOC_STACK) a); destruct (Z.lt_ge_cases a (spZ regs3));
        destruct (Z.le_gt_cases (errno_addr B) a); destruct (Z.lt_ge_cases a (errno_addr B + 4));
        first [left; lia | right; lia]. }
    destruct D as [Hs3|Hs3]; [exact (Hsc2 a Hs3)|].
    assert (Hr : spZ regs1 - (ALLOC_STACK + 32) <= a < spZ regs1).
    { destruct Hs as [Hs|Hs]; [exact Hs | exfalso; apply Hs3; right; exact Hs]. }
    assert (Hw3 : writable_at (ms_segs B) m3 a) by (apply WM; apply Hsc1; exact Hs).
    assert (Hn1 : ~ owned B L1 A1 a) by (intros Ho; pose proof (mr_owned_low _ _ (aa_laws API) L1 A1 m2 md1 a HM2 Ho); lia).
    assert (Hn4 : ~ owned B L4 A4 a) by (intros Ho; pose proof (mr_owned_low _ _ (aa_laws API) L4 A4 m4 md2 a HM4 Ho); lia).
    assert (HnW : ~ free_writes w n a) by (intros [Hf|[_ Hf]]; unfold G_LIVE in *; lia).
    destruct (Hfr2 a ltac:(left; lia) Hn1 Hn4 Hs3 HnW) as [_ Hw4]. apply Hw4. exact Hw3. }
  split; [exact RA4|].
  intros i Hi. rewrite (GK2 i Hi).
  pose proof (guard_low B API L1 A1 m2 md1 HM2) as GL.
  assert (Own : owned B L1 A1 (ms_got_guard B + i)) by (right; unfold static_owned; do 4 right; left; lia).
  assert (GO : 0 <= ms_got_guard B + i < 2 ^ 64 /\ outside [(spZ regs1 - (ALLOC_STACK + 32), spZ regs1); (w, w + n)] (ms_got_guard B + i)).
  { split; [lia|]. cbn [outside]. unfold ALLOC_STACK in *. split; [lia|]. split; [|exact I]. intros Hb.
    pose proof (rd_block_facts L1 A1 m2 md1 (w - 16) (n + 16) (ms_got_guard B + i - (w - 16)) HM2 INX ltac:(lia))
      as (_ & _ & _ & No & _).
    apply No. replace (w - 16 + (ms_got_guard B + i - (w - 16))) with (ms_got_guard B + i) by lia. exact Own. }
  rewrite (KindB.mbyte_munch _ _ m2 m3 _ MU (proj1 GO) (proj2 GO)). exact (GK1 i Hi).
Qed.


Lemma rd_fail_inner : forall L A regs1 m1 md L1 A1 regs2 m2 md1,
  MR L A m1 md ->
  call_post_k B MR (ALLOC_STACK + 32) L A regs1 m1 md (alloc_writes 0) L1 A1 regs2 m2 md1 ->
  keeps B L A m1 m2 0 -> guard_kept B m1 m2 -> blocks L1 A1 = blocks L A -> ro_agree (ms_segs B) m2 ->
  bpost B MR (ALLOC_STACK + 32) stat_writes L A regs1 m1 md L1 A1 regs1 m2 md1.
Proof.
  intros L A regs1 m1 md L1 A1 regs2 m2 md1 HM CP KP GK Hbl RA.
  destruct CP as (HM2 & HWF2 & HBD2 & _ & _ & _ & Hmd & Hfr & _ & Hsc).
  split; [exact HM2|]. split; [exact HWF2|]. split; [exact HBD2|].
  split; [intros r _; reflexivity|]. split; [exact Hmd|]. split; [exact Hbl|].
  split.
  { intros a k i Hin Hi. pose proof (rd_block_facts L A m1 md a k i HM Hin Hi) as (_ & B1 & _ & _ & _).
    exact (KP a k i Hin ltac:(lia) Hi). }
  split.
  { intros a Hr HnA HnA' Hsc0 HnE. apply (Hfr a Hr HnA HnA' Hsc0).
    intros [Ha|[Ha _]]; [apply HnE; unfold stat_writes, alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in *; lia | lia]. }
  split; [exact Hsc|]. split; [exact RA | exact GK].
Qed.

Lemma rd_bpost_weak : forall K E E' L A regs mem md L' A' regs' mem' md', (forall a, E a -> E' a) ->
  bpost B MR K E L A regs mem md L' A' regs' mem' md' -> bpost B MR K E' L A regs mem md L' A' regs' mem' md'.
Proof.
  intros K E E' L A regs mem md L' A' regs' mem' md' HE (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split; [exact H6|]. split; [exact H7|].
  split; [intros a Hr Hn Hn' Hs He; exact (H8 a Hr Hn Hn' Hs (fun e => He (HE a e)))|].
  split; [exact H9 | exact H10].
Qed.

Lemma rd_bpost_ext : forall K E L A regs mem md L' A' regs' mem' md' W mem'',
  bpost B MR K E L A regs mem md L' A' regs' mem' md' ->
  munch W mem' mem'' -> wmono (ms_segs B) mem' mem'' -> ro_agree (ms_segs B) mem'' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ outside W x -> alloc_ceiling <= x /\ (scratch_k B K regs x \/ E x)) ->
  bpost B MR K E L A regs mem md L' A' regs' mem'' md'.
Proof.
  intros K E L A regs mem md L' A' regs' mem' md' W mem'' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & _ & H10)
    MU WM RA HW.
  pose proof alloc_ceiling_val as Hacv. pose proof alloc_ceiling_lt as Hlt.
  assert (LOW : forall x, 0 <= x < alloc_ceiling -> outside W x).
  { intros x Hx. destruct (outside_dec W x) as [O|O]; [exact O|]. pose proof (HW x ltac:(lia) O). lia. }
  split; [apply (MR_high B API L' A' mem' mem'' md' W H1 MU LOW)|].
  split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [exact H6|].
  split.
  { intros a k i Hin Hi. rewrite <- H6 in Hin.
    pose proof (rd_block_facts L' A' mem' md' a k i H1 Hin Hi) as (_ & B1 & B2 & _ & _). rewrite H6 in Hin.
    rewrite (KindB.mbyte_munch _ W mem' mem'' (a + i) MU ltac:(lia) (LOW (a + i) ltac:(lia))). exact (H7 a k i Hin Hi). }
  split.
  { intros a Hr Hn Hn' Hs He.
    assert (Ha64 : 0 <= a < 2 ^ 64) by (destruct Hr as [Hr|Hr]; [lia | pose proof (in_img_low B SEG a Hr); lia]).
    assert (O : outside W a).
    { destruct (outside_dec W a) as [O|O]; [exact O|]. exfalso. destruct (HW a Ha64 O) as [_ [Q|Q]]; auto. }
    destruct (H8 a Hr Hn Hn' Hs He) as [Hm Hw]. split.
    - rewrite (KindB.mbyte_munch _ W mem' mem'' a MU Ha64 O). exact Hm.
    - rewrite Hw. exact (KindB.writable_munch _ W mem' mem'' a MU Ha64 O). }
  split; [intros a Hs; apply WM; exact (H9 a Hs)|].
  split; [exact RA|].
  intros i Hi. pose proof (guard_low B API L' A' mem' md' H1) as GL.
  rewrite (KindB.mbyte_munch _ W mem' mem'' (ms_got_guard B + i) MU ltac:(lia) (LOW (ms_got_guard B + i) ltac:(lia))). exact (H10 i Hi).
Qed.

Lemma rd_bpost_kindA : forall K E L A regs mem md regs' mem' W,
  MR L A mem md -> WF A -> bounded A -> regs_preserved regs regs' ->
  munch W mem mem' -> wmono (ms_segs B) mem mem' -> ro_agree (ms_segs B) mem' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ outside W x -> alloc_ceiling <= x /\ (scratch_k B K regs x \/ E x)) ->
  (forall a, scratch_k B K regs a -> writable_at (ms_segs B) mem' a) ->
  bpost B MR K E L A regs mem md L A regs' mem' md.
Proof.
  intros K E L A regs mem md regs' mem' W HM HWF HBD RP MU WM RA HW HS.
  pose proof alloc_ceiling_val as Hacv. pose proof alloc_ceiling_lt as Hlt.
  assert (LOW : forall x, 0 <= x < alloc_ceiling -> outside W x).
  { intros x Hx. destruct (outside_dec W x) as [O|O]; [exact O|]. pose proof (HW x ltac:(lia) O). lia. }
  split; [apply (MR_high B API L A mem mem' md W HM MU LOW)|].
  split; [exact HWF|]. split; [exact HBD|]. split; [exact RP|].
  split; [exists (m_vmmaps md); apply rd_vm_self|]. split; [reflexivity|].
  split.
  { intros a k i Hin Hi. pose proof (rd_block_facts L A mem md a k i HM Hin Hi) as (_ & B1 & B2 & _ & _).
    exact (KindB.mbyte_munch _ W mem mem' (a + i) MU ltac:(lia) (LOW (a + i) ltac:(lia))). }
  split.
  { intros a Hr Hn Hn' Hs He.
    assert (Ha64 : 0 <= a < 2 ^ 64) by (destruct Hr as [Hr|Hr]; [lia | pose proof (in_img_low B SEG a Hr); lia]).
    assert (O : outside W a).
    { destruct (outside_dec W a) as [O|O]; [exact O|]. exfalso. destruct (HW a Ha64 O) as [_ [Q|Q]]; auto. }
    split; [exact (KindB.mbyte_munch _ W mem mem' a MU Ha64 O) | exact (KindB.writable_munch _ W mem mem' a MU Ha64 O)]. }
  split; [exact HS|]. split; [exact RA|].
  intros i Hi. pose proof (guard_low B API L A mem md HM) as GL.
  exact (KindB.mbyte_munch _ W mem mem' (ms_got_guard B + i) MU ltac:(lia) (LOW (ms_got_guard B + i) ltac:(lia))).
Qed.

Lemma rd_cstr_keep : forall L A mem L' A' m' md' s tb ts,
  ro_agree rsegs mem -> ro_agree rsegs m' -> MR L' A' m' md' ->
  cstr_at mem s tb ts -> Z.of_nat (length ts) = (- (s + Z.of_nat (length tb) + 1)) mod 8 ->
  str_home L A s (Z.of_nat (length tb + 1)) ->
  (forall y, In y (blocks L A) -> In y (blocks L' A')) ->
  (forall a k i, In (a, k) (blocks L A) -> 0 <= i < k -> mbyte rsegs m' (a + i) = mbyte rsegs mem (a + i)) ->
  exists ts', length ts' = length ts /\ cstr_at m' s tb ts'.
Proof.
  intros L A mem L' A' m' md' s tb ts RA RA' HM' (Hb & Hn & Ha) Hr Hh INL KP.
  pose proof (bytes_at_bound _ _ _ _ Hb) as BB. rewrite length_app in BB. cbn [length] in BB.
  set (e := s + Z.of_nat (length tb) + 1) in *.
  assert (Er : e + Z.of_nat (length ts) = 8 * ((e + 7) / 8)) by (rewrite Hr; Z.div_mod_to_equations; lia).
  destruct Hh as [(a & k & Hin & Ha1 & Ha2) | Hro].
  - assert (Kk : 0 < k) by lia.
    assert (PR : forall i, 0 <= i < Z.of_nat (length ts) -> exists b, m' (Z_to_bv 64 (e + i)) = Some b).
    { intros i Hi. destruct (Z_lt_le_dec (e + i) (a + k)) as [Q|Q].
      - pose proof (rd_block_facts L' A' m' md' a k (e + i - a) HM' (INL _ Hin) ltac:(lia)) as (P & _).
        replace (a + (e + i - a)) with (e + i) in P by lia. exact P.
      - apply (BSP L' A' m' md' a k (e + i) HM' (INL _ Hin)).
        assert (8 * ((e + 7) / 8) <= 8 * ((a + k + 7) / 8)) by (apply Z.mul_le_mono_nonneg_l; [lia | apply Z.div_le_mono; lia]).
        lia. }
    destruct (present_bytes m' e (length ts) ltac:(lia) ltac:(lia) PR) as (ts' & Hl & Hb').
    exists ts'. split; [exact Hl|].
    split; [|split; [exact Hn | rewrite Hl; lia]].
    replace (tb ++ Z_to_bv 8 0 :: ts') with ((tb ++ [Z_to_bv 8 0]) ++ ts') by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app. split.
    + apply (bytes_keep mem m' s); [|].
      * replace (tb ++ Z_to_bv 8 0 :: ts) with ((tb ++ [Z_to_bv 8 0]) ++ ts) in Hb by (rewrite <- app_assoc; reflexivity).
        exact (proj1 (proj1 (bytes_at_app rsegs mem s _ _) Hb)).
      * intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
        replace (s + i) with (a + (s - a + i)) by lia. apply (KP a k); [exact Hin | lia].
    + rewrite length_app. cbn [length]. replace (s + Z.of_nat (length tb + 1)) with e by lia. exact Hb'.
  - exists ts. split; [reflexivity|]. split; [|split; [exact Hn | exact Ha]].
    apply (bytes_ro mem m' s _ RA RA'); [|exact Hb].
    intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    destruct (Nat.lt_ge_cases i (length tb + 1)) as [Q|Q].
    + exact (Hro (Z.of_nat i) ltac:(lia)).
    + pose proof (Hro (Z.of_nat (length tb)) ltac:(lia)) as R0.
      apply (ro_slack (s + Z.of_nat (length tb))); [lia | exact R0 | lia].
Qed.

Lemma rd_str_vs_block : forall L A L1 A1 m1 md1 s (tb : list byte) r w n b1 b2,
  MR L1 A1 m1 md1 -> str_home L A s (Z.of_nat (length tb + 1)) -> 0 <= s -> s + Z.of_nat (length tb) + 1 <= 2 ^ 64 ->
  r = (- (s + Z.of_nat (length tb) + 1)) mod 8 ->
  blocks L1 A1 = b1 ++ (w - 16, n + 16) :: b2 -> blocks L A = b1 ++ b2 -> 0 <= n -> w mod 16 = 0 ->
  s + Z.of_nat (length tb) + 1 + r <= w - 16 \/ w + n <= s.
Proof.
  intros L A L1 A1 m1 md1 s tb r w n b1 b2 HM1 Hh Hs0 Hs1 Hr E1 E2 Hn Hw.
  set (e := s + Z.of_nat (length tb) + 1) in *.
  assert (Er : e + r = 8 * ((e + 7) / 8)) by (rewrite Hr; Z.div_mod_to_equations; lia).
  assert (INX : In (w - 16, n + 16) (blocks L1 A1)) by (rewrite E1; apply in_or_app; right; left; reflexivity).
  destruct Hh as [(a & k & Hin & Ha1 & Ha2) | Hro].
  - pose proof (rd_pw L1 A1 m1 md1 HM1) as PW. rewrite E1 in PW. rewrite E2 in Hin.
    pose proof (rd_newblock_disj b1 b2 (w - 16, n + 16) a k PW ltac:(cbn; lia) Hin) as D.
    unfold ranges_disjoint in D. cbn [fst snd] in D.
    destruct D as [D|D]; [left | right; lia].
    assert (8 * ((e + 7) / 8) <= w - 16) by (Z.div_mod_to_equations; lia). lia.
  - pose proof (Hro (Z.of_nat (length tb)) ltac:(lia)) as R0.
    apply (proj1 (ro_addr_spec (s + Z.of_nat (length tb)) ltac:(lia))) in R0.
    pose proof (Hro 0 ltac:(lia)) as R1. apply (proj1 (ro_addr_spec (s + 0) ltac:(lia))) in R1.
    pose proof (rd_block_facts L1 A1 m1 md1 (w - 16) (n + 16) 0 HM1 INX ltac:(lia)) as (_ & W1 & W2 & _ & N0).
    destruct (Z_lt_le_dec (w - 16) 0x10000) as [Q|Q].
    + right. destruct (Z_le_gt_dec (w + n) 0x10000) as [Q2|Q2]; [lia|]. exfalso.
      pose proof (rd_block_facts L1 A1 m1 md1 (w - 16) (n + 16) (0x10000 - (w - 16)) HM1 INX ltac:(lia)) as (_ & _ & _ & _ & N1).
      apply N1. replace (w - 16 + (0x10000 - (w - 16))) with 0x10000 by lia. apply (rd_img_all B SEG). lia.
    + left. destruct (Z_lt_le_dec (w - 16) 0x50000) as [Q2|Q2].
      * exfalso. apply N0. replace (w - 16 + 0) with (w - 16) by lia. apply (rd_img_all B SEG). lia.
      * assert (8 * ((e + 7) / 8) <= 122880) by (Z.div_mod_to_equations; lia). lia.
Qed.

End Q.

Lemma rd_back : forall m mc m0' W, ro_agree rsegs m -> mem_rel rsegs mc m0' -> ro_same rsegs m mc ->
  munch W (normalize rsegs m) m0' -> wmono rsegs (normalize rsegs m) m0' ->
  munch W m mc /\ wmono rsegs m mc /\ ro_agree rsegs mc.
Proof.
  intros m mc m0' W RA HR ROS MU WM. pose proof (mem_rel_normalize rsegs m RA) as HR0.
  split; [exact (munch_rel rsegs W m (normalize rsegs m) mc m0' HR0 HR ROS MU)|].
  split; [exact (wmono_rel rsegs m (normalize rsegs m) mc m0' HR0 HR ROS WM)|].
  exact (ro_agree_of_mem_rel rsegs mc m0' HR).
Qed.

Lemma rd_same : forall m mc, ro_agree rsegs m -> mem_rel rsegs mc (normalize rsegs m) -> ro_same rsegs m mc ->
  munch [] m mc /\ wmono rsegs m mc /\ ro_agree rsegs mc.
Proof.
  intros m mc RA HR ROS. pose proof (mem_rel_normalize rsegs m RA) as HR0.
  pose proof (mem_unchanged_rel rsegs m (normalize rsegs m) mc (normalize rsegs m) HR0 HR ROS (fun x => eq_refl)) as EQ.
  split; [intros x _; exact (EQ x)|]. split; [intros x Hx; unfold wview; rewrite (EQ x); exact Hx|].
  exact (ro_agree_of_mem_rel rsegs mc _ HR).
Qed.

Section Q2.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.
Hypothesis SEG : ms_segs B = rsegs.
Hypothesis ERR : errno_low B.

Lemma rd_bpost_word : forall K L A regs mem md L' A' regs' mem' md' p bs,
  bpost B MR K stat_writes L A regs mem md L' A' regs' mem' md' -> MR L A mem md ->
  alloc_ceiling <= p -> p + 8 <= 2 ^ 64 -> spZ regs <= p -> length bs = 8%nat ->
  bytes_at rsegs mem p bs -> wr_at rsegs mem p 8 -> bytes_at rsegs mem' p bs /\ wr_at rsegs mem' p 8.
Proof.
  intros K L A regs mem md L' A' regs' mem' md' p bs BP HM Hp Hp8 Hsp Hl Hb Hw.
  pose proof alloc_ceiling_val as Hacv. pose proof alloc_ceiling_lt as Hlt.
  destruct BP as (HM' & _ & _ & _ & _ & _ & _ & Hfr & _).
  assert (FR : forall x, p <= x < p + 8 ->
            mbyte (ms_segs B) mem' x = mbyte (ms_segs B) mem x /\
            (writable_at (ms_segs B) mem x <-> writable_at (ms_segs B) mem' x)).
  { intros x Hx. apply Hfr; [left; lia | | | |].
    - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) L A mem md x HM Ho). lia.
    - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) L' A' mem' md' x HM' Ho). lia.
    - unfold scratch_k, errno_low in *. lia.
    - unfold stat_writes, G_LIVE, G_COUNT, G_FAIL. lia. }
  split.
  - apply (bytes_keep mem mem' p bs Hb). intros i Hi. rewrite Hl in Hi. rewrite <- SEG. apply FR. lia.
  - destruct Hw as (W1 & W2 & W3). split; [lia|]. split; [lia|]. intros i Hi.
    pose proof (proj1 (proj2 (FR (p + i) ltac:(lia))) ltac:(unfold writable_at; rewrite SEG; exact (W3 i Hi))) as W.
    unfold writable_at in W. rewrite SEG in W. exact W.
Qed.

End Q2.

From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require readings_scan has_prefixed_c.

Ltac rfeed H :=
  repeat match type of H with
  | ?P -> _ => match type of P with Prop => match goal with Hp : _ |- _ => specialize (H Hp) end end
  end.

Ltac rgp kZ RP XR :=
  match goal with |- reg_get ?R' _ = ?v =>
    change (getr R' (Z_to_bv 5 kZ) = v); rewrite (RP kZ ltac:(unfold callee_saved; lia));
    rewrite <- (getr_eqv _ _ XR); reflexivity
  end.

Lemma munch_eq2 : forall a b c d a' b' c' d' m m', munch [(a, b); (c, d)] m m' -> a = a' -> b = b' -> c = c' -> d = d' ->
  munch [(a', b'); (c', d')] m m'.
Proof. intros; subst; assumption. Qed.

Lemma rw_cells_norm_cj : forall m A cs, ro_agree rsegs m -> rw_cells rsegs m A cs ->
  A + Z.of_nat (cells_size cs) <= TASK_SIZE ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> ro_addr rsegs (wa (A + i)) = false) ->
  rw_cells rsegs (normalize_cj rsegs m) A cs.
Proof.
  intros m A cs Hro [[Hw Hb] Hwr] Ht Hf. split.
  - split; [exact Hw|]. apply bytes_at_normalize_cj_low; [exact Hro | rewrite cells_bytes_length by exact Hw; exact Ht | exact Hb].
  - apply (wr_at_norm_cj rsegs m (normalize_cj rsegs m)); [apply mem_rel_cj_normalize; exact Hro | exact Hwr |].
    intros i Hi. apply cj_drop_false_intro; [exact (Hf i Hi) | right].
    destruct Hwr as (W1 & W2 & _). rewrite wa_unsigned by lia. lia.
Qed.

Lemma rw_cells_back_cj : forall m m0 A cs, mem_rel_cj rsegs m m0 -> rw_cells rsegs m0 A cs -> rw_cells rsegs m A cs.
Proof.
  intros m m0 A cs HR [[Hw Hb] Hwr]. split; [split; [exact Hw | exact (bytes_at_rel_cj rsegs m m0 A _ HR Hb)] |].
  exact (wr_at_rel_cj rsegs m m0 A _ HR Hwr).
Qed.

Lemma stk_norm_cj : forall m lo hi, ro_agree rsegs m -> stk rsegs m lo hi -> hi <= TASK_SIZE ->
  (forall a, lo <= a < hi -> ro_addr rsegs (wa a) = false) -> stk rsegs (normalize_cj rsegs m) lo hi.
Proof.
  intros m lo hi Hro (H1 & H2 & H) Ht Hf. split; [lia|]. split; [lia|]. intros a Ha. destruct (H a Ha) as [Hw (b & Hb)].
  assert (K : cj_drop rsegs (wa a) = false).
  { apply cj_drop_false_intro; [exact (Hf a Ha) | right]. rewrite wa_unsigned by lia. lia. }
  pose proof (mem_rel_cj_normalize rsegs m Hro) as HR. split.
  - rewrite (wview_rel_cj rsegs m (normalize_cj rsegs m) (wa a) HR K). exact Hw.
  - exists b. rewrite (mrd_normalize_cj rsegs m (wa a) Hro); [exact Hb |]. right. right. rewrite wa_unsigned by lia. lia.
Qed.

Lemma stk_back_cj : forall m m0 lo hi, mem_rel_cj rsegs m m0 -> stk rsegs m0 lo hi -> stk rsegs m lo hi.
Proof.
  intros m m0 lo hi HR (H1 & H2 & H). split; [lia|]. split; [lia|]. intros a Ha. destruct (H a Ha) as [Hw (b & Hb)].
  split.
  - rewrite <- (wview_rel_cj rsegs m m0 (wa a) HR (keep_of_wview_cj rsegs m m0 (wa a) HR Hw)). exact Hw.
  - exists b. exact (mrd_rel_cj rsegs m m0 (wa a) b HR Hb).
Qed.

Lemma cstr_norm_cj : forall m s tb ts, ro_agree rsegs m -> cstr_at m s tb ts ->
  s + Z.of_nat (length tb + 1 + length ts) <= TASK_SIZE -> cstr_at (normalize_cj rsegs m) s tb ts.
Proof.
  intros m s tb ts Hro (Hb & Hn & Ha) Ht. split; [|split; assumption].
  apply bytes_at_normalize_cj_low; [exact Hro | | exact Hb]. rewrite length_app. cbn [length]. lia.
Qed.

Lemma ms_rel_cj_MS : forall s R F pc fc rv m0 ro, ms_rel_cj rsegs s (MS R F pc fc rv m0 ro) ->
  s = MS R F pc fc rv (ms_mem s) ro /\ mem_rel_cj rsegs (ms_mem s) m0.
Proof.
  intros [R' F' pc' svc' rv' fc' m' ro'] R F pc fc rv m0 ro (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  cbn in *. subst. split; [reflexivity | exact H8].
Qed.

Lemma rd_back_cj : forall m mc m0' W, ro_agree rsegs m -> mem_rel_cj rsegs mc m0' -> cj_same rsegs m mc ->
  munch W (normalize_cj rsegs m) m0' -> wmono rsegs (normalize_cj rsegs m) m0' ->
  munch W m mc /\ wmono rsegs m mc /\ ro_agree rsegs mc.
Proof.
  intros m mc m0' W RA HR ROS MU WM. pose proof (mem_rel_cj_normalize rsegs m RA) as HR0.
  split; [exact (munch_rel_cj rsegs W m (normalize_cj rsegs m) mc m0' HR0 HR ROS MU)|].
  split; [exact (wmono_rel_cj rsegs m (normalize_cj rsegs m) mc m0' HR0 HR ROS WM)|].
  exact (ro_agree_same_cj rsegs m mc RA ROS).
Qed.

Lemma rd_find_sub_bound : forall h nd fuel i j, find_sub_from h nd i fuel = Some j -> (j + length nd <= length h)%nat.
Proof.
  intros h nd fuel. induction fuel as [|fuel IH]; intros i j H; cbn [find_sub_from] in H; [discriminate H|].
  match type of H with context [if ?c then _ else _] => destruct c eqn:E end.
  - injection H as <-. apply andb_true_iff in E as [E _]. apply Nat.leb_le in E. exact E.
  - exact (IH (S i) j H).
Qed.

Lemma rd_found_zero : forall (txt : word) tb ub, 0 < bv_unsigned txt -> bv_unsigned txt + Z.of_nat (length tb) < 2 ^ 64 ->
  (bv_unsigned (rd_found txt tb ub) = 0 <-> whole (ManifestMem.zbytes tb) (ManifestMem.zbytes ub) = false).
Proof.
  intros txt tb ub H0 H1. rewrite <- rd_whole_find. unfold rd_found.
  destruct (find_sub (ManifestMem.zbytes tb) (60 :: ManifestMem.zbytes ub ++ [62])) as [i|] eqn:E.
  - unfold find_sub in E. pose proof (rd_find_sub_bound _ _ _ _ _ E) as Hb.
    assert (Li : (i <= length tb)%nat).
    { unfold ManifestMem.zbytes in Hb. rewrite length_map in Hb. cbn [length] in Hb. lia. }
    rewrite unsigned_lit by lia. split; [intros Hc; lia | intros Hc; discriminate Hc].
  - rewrite unsigned_lit by lia. split; intros _; reflexivity.
Qed.

Lemma c8_bytes : forall m A x, rw_cells rsegs m A [C8 x] -> bytes_at rsegs m A (le8 x).
Proof. intros m A x [[_ H] _]. cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H. exact H. Qed.

Lemma rd_cells_size : forall ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 junk,
  cells_size (rd_cells ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 junk) = 176%nat.
Proof. reflexivity. Qed.

Lemma cstr_bound : forall m s tb ts, cstr_at m s tb ts -> 0 <= s /\ s + Z.of_nat (length tb + 1 + length ts) <= 2 ^ 64.
Proof.
  intros m s tb ts (Hb & _ & _). pose proof (bytes_at_bound _ _ _ _ Hb) as BB. rewrite length_app in BB.
  cbn [length] in BB. lia.
Qed.

Lemma not_outside1 : forall lo hi x, ~ outside [(lo, hi)] x -> lo <= x < hi.
Proof.
  intros lo hi x H. destruct (Z_le_dec lo x); destruct (Z_lt_dec x hi); try lia; exfalso; apply H;
    cbn [outside]; (split; [lia | exact I]).
Qed.

Lemma not_outside2 : forall l1 h1 l2 h2 x, ~ outside [(l1, h1); (l2, h2)] x -> l1 <= x < h1 \/ l2 <= x < h2.
Proof.
  intros l1 h1 l2 h2 x H. destruct (Z_le_dec l1 x); destruct (Z_lt_dec x h1); destruct (Z_le_dec l2 x);
    destruct (Z_lt_dec x h2); try lia; exfalso; apply H; cbn [outside]; (split; [lia | (split; [lia | exact I])]).
Qed.

Lemma wr_at_wmono : forall m m' a n, wr_at rsegs m a n -> wmono rsegs m m' -> wr_at rsegs m' a n.
Proof.
  intros m m' a n (W1 & W2 & W3) WM. split; [exact W1|]. split; [exact W2|]. intros i Hi. apply WM. exact (W3 i Hi).
Qed.

Section R.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEG : ms_segs B = rsegs.
Hypothesis SF : statics_free B (aa_MR API).
Hypothesis SFA : statics_facts B.
Hypothesis CTX : ManifestB.ctx_owned B (aa_MR API).
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis BSP : block_slack_present B API.
Hypothesis ERR : errno_low B.
Hypothesis GS : guard_syms B.

Lemma rd_str_low : forall L A m md s (tb sl : list byte), aa_MR API L A m md ->
  str_home L A s (Z.of_nat (length tb + 1)) -> 0 <= s -> s + Z.of_nat (length tb) + 1 <= 2 ^ 64 ->
  Z.of_nat (length sl) = (- (s + Z.of_nat (length tb) + 1)) mod 8 ->
  s + Z.of_nat (length tb + 1 + length sl) <= alloc_ceiling.
Proof.
  intros L A m md s tb sl HM Hh Hs0 Hs1 Hl.
  pose proof alloc_ceiling_val as Hacv. pose proof alloc_ceiling_value as [_ Hmod].
  pose proof (rd_block_facts B API) as RBF. rfeed RBF.
  assert (Er : s + Z.of_nat (length tb) + 1 + Z.of_nat (length sl) = 8 * ((s + Z.of_nat (length tb) + 1 + 7) / 8))
    by (rewrite Hl; Z.div_mod_to_equations; lia).
  destruct Hh as [(a & k & Hin & Ha1 & Ha2) | Hro].
  - pose proof (RBF L A m md a k 0 HM Hin ltac:(lia)) as (_ & _ & Hk & _).
    assert (8 * ((s + Z.of_nat (length tb) + 1 + 7) / 8) <= alloc_ceiling) by (Z.div_mod_to_equations; lia).
    lia.
  - pose proof (Hro (Z.of_nat (length tb)) ltac:(lia)) as R0.
    apply (proj1 (ro_addr_spec (s + Z.of_nat (length tb)) ltac:(lia))) in R0.
    assert (8 * ((s + Z.of_nat (length tb) + 1 + 7) / 8) <= 122880) by (Z.div_mod_to_equations; lia).
    lia.
Qed.

Lemma rd_cells_after : forall K L A regs mem md E L' A' regs' mem' md' X cs,
  aa_MR API L A mem md -> call_post_k B (aa_MR API) K L A regs mem md E L' A' regs' mem' md' ->
  rw_cells rsegs mem X cs -> alloc_ceiling <= X -> X + Z.of_nat (cells_size cs) <= 2 ^ 64 ->
  (forall a, X <= a < X + Z.of_nat (cells_size cs) -> ~ scratch_k B K regs a /\ ~ E a) ->
  rw_cells rsegs mem' X cs.
Proof.
  intros K L A regs mem md E L' A' regs' mem' md' X cs HM CP FR HX HX2 HN.
  destruct CP as (HM' & _ & _ & _ & _ & _ & _ & HFR & _).
  apply (rw_cells_keep mem mem' _ _ FR). intros a Ha. rewrite <- SEG. destruct (HN a Ha) as [N1 N2].
  apply HFR; [left; lia | | | exact N1 | exact N2].
  - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM Ho). lia.
  - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM' Ho). lia.
Qed.

Lemma rd_stk_after : forall K L A regs mem md E L' A' regs' mem' md' lo hi,
  aa_MR API L A mem md -> call_post_k B (aa_MR API) K L A regs mem md E L' A' regs' mem' md' ->
  alloc_ceiling <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> writable_at rsegs mem a) -> (forall a, lo <= a < hi -> ~ E a) ->
  stk rsegs mem' lo hi.
Proof.
  intros K L A regs mem md E L' A' regs' mem' md' lo hi HM CP Hlo Hhi HW HN.
  pose proof alloc_ceiling_val as Hacv.
  destruct CP as (HM' & _ & _ & _ & _ & _ & _ & HFR & _ & HSC).
  apply stk_of_writable; [lia | exact Hhi |]. intros a Ha. rewrite <- SEG.
  assert (D : scratch_k B K regs a \/ ~ scratch_k B K regs a) by (unfold scratch_k; lia).
  destruct D as [D|D]; [exact (HSC a D)|].
  assert (Na : ~ owned B L A a) by (intros Ho; pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM Ho); lia).
  assert (Na' : ~ owned B L' A' a) by (intros Ho; pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM' Ho); lia).
  assert (Ha1 : alloc_ceiling <= a < 2 ^ 64) by lia.
  destruct (HFR a (or_introl Ha1) Na Na' D (HN a Ha)) as [_ Hw]. apply Hw. rewrite SEG. exact (HW a Ha).
Qed.

Lemma rd_post_intro : forall L A regs mem md b (tb ts ub us : list byte) Lam peak cnt fail (v : word)
    (fx' : FPState) L' A' regs' mem' md' res c',
  aa_MR API L A mem md -> ro_agree rsegs mem ->
  cstr_at mem (bv_unsigned (reg_get regs 10)) tb ts -> cstr_at mem (bv_unsigned (reg_get regs 11)) ub us ->
  str_home L A (bv_unsigned (reg_get regs 10)) (Z.of_nat (length tb + 1)) ->
  str_home L A (bv_unsigned (reg_get regs 11)) (Z.of_nat (length ub + 1)) ->
  c' = mkCfg (@mkst fx' regs' (reg_get regs 1) mem' (seg_rom (ms_segs B))) md' ->
  frm_zero (@fp_csr fx') -> st_init_done A' = true ->
  bpost B (aa_MR API) READINGS_KB (rd_writes (bv_unsigned (reg_get regs 12))) L A regs mem md L' A' regs' mem' md' ->
  wr_at rsegs mem' (bv_unsigned (reg_get regs 12)) 8 ->
  getr regs' 10 = Z_to_bv 64 res ->
  ( (ub = [] /\ res = 0 /\ ledger B L' A' mem' Lam peak cnt fail /\
       bytes_at rsegs mem' (bv_unsigned (reg_get regs 12)) (le8 v))
    \/ (ub <> [] /\ cnt = fail /\ res = 0 /\
        ledger B L' A' mem' Lam peak ((cnt + 1) mod 2 ^ 64) (2 ^ 64 - 1) /\
        bytes_at rsegs mem' (bv_unsigned (reg_get regs 12)) (le8 v))
    \/ (ub <> [] /\ cnt <> fail /\ res = names (ManifestMem.zbytes tb) (ManifestMem.zbytes ub) /\
        ledger B L' A' mem' Lam (Z.max peak (lsum Lam + Z.of_nat (length ub) + 3)) ((cnt + 1) mod 2 ^ 64) fail /\
        bytes_at rsegs mem' (bv_unsigned (reg_get regs 12))
          (le8 (Z_to_bv 64 (bv_unsigned v + Z.of_nat (nreadings (ManifestMem.zbytes tb) (ManifestMem.zbytes ub))))))) ->
  res_ok_slots A' b ->
  readings_post B API L A regs mem md READINGS_KB tb ub Lam peak cnt fail v b c'.
Proof.
  intros L A regs mem md b tb ts ub us Lam peak cnt fail v fx' L' A' regs' mem' md' res c'
    HM RA CT CU HT HU Ec FRM INIT BP WR R10 ARMS SL.
  pose proof BP as (HM' & _ & _ & _ & _ & HBL & HBB & _ & _ & RA' & _).
  rewrite SEG in HBB, RA'.
  assert (INL : forall y, In y (blocks L A) -> In y (blocks L' A')) by (intros y Hy; rewrite HBL; exact Hy).
  pose proof (rd_cstr_keep B API) as CK. rfeed CK.
  destruct (cstr_trim _ _ _ _ CT) as (st & CT' & Lst).
  destruct (cstr_trim _ _ _ _ CU) as (su & CU' & Lsu).
  destruct (CK L A mem L' A' mem' md' _ tb st RA RA' HM' CT' Lst HT INL HBB) as (st' & _ & CT2).
  destruct (CK L A mem L' A' mem' md' _ ub su RA RA' HM' CU' Lsu HU INL HBB) as (su' & _ & CU2).
  unfold readings_post. exists fx', L', A', regs', mem', md', res.
  split; [exact Ec|]. split; [exact FRM|]. split; [exact INIT|]. split; [exact BP|]. split; [exact WR|].
  split; [exact R10|]. split; [exists st'; exact CT2|]. split; [exists su'; exact CU2|].
  split; [exact ARMS | exact SL].
Qed.

Lemma rd_sandwich : forall L A regs mem md m1 regs1 L' A' mem2 md' regs3,
  call_pre_k B (aa_MR API) READINGS_KB L A regs mem md ->
  spZ regs1 = spZ regs - 176 ->
  munch [(spZ regs - 176, spZ regs)] mem m1 -> wmono rsegs mem m1 ->
  bpost B (aa_MR API) (ALLOC_STACK + 32) stat_writes L A regs1 m1 md L' A' regs1 mem2 md' ->
  regs_preserved regs regs3 ->
  bpost B (aa_MR API) READINGS_KB stat_writes L A regs mem md L' A' regs3 mem2 md'.
Proof.
  intros L A regs mem md m1 regs1 L' A' mem2 md' regs3 PRE S1 MU1 WM1 BP RP.
  pose proof alloc_ceiling_val as Hacv.
  assert (KB : READINGS_KB = 8400) by reflexivity. assert (AS : ALLOC_STACK = 8192) by reflexivity.
  pose proof PRE as (HM & _ & _ & _ & _ & HAC & H63 & HWS & _).
  pose proof BP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & RA2 & _).
  pose proof (bpost_sandwich_s B API) as SW. rfeed SW.
  apply (SW READINGS_KB (ALLOC_STACK + 32) stat_writes L A regs mem md m1 regs1 L' A' regs1 mem2 md' mem2 regs3
    [(spZ regs - 176, spZ regs)] []).
  - exact HM.
  - exact HWS.
  - exact HAC.
  - exact H63.
  - intros a [Ha|Ha]; [left | right; exact Ha]. rewrite S1 in Ha. lia.
  - intros a Ha. unfold stat_writes, G_LIVE, G_COUNT, G_FAIL in Ha. lia.
  - intros a Ha. unfold alloc_statics, stat_writes, G_LIVE, G_PEAK, G_COUNT, G_FAIL in *. lia.
  - exact (in_img_low B SEG).
  - intros x Hx H1 H2. cbn [outside]. split; [lia | exact I].
  - intros x Hx H1 H2. exact I.
  - exact MU1.
  - rewrite SEG. exact WM1.
  - exact BP.
  - exact (munch_refl [] mem2).
  - exact (wmono_refl (ms_segs B) mem2).
  - exact GS.
  - exact RA2.
  - exact RP.
Qed.

Hypothesis STRLEN : LibcNeeds_c.strlen_contract.
Hypothesis SNP : snprintf_contract.
Hypothesis STRS : LibcNeeds_c.strstr_contract.
Hypothesis SCAN : readings_scan_c.readings_scan_contract.
Hypothesis MALLOC : forall fx' : FPState, @fuzz_malloc_contract fx' rc B API.
Hypothesis FREE : forall fx' : FPState, @fuzz_free_contract fx' rc B API.

Theorem rd_core : readings_contract B API.
Proof.
  unfold readings_contract.
  intros L A regs mem md b tb ts ub us Lam peak cnt fail v SEG' PRE INIT RPT FRM RA GC CT CU HT HU T4 U4 LT LU IMG
    OT OU RPB RPW SPRP DJ LED RES CAP BY0 BYT.
  clear SEG'.
  change (getr regs 1) with (reg_get regs 1) in *.
  change (getr regs 10) with (reg_get regs 10) in *.
  change (getr regs 11) with (reg_get regs 11) in *.
  change (getr regs 12) with (reg_get regs 12) in *.
  change (bv_unsigned (getr regs 2)) with (spZ regs) in *.
  unfold off_stack in OT, OU. change (bv_unsigned (getr regs 2)) with (spZ regs) in OT, OU.
  pose proof alloc_ceiling_val as Hacv. pose proof alloc_ceiling_lt as Hlt. pose proof alloc_ceiling_value as [_ Hmod].
  assert (KB : READINGS_KB = 8400) by reflexivity. assert (AS : ALLOC_STACK = 8192) by reflexivity.
  pose proof PRE as (HM & HWF & HBD & HRA & H16 & HAC & H63 & HWS & HTP & HER & _).
  change (getr regs 1) with (reg_get regs 1) in HRA.
  destruct (mr_model _ _ (aa_laws API) L A mem md HM) as (Hh & Hl & _).
  assert (SP : bv_unsigned (reg_get regs 2) = spZ regs) by reflexivity.
  pose proof RPW as (RP0 & RP8 & _).
  destruct (cstr_trim _ _ _ _ CT) as (st & CTt & Lst).
  destruct (cstr_trim _ _ _ _ CU) as (su & CUt & Lsu).
  destruct (cstr_bound _ _ _ _ CTt) as [Bt0 Bt1].
  destruct (cstr_bound _ _ _ _ CUt) as [Bu0 Bu1].
  pose proof (rd_str_low L A mem md _ tb st HM HT Bt0 ltac:(lia) Lst) as TLO.
  pose proof (rd_str_low L A mem md _ ub su HM HU Bu0 ltac:(lia) Lsu) as ULO.
  assert (STK : stk rsegs mem (spZ regs - READINGS_KB) (spZ regs)).
  { apply stk_of_writable; [lia | lia |]. intros a Ha. rewrite <- SEG. apply HWS. exact Ha. }
  pose proof (rd_bpost_word B API) as BW. rfeed BW.
  pose proof (rd_cstr_keep B API) as RCK. rfeed RCK.
  pose proof (rd_block_facts B API) as RBF. rfeed RBF.
  pose proof (rd_guards B API) as RG. rfeed RG.
  assert (RPa : alloc_ceiling <= bv_unsigned (reg_get regs 12)) by lia.
  assert (RPb : bv_unsigned (reg_get regs 12) + 8 <= 2 ^ 64) by lia.
  assert (RPc : spZ regs <= bv_unsigned (reg_get regs 12)) by lia.
  assert (TS : spZ regs + 8 <= TASK_SIZE) by lia.
  assert (RK : readings_scan_c.READINGS_K = 2544) by reflexivity.
  assert (RF : readings_scan_c.READINGS_FRAME = 176) by reflexivity.
  assert (HK : has_prefixed_c.HAS_PREFIXED_K = 2368) by reflexivity.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. rewrite SEG. unfold mkR_of.
    eapply (evt_normalize rsegs); [exact FrameAPI.wx_apart_rsegs | exact RA |].
    eapply rd_pro with (m := normalize rsegs mem) (lo := spZ regs - READINGS_KB) (ub := ub) (us := su).
    - exact STRLEN.
    - exact (cstr_normalize _ _ _ _ RA CUt).
    - exact (mem_inv_normalize rsegs mem).
    - rewrite SP. apply stk_normalize; [exact STK | lia].
    - rewrite SP. lia.
    - unfold off_stack. rewrite SP. lia.
    - exact LU. }
  intros ms1 (can & (s0 & ARMS & REL & ROS) & EQV).
  destruct ARMS as [(UB & POST) | (UNE & POST)].
  - destruct POST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
      E & MU & WM & MI' & ST').
    subst s0.
    destruct (ms_rel_MS _ _ _ _ _ _ _ _ REL) as [Ecan HRc]. rewrite Ecan in EQV.
    destruct (rd_back mem (ms_mem can) m' _ RA HRc ROS MU WM) as (MU1 & WM1 & RA1).
    apply eqv_shape in EQV as [Ems1 XR1]. rewrite Ems1.
    rewrite SP in MU1.
    pose proof (rd_rp_final regs (ms_regs ms1) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ XR1) as RP1.
    assert (BPs : bpost B (aa_MR API) READINGS_KB stat_writes L A regs mem md L A (ms_regs ms1) (ms_mem can) md).
    { pose proof (rd_bpost_kindA B API) as KA. rfeed KA.
      apply (KA READINGS_KB stat_writes L A regs mem md (ms_regs ms1) (ms_mem can) [(spZ regs - 176, spZ regs)]
        HM HWF HBD RP1 MU1).
      - rewrite SEG. exact WM1.
      - rewrite SEG. exact RA1.
      - intros x Hx HO. apply not_outside1 in HO. split; [lia | left; unfold scratch_k; lia].
      - intros a Ha. unfold writable_at. rewrite SEG. apply WM1. rewrite <- SEG.
        destruct Ha as [Ha|Ha]; [apply HWS; exact Ha | apply HER; exact Ha]. }
    destruct (BW READINGS_KB L A regs mem md L A (ms_regs ms1) (ms_mem can) md (bv_unsigned (reg_get regs 12)) (le8 v)
      BPs HM RPa RPb RPc (length_le8 v) RPB RPW) as [RPB1 RPW1].
    apply SR_ret.
    apply (rd_post_intro L A regs mem md b tb ts ub us Lam peak cnt fail v fx L A (ms_regs ms1) (ms_mem can) md 0).
    + exact HM.
    + exact RA.
    + exact CT.
    + exact CU.
    + exact HT.
    + exact HU.
    + rewrite (ret_pc_ok _ HRA). rewrite SEG. reflexivity.
    + exact FRM.
    + exact INIT.
    + eapply (rd_bpost_weak B API); [|exact BPs]. intros a Ha. left. exact Ha.
    + exact RPW1.
    + rewrite <- (getr_eqv _ _ XR1). reflexivity.
    + left. split; [exact UB|]. split; [reflexivity|]. split; [|exact RPB1].
      apply (ledger_munch B API L A mem md _ _ Lam peak cnt fail HM LED MU1). intros x Hx. apply outside_one. lia.
    + exact RES.
  - destruct POST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & junk & m' &
      E & MU & WM & MI' & ST' & FR').
    subst s0.
    destruct (ms_rel_MS _ _ _ _ _ _ _ _ REL) as [Ecan HRc]. rewrite Ecan in EQV.
    destruct (rd_back mem (ms_mem can) m' _ RA HRc ROS MU WM) as (MU1 & WM1 & RA1).
    pose proof (rw_cells_back _ _ _ _ HRc FR') as FR1.
    apply eqv_shape in EQV as [Ems1 XR1]. rewrite Ems1.
    set (m1 := ms_mem can) in *. set (regs1 := ms_regs ms1) in *.
    change (bv_unsigned (reg_get regs 2)) with (spZ regs) in *.
    clear SP. assert (SP : bv_unsigned (reg_get regs 2) = spZ regs) by reflexivity.
    assert (E1_1 : getr regs1 1 = Z_to_bv 64 0x13c9c) by (rewrite <- (getr_eqv _ _ XR1); reflexivity).
    assert (E1_2 : getr regs1 2 = Z_to_bv 64 (spZ regs - 176)) by (rewrite <- (getr_eqv _ _ XR1); reflexivity).
    assert (E1_4 : getr regs1 4 = reg_get regs 4) by (rewrite <- (getr_eqv _ _ XR1); reflexivity).
    assert (E1_10 : getr regs1 10 = Z_to_bv 64 (Z.of_nat (length ub) + 3))
      by (rewrite <- (getr_eqv _ _ XR1); reflexivity).
    assert (S1' : spZ regs1 = spZ regs - 176).
    { change (bv_unsigned (getr regs1 2) = spZ regs - 176). rewrite E1_2. apply unsigned_lit. lia. }
    assert (HM1 : aa_MR API L A m1 md).
    { apply (MR_high B API L A mem m1 md _ HM MU1). intros x Hx. apply outside_one. lia. }
    replace (PropExec.seg_rom rsegs) with (seg_rom (ms_segs B)) by (rewrite SEG; reflexivity).
    eapply SR_bind.
    { apply (MALLOC fx L A regs1 m1 md (Z.of_nat (length ub) + 3) b Lam peak cnt fail).
      - unfold call_pre_k. rewrite S1'.
        split; [exact HM1|]. split; [exact HWF|]. split; [exact HBD|].
        split; [rewrite E1_1; apply ret_ok_even; vm_compute; reflexivity|].
        split; [Z.div_mod_to_equations; lia|].
        split; [lia|]. split; [lia|].
        split; [intros a Ha; unfold writable_at; rewrite SEG; apply WM1; rewrite <- SEG; apply HWS; lia|].
        split; [rewrite E1_4; exact HTP|].
        split; [intros a Ha; unfold writable_at; rewrite SEG; apply WM1; rewrite <- SEG; apply HER; exact Ha|].
        intros H. rewrite INIT in H. discriminate.
      - exact E1_10.
      - lia.
      - apply (ledger_munch B API L A mem md m1 _ Lam peak cnt fail HM LED MU1). intros x Hx. apply outside_one. lia.
      - rewrite SEG. exact RA1.
      - exact RES.
      - apply room_slots_small; lia. }
    intros c2 (L1 & A1 & regs2 & m2 & md1 & w & -> & RA2 & GK2 & INIT2 & _ & CP2 & LEN2 & R2_10 & SL2 & KP2 & UBK2 & ARMS2).
    rewrite SEG in RA2.
    pose proof CP2 as (HM2 & HWF2 & HBD2 & _ & _ & RP2 & HMD1 & HFR2 & _ & HSC2).
    rewrite SEG in HSC2.
    destruct (mr_model _ _ (aa_laws API) L1 A1 m2 md1 HM2) as (Hh2 & Hl2 & _).
    pose proof (INIT2 INIT) as INIT1.
    rewrite E1_1.
    assert (ST2 : stk rsegs m2 (spZ regs - READINGS_KB) (spZ regs - 176)).
    { apply stk_of_writable; [lia | lia |]. intros a Ha. apply HSC2. unfold scratch_k. left. rewrite S1'. lia. }
    assert (E2_2 : reg_get regs2 2 = Z_to_bv 64 (bv_unsigned (reg_get regs 2) - 176)) by (rgp 2 RP2 XR1).
    assert (E2_3 : reg_get regs2 3 = reg_get regs 3) by (rgp 3 RP2 XR1).
    assert (E2_4 : reg_get regs2 4 = reg_get regs 4) by (rgp 4 RP2 XR1).
    assert (FRa : alloc_ceiling <= spZ regs - 176) by lia.
    assert (FRb : spZ regs - 176 + Z.of_nat 176 <= 2 ^ 64) by lia.
    pose proof (rd_cells_after _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM1 CP2 FR1) as FR2.
    rewrite rd_cells_size in FR2. specialize (FR2 FRa FRb).
    destruct ARMS2 as [(Ecf & Ew & _ & _ & _ & SLb & _ & HBL1 & LED1) |
                       (Ncf & Nw & Wm16 & NS & NI & NL & (b1 & b2 & E1 & E2) & LED1)].
    + subst w.
      assert (FRc : forall a, spZ regs - 176 <= a < spZ regs - 176 + Z.of_nat 176 ->
                ~ scratch_k B (ALLOC_STACK + 32) regs1 a /\ ~ alloc_writes 0 a).
      { intros a Ha. split.
        - unfold scratch_k. rewrite S1'. unfold errno_low in ERR. lia.
        - unfold alloc_writes, alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL. lia. }
      specialize (FR2 FRc).
      assert (E2_10 : reg_get regs2 10 = Z_to_bv 64 0) by exact R2_10.
      eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
      { rewrite canon_mkst. rewrite SEG. unfold mkR_of. rewrite E2_2, E2_3, E2_4, E2_10.
        eapply rd_fail with (ra := reg_get regs 1) (sp := reg_get regs 2) (gp := reg_get regs 3) (tp := reg_get regs 4)
          (s0 := reg_get regs 8) (s1 := reg_get regs 9) (s2 := reg_get regs 18) (s3 := reg_get regs 19)
          (s4 := reg_get regs 20) (s5 := reg_get regs 21) (s6 := reg_get regs 22) (s7 := reg_get regs 23)
          (s8 := reg_get regs 24) (s9 := reg_get regs 25) (s10 := reg_get regs 26) (s11 := reg_get regs 27)
          (lo := spZ regs - READINGS_KB) (junk := junk).
        - rewrite ?SP. lia.
        - rewrite ?SP. exact FR2.
        - rewrite ?SP. exact ST2.
        - rewrite ?SP. lia. }
      intros ms3 (can3 & (Ecan3 & ST3) & EQV3). subst can3.
      apply eqv_shape in EQV3 as [Ems3 XR3]. rewrite Ems3.
      pose proof (rd_rp_final regs (ms_regs ms3) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ XR3) as RP3.
      pose proof (rd_fail_inner B API) as FI. rfeed FI.
      assert (RA2' : ro_agree (ms_segs B) m2) by (rewrite SEG; exact RA2).
      pose proof (FI L A regs1 m1 md L1 A1 regs2 m2 md1 HM1 CP2 KP2 GK2 HBL1 RA2') as BPi.
      pose proof (rd_sandwich L A regs mem md m1 regs1 L1 A1 m2 md1 (ms_regs ms3) PRE S1' MU1 WM1 BPi RP3) as BPs.
      destruct (BW READINGS_KB L A regs mem md L1 A1 (ms_regs ms3) m2 md1 (bv_unsigned (reg_get regs 12)) (le8 v)
        BPs HM RPa RPb RPc (length_le8 v) RPB RPW) as [RPB3 RPW3].
      apply SR_ret.
      apply (rd_post_intro L A regs mem md b tb ts ub us Lam peak cnt fail v fx L1 A1 (ms_regs ms3) m2 md1 0).
      * exact HM.
      * exact RA.
      * exact CT.
      * exact CU.
      * exact HT.
      * exact HU.
      * rewrite (ret_pc_ok _ HRA). rewrite SEG. reflexivity.
      * exact FRM.
      * exact INIT1.
      * eapply (rd_bpost_weak B API); [|exact BPs]. intros a Ha. left. exact Ha.
      * exact RPW3.
      * rewrite <- (getr_eqv _ _ XR3). reflexivity.
      * right. left. split; [exact UNE|]. split; [exact Ecf|]. split; [reflexivity|]. split; [exact LED1 | exact RPB3].
      * exact SLb.
    + assert (INX : In (w - 16, Z.of_nat (length ub) + 3 + 16) (blocks L1 A1)).
      { rewrite E1. apply in_or_app. right. left. reflexivity. }
      assert (Z0 : 0 <= 0 < Z.of_nat (length ub) + 3 + 16) by lia.
      pose proof (RBF L1 A1 m2 md1 _ _ 0 HM2 INX Z0) as (_ & W16 & WE & _ & _).
      assert (WU : bv_unsigned (Z_to_bv 64 w) = w) by (apply unsigned_lit; lia).
      assert (FRc : forall a, spZ regs - 176 <= a < spZ regs - 176 + Z.of_nat 176 ->
                ~ scratch_k B (ALLOC_STACK + 32) regs1 a /\ ~ alloc_writes w a).
      { intros a Ha. split.
        - unfold scratch_k. rewrite S1'. unfold errno_low in ERR. lia.
        - unfold alloc_writes, alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL. lia. }
      specialize (FR2 FRc).
      assert (HB1 : forall a k i, In (a, k) (blocks L A) -> 0 <= i < k -> mbyte rsegs m2 (a + i) = mbyte rsegs m1 (a + i)).
      { intros a k i Hin Hi. pose proof (RBF L A m1 md a k i HM1 Hin Hi) as (_ & B1 & _ & _ & _).
        rewrite <- SEG. apply (KP2 a k i Hin); lia. }
      assert (INL1 : forall y, In y (blocks L A) -> In y (blocks L1 A1)).
      { intros y Hy. rewrite E1. rewrite E2 in Hy. apply in_app_or in Hy as [Hy|Hy]; apply in_or_app;
          [left; exact Hy | right; right; exact Hy]. }
      assert (CTm1 : cstr_at m1 (bv_unsigned (reg_get regs 10)) tb st).
      { eapply cstr_munch; [exact CTt | exact MU1 |]. cbn [disjoint_from]. split; [lia | exact I]. }
      assert (CUm1 : cstr_at m1 (bv_unsigned (reg_get regs 11)) ub su).
      { eapply cstr_munch; [exact CUt | exact MU1 |]. cbn [disjoint_from]. split; [lia | exact I]. }
      destruct (RCK L A m1 L1 A1 m2 md1 _ tb st RA1 RA2 HM2 CTm1 Lst HT INL1 HB1) as (st2 & Lst2 & CT2).
      destruct (RCK L A m1 L1 A1 m2 md1 _ ub su RA1 RA2 HM2 CUm1 Lsu HU INL1 HB1) as (su2 & Lsu2 & CU2).
      destruct (RG L1 A1 m2 md1 HM2) as (canary & GG2 & GD2).
      pose proof (img_strings_keep mem m2 RA RA2 IMG) as IMG2.
      assert (PB : forall i, 0 <= i < Z.of_nat (length ub + 3) -> exists bb, m2 (Z_to_bv 64 (w + i)) = Some bb).
      { intros i Hi. assert (Hi' : 0 <= i + 16 < Z.of_nat (length ub) + 3 + 16) by lia.
        pose proof (RBF L1 A1 m2 md1 _ _ (i + 16) HM2 INX Hi') as (P & _).
        replace (w - 16 + (i + 16)) with (w + i) in P by lia. exact P. }
      assert (Pw0 : 0 <= w) by lia.
      assert (Pw1 : w + Z.of_nat (length ub + 3) <= 2 ^ 64) by lia.
      destruct (present_bytes m2 w (length ub + 3) Pw0 Pw1 PB) as (wj & Lwj & Bwj).
      assert (WB : rw_cells rsegs m2 w [CB (length ub + 3) wj]).
      { split; [split; [split; [exact Lwj | exact I] | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact Bwj] |].
        cbn [cells_size csize]. split; [lia|]. split; [lia|]. intros i Hi.
        assert (Hi2 : 0 <= i < Z.of_nat (length ub + 3)) by lia.
        destruct (PB i Hi2) as (bb & Hb). exact (YL01.present_writable rsegs m2 (w + i) (ex_intro _ bb Hb)). }
      pose proof (rd_img_all B) as RIA. rfeed RIA.
      assert (RFB : forall i, 0 <= i < Z.of_nat (length ub) + 3 -> ro_addr rsegs (wa (w + i)) = false).
      { intros i Hi. destruct (ro_addr rsegs (wa (w + i))) eqn:Er; [|reflexivity]. exfalso.
        assert (Hwi : 0 <= w + i < 2 ^ 64) by lia. unfold wa in Er.
        apply (proj1 (ro_addr_spec (w + i) Hwi)) in Er.
        apply (NI (i + 16)); [lia|]. replace (w - 16 + (i + 16)) with (w + i) by lia. apply RIA. lia. }
      assert (PS : forall i, 0 <= i < Z.of_nat (Z.to_nat ((- (w + Z.of_nat (length ub) + 3)) mod 8)) ->
                     exists bb, m2 (Z_to_bv 64 (w + Z.of_nat (length ub) + 3 + i)) = Some bb).
      { intros i Hi. rewrite Z2Nat.id in Hi by (apply Z.mod_pos_bound; lia).
        apply (BSP L1 A1 m2 md1 (w - 16) (Z.of_nat (length ub) + 3 + 16) _ HM2 INX). Z.div_mod_to_equations. lia. }
      assert (Ps0 : 0 <= w + Z.of_nat (length ub) + 3) by lia.
      assert (Ps1 : w + Z.of_nat (length ub) + 3 + Z.of_nat (Z.to_nat ((- (w + Z.of_nat (length ub) + 3)) mod 8)) <= 2 ^ 64).
      { rewrite Z2Nat.id by (apply Z.mod_pos_bound; lia). Z.div_mod_to_equations. lia. }
      destruct (present_bytes m2 (w + Z.of_nat (length ub) + 3) _ Ps0 Ps1 PS) as (ns & Lns & Bns).
      pose proof (rd_str_vs_block B API) as RSB. rfeed RSB.
      pose proof (RSB L A L1 A1 m2 md1 _ ub (Z.of_nat (length su)) w (Z.of_nat (length ub) + 3) b1 b2 HM2 HU Bu0
        ltac:(lia) Lsu E1 E2 ltac:(lia) Wm16) as DU.
      pose proof (RSB L A L1 A1 m2 md1 _ tb (Z.of_nat (length st)) w (Z.of_nat (length ub) + 3) b1 b2 HM2 HT Bt0
        ltac:(lia) Lst E1 E2 ltac:(lia) Wm16) as DT.
      assert (E2_8 : reg_get regs2 8 = reg_get regs 12) by (rgp 8 RP2 XR1).
      assert (E2_9 : reg_get regs2 9 = reg_get regs 11) by (rgp 9 RP2 XR1).
      assert (E2_10 : reg_get regs2 10 = Z_to_bv 64 w) by exact R2_10.
      assert (E2_18 : reg_get regs2 18 = reg_get regs 10) by (rgp 18 RP2 XR1).
      assert (E2_19 : reg_get regs2 19 = Z_to_bv 64 (Z.of_nat (length ub))) by (rgp 19 RP2 XR1).
      assert (E2_21 : reg_get regs2 21 = Z_to_bv 64 (Z.of_nat (length ub) + 3)) by (rgp 21 RP2 XR1).
      eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
      { rewrite canon_mkst. rewrite SEG. unfold mkR_of.
        rewrite E2_2, E2_3, E2_4, E2_8, E2_9, E2_10, E2_18, E2_19, E2_21.
        eapply (evt_normalize_cj rsegs); [exact FrameAPI.wx_apart_rsegs | exact RA2 |].
        eapply rd_mid with (ra := reg_get regs 1) (sp := reg_get regs 2) (gp := reg_get regs 3) (tp := reg_get regs 4)
          (s0 := reg_get regs 8) (s1 := reg_get regs 9) (s2 := reg_get regs 18) (s3 := reg_get regs 19)
          (s4 := reg_get regs 20) (s5 := reg_get regs 21) (s6 := reg_get regs 22) (s7 := reg_get regs 23)
          (s8 := reg_get regs 24) (s9 := reg_get regs 25) (s10 := reg_get regs 26) (s11 := reg_get regs 27)
          (rp := reg_get regs 12) (uri := reg_get regs 11) (w := Z_to_bv 64 w) (txt := reg_get regs 10)
          (un := Z_to_bv 64 (Z.of_nat (length ub))) (canary := canary) (m := normalize_cj rsegs m2)
          (lo := spZ regs - READINGS_KB) (junk := junk) (wj := wj) (ns := ns) (tb := tb) (ts := st2) (ub := ub) (us := su2).
        - exact SNP.
        - exact STRS.
        - rewrite ?SP. lia.
        - rewrite ?SP. lia.
        - rewrite ?SP. apply rw_cells_norm_cj; [exact RA2 | exact FR2 | rewrite rd_cells_size; lia |].
          intros i Hi. apply ro_false_hi. rewrite rd_cells_size in Hi. lia.
        - rewrite ?SP. apply stk_norm_cj; [exact RA2 | exact ST2 | lia |]. intros a Ha. apply ro_false_hi. lia.
        - rewrite ?SP. unfold SNPRINTF_K. lia.
        - unfold IMG_END. lia.
        - exact (mem_inv_cj_inv rsegs _ (mem_inv_cj_normalize rsegs m2)).
        - exact (mem_inv_cj_task rsegs _ (mem_inv_cj_normalize rsegs m2)).
        - exact FRM.
        - apply cstr_norm_cj; [exact RA2 | exact CT2 | rewrite Lst2; lia].
        - apply cstr_norm_cj; [exact RA2 | exact CU2 | rewrite Lsu2; lia].
        - exact UNE.
        - exact LU.
        - apply bytes_at_normalize_cj_low; [exact RA2 | | exact (proj2 (proj2 IMG2))].
          change (Z.of_nat (length (map (Z_to_bv 8) (ManifestB.fmt_whole ++ [0])))) with 5.
          unfold ManifestB.FMT_WHOLE_STR. lia.
        - rewrite WU. apply rw_cells_norm_cj; [exact RA2 | exact WB | cbn [cells_size csize]; lia |].
          intros i Hi. cbn [cells_size csize] in Hi. apply RFB. lia.
        - rewrite WU. apply bytes_at_normalize_cj_low; [exact RA2 | | exact Bns].
          rewrite Lns, Z2Nat.id by (apply Z.mod_pos_bound; lia). Z.div_mod_to_equations. lia.
        - rewrite WU, Lns, Z2Nat.id by (apply Z.mod_pos_bound; lia). lia.
        - rewrite WU. lia.
        - rewrite WU. intros i Hi s Hs Hr. apply (NI (i + 16)); [lia|].
          split; [rewrite SEG; intros Hn; pose proof rsegs_tri as T; rewrite Hn in T; cbn in T; discriminate T|].
          exists s. rewrite SEG. split; [exact Hs|]. replace (w - 16 + (i + 16)) with (w + i) by lia. exact Hr.
        - rewrite WU, Lns, Z2Nat.id by (apply Z.mod_pos_bound; lia). Z.div_mod_to_equations. lia.
        - rewrite ?SP. left. rewrite Lst2. lia.
        - rewrite ?SP. left. rewrite Lsu2. lia.
        - rewrite WU, Lsu2. lia.
        - rewrite WU, Lst2. lia.
        - lia.
        - lia.
        - apply bytes_at_normalize_cj_low; [exact RA2 | rewrite length_le8; unfold GOT_GUARD; lia | exact (c8_bytes _ _ _ GG2)].
        - apply bytes_at_normalize_cj_low; [exact RA2 | rewrite length_le8; unfold GUARD; lia | exact (c8_bytes _ _ _ GD2)]. }
      intros ms3 (can3 & (s3 & POST3 & REL3 & ROS3) & EQV3).
      destruct POST3 as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & F' & fc' & m3' &
        E3 & MU3 & WM3 & MI3 & FRM3 & ST3 & FR3).
      subst s3.
      destruct (ms_rel_cj_MS _ _ _ _ _ _ _ _ REL3) as [Ecan3 HR3]. rewrite Ecan3 in EQV3.
      destruct (rd_back_cj m2 (ms_mem can3) m3' _ RA2 HR3 ROS3 MU3 WM3) as (MU3' & WM3' & RA3).
      pose proof (rw_cells_back_cj _ _ _ _ HR3 FR3) as FR3'.
      pose proof (eqv_shape (mkFP F' fc') _ _ _ _ _ EQV3) as [Ems3 XR3]. rewrite Ems3.
      set (m3 := ms_mem can3) in *. set (regs3 := ms_regs ms3) in *.
      change (bv_unsigned (reg_get regs 2)) with (spZ regs) in *. rewrite WU in MU3'.
      clear SP. assert (SP : bv_unsigned (reg_get regs 2) = spZ regs) by reflexivity.
      replace (w + Z.of_nat (length ub) + 3) with (w + (Z.of_nat (length ub) + 3)) in MU3' by lia.
      assert (E3_1 : getr regs3 1 = Z_to_bv 64 0x13cd4) by (rewrite <- (getr_eqv _ _ XR3); reflexivity).
      assert (E3_2 : getr regs3 2 = Z_to_bv 64 (spZ regs - 176)) by (rewrite <- (getr_eqv _ _ XR3); reflexivity).
      assert (E3_4 : getr regs3 4 = reg_get regs 4) by (rewrite <- (getr_eqv _ _ XR3); reflexivity).
      assert (E3_10 : getr regs3 10 = Z_to_bv 64 w) by (rewrite <- (getr_eqv _ _ XR3); reflexivity).
      assert (S3' : spZ regs3 = spZ regs - 176).
      { change (bv_unsigned (getr regs3 2) = spZ regs - 176). rewrite E3_2. apply unsigned_lit. lia. }
      pose proof (rd_MR_write B API) as MW. rfeed MW.
      assert (HM3 : aa_MR API L1 A1 m3 md1).
      { apply (MW L1 A1 m2 md1 m3 (spZ regs - READINGS_KB) (spZ regs - 176) w (Z.of_nat (length ub) + 3) HM2 INX);
          [lia | lia | exact MU3' | rewrite SEG; exact WM3']. }
      pose proof (rd_ledger_write B API) as LW. rfeed LW.
      pose proof (LW L1 A1 m2 md1 m3 (spZ regs - READINGS_KB) (spZ regs - 176) w (Z.of_nat (length ub) + 3) Lam _ _ _
        HM2 LED1 INX ltac:(lia) ltac:(lia) MU3') as LED3.
      replace (PropExec.seg_rom rsegs) with (seg_rom (ms_segs B)) by (rewrite SEG; reflexivity).
      eapply SR_bind.
      { apply (FREE (mkFP F' fc') L1 A1 regs3 m3 md1 w (Z.of_nat (length ub) + 3)
          (sb_malloc b (Z.of_nat (length ub) + 3 + 16)) ((w, Z.of_nat (length ub) + 3) :: Lam)
          (Z.max peak (lsum Lam + (Z.of_nat (length ub) + 3))) ((cnt + 1) mod 2 ^ 64) fail).
        - unfold call_pre_k. rewrite S3'.
          split; [exact HM3|]. split; [exact HWF2|]. split; [exact HBD2|].
          split; [rewrite E3_1; apply ret_ok_even; vm_compute; reflexivity|].
          split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|].
          split; [intros a Ha; unfold writable_at; rewrite SEG; apply WM3'; apply HSC2; unfold scratch_k; left;
                  rewrite S1'; lia|].
          split; [rewrite E3_4; exact HTP|].
          split; [intros a Ha; unfold writable_at; rewrite SEG; apply WM3'; apply HSC2; unfold scratch_k; right;
                  exact Ha|].
          intros H. rewrite INIT1 in H. discriminate.
        - exact E3_10.
        - exact LED3.
        - rewrite SEG. exact RA3.
        - right. left. reflexivity.
        - exact SL2. }
      intros c4 (L4 & A4 & regs4 & m4 & md2 & -> & RA4 & GK4 & INIT4 & _ & CP4 & LEN4 & KP4 & UBK4 & ARMS4).
      destruct ARMS4 as [(Ew0 & _) | (_ & (c1 & c2 & F1 & F2) & (l1 & l2 & EL & LED4) & SL4)]; [lia|].
      rewrite SEG in RA4.
      pose proof CP4 as (HM4 & HWF4 & HBD4 & _ & _ & RP4 & HMD2 & HFR4 & _ & HSC4).
      destruct (mr_model _ _ (aa_laws API) L4 A4 m4 md2 HM4) as (Hh4 & Hl4 & _).
      pose proof (INIT4 INIT1) as INIT5.
      pose proof (rd_inner B API) as RI. rfeed RI.
      assert (MU3i : munch [(spZ regs1 - (ALLOC_STACK + 32), spZ regs1); (w, w + (Z.of_nat (length ub) + 3))] m2 m3).
      { apply (munch_eq2 _ _ _ _ _ _ _ _ _ _ MU3'); lia. }
      assert (RA4' : ro_agree (ms_segs B) m4) by (rewrite SEG; exact RA4).
      assert (WM3s : wmono (ms_segs B) m2 m3) by (rewrite SEG; exact WM3').
      assert (Hac1 : alloc_ceiling + (ALLOC_STACK + 32) <= spZ regs1) by lia.
      assert (H631 : spZ regs1 < 2 ^ 63) by lia.
      assert (S31 : spZ regs3 = spZ regs1) by lia.
      assert (N0 : 0 <= Z.of_nat (length ub) + 3) by lia.
      pose proof (RI L A regs1 m1 md L1 A1 regs2 m2 md1 m3 regs3 L4 A4 regs4 m4 md2 w (Z.of_nat (length ub) + 3)
        b1 b2 c1 c2 HM1 Hac1 H631 S31 CP2 KP2 GK2 N0 NI E1 E2 MU3i WM3s HM3 CP4 KP4 GK4 F1 F2 RA4') as BPi.
      rewrite E3_1.
      assert (E4_2 : reg_get regs4 2 = Z_to_bv 64 (bv_unsigned (reg_get regs 2) - 176)) by (rgp 2 RP4 XR3).
      assert (E4_3 : reg_get regs4 3 = reg_get regs 3) by (rgp 3 RP4 XR3).
      assert (E4_4 : reg_get regs4 4 = reg_get regs 4) by (rgp 4 RP4 XR3).
      assert (E4_8 : reg_get regs4 8 = reg_get regs 12) by (rgp 8 RP4 XR3).
      assert (E4_9 : reg_get regs4 9 = reg_get regs 11) by (rgp 9 RP4 XR3).
      assert (E4_18 : reg_get regs4 18 = reg_get regs 10) by (rgp 18 RP4 XR3).
      assert (E4_19 : reg_get regs4 19 = Z_to_bv 64 (Z.of_nat (length ub))) by (rgp 19 RP4 XR3).
      assert (E4_21 : reg_get regs4 21 = rd_found (reg_get regs 10) tb ub) by (rgp 21 RP4 XR3).
      pose proof (rd_cells_after _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM3 CP4 FR3') as FR4.
      rewrite rd_cells_size in FR4.
      assert (FRc4 : forall a, spZ regs - 176 <= a < spZ regs - 176 + Z.of_nat 176 ->
                ~ scratch_k B ALLOC_STACK regs3 a /\ ~ free_writes w (Z.of_nat (length ub) + 3) a).
      { intros a Ha. split.
        - unfold scratch_k. rewrite S3'. unfold errno_low in ERR. lia.
        - unfold free_writes, G_LIVE. lia. }
      specialize (FR4 FRa FRb FRc4).
      assert (ST4 : stk rsegs m4 (spZ regs - READINGS_KB) (spZ regs - 176)).
      { apply (rd_stk_after _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM3 CP4); [lia | lia | |].
        - intros a Ha. unfold writable_at. apply WM3'. apply HSC2. unfold scratch_k. left. rewrite S1'. lia.
        - intros a Ha. unfold free_writes, G_LIVE. lia. }
      pose proof LED1 as (_ & _ & _ & _ & ND1 & _).
      pose proof (rd_lam_eq Lam l1 l2 _ ND1 EL) as ELam. rewrite ELam in LED4.
      replace (lsum Lam + (Z.of_nat (length ub) + 3)) with (lsum Lam + Z.of_nat (length ub) + 3) in LED4 by lia.
      assert (SL5 : res_ok_slots A4 b) by (rewrite sb_free_malloc in SL4; exact SL4).
      pose proof BPi as (_ & _ & _ & _ & _ & HBL4 & HBB4 & _). rewrite SEG in HBB4.
      assert (INL4 : forall y, In y (blocks L A) -> In y (blocks L4 A4)) by (intros y Hy; rewrite HBL4; exact Hy).
      destruct (RCK L A m1 L4 A4 m4 md2 _ tb st RA1 RA4 HM4 CTm1 Lst HT INL4 HBB4) as (st4 & Lst4 & CT4).
      destruct (RCK L A m1 L4 A4 m4 md2 _ ub su RA1 RA4 HM4 CUm1 Lsu HU INL4 HBB4) as (su4 & Lsu4 & CU4).
      destruct (RG L4 A4 m4 md2 HM4) as (canary4 & GG4 & GD4).
      pose proof (img_strings_keep mem m4 RA RA4 IMG) as IMG4.
      pose proof (rd_sandwich L A regs mem md m1 regs1 L4 A4 m4 md2 regs PRE S1' MU1 WM1 BPi (fun r _ => eq_refl)) as BPr.
      destruct (BW READINGS_KB L A regs mem md L4 A4 regs m4 md2 (bv_unsigned (reg_get regs 12)) (le8 v)
        BPr HM RPa RPb RPc (length_le8 v) RPB RPW) as [RPB4 RPW4].
      assert (LZ : (length (ManifestMem.zbytes ub) =? 0)%nat = false).
      { destruct ub; [exfalso; exact (UNE eq_refl) | reflexivity]. }
      assert (LTB : length (ManifestMem.zbytes tb) = length tb) by (unfold ManifestMem.zbytes; apply length_map).
      assert (TB64 : bv_unsigned (reg_get regs 10) + Z.of_nat (length tb) < 2 ^ 64) by lia.
      assert (TB0 : 0 < bv_unsigned (reg_get regs 10)) by lia.
      destruct (Z.eq_dec (bv_unsigned (rd_found (reg_get regs 10) tb ub)) 0) as [F0|F0].
      * pose proof (proj1 (rd_found_zero _ tb ub TB0 TB64) F0) as WH.
        eapply evt_SR_canon; [ | exact Hh4 | exact Hl4 | ].
        { rewrite canon_mkst. rewrite SEG. unfold mkR_of.
          rewrite E4_3, E4_4, E4_8, E4_9, E4_18, E4_19, E4_21.
          eapply (evt_normalize rsegs); [exact FrameAPI.wx_apart_rsegs | exact RA4 |].
          eapply rd_miss; [exact F0|].
          eapply SCAN with (ra := reg_get regs 1) (sp := reg_get regs 2) (s0 := reg_get regs 8) (s1 := reg_get regs 9)
            (s2 := reg_get regs 18) (s3 := reg_get regs 19) (s4 := reg_get regs 20) (s5 := reg_get regs 21)
            (s6 := reg_get regs 22) (s7 := reg_get regs 23) (s8 := reg_get regs 24) (s9 := reg_get regs 25)
            (s10 := reg_get regs 26) (s11 := reg_get regs 27) (lo := spZ regs - READINGS_KB) (junk := junk)
            (tb := tb) (ts := st4) (ub := ub) (us := su4) (v := v).
          - rewrite E4_2. reflexivity.
          - rewrite ?SP. apply rw_cells_norm; [exact RA4 | exact FR4 |].
            intros i Hi. apply ro_false_hi. cbn [cells_size csize] in Hi. lia.
          - exact (mem_inv_normalize rsegs m4).
          - rewrite ?SP. apply stk_normalize; [exact ST4 | lia].
          - rewrite ?SP. lia.
          - exact (cstr_normalize _ _ _ _ RA4 CT4).
          - exact (cstr_normalize _ _ _ _ RA4 CU4).
          - exact UNE.
          - reflexivity.
          - exact T4.
          - lia.
          - exact U4.
          - exact (bytes_at_normalize rsegs _ _ _ RA4 RPB4).
          - apply (wr_at_norm rsegs m4 (normalize rsegs m4)); [exact (mem_rel_normalize rsegs m4 RA4) | exact RPW4 |].
            intros i Hi. apply ro_false_hi. lia.
          - exact (bytes_at_normalize rsegs _ _ _ RA4 (proj1 IMG4)).
          - exact (bytes_at_normalize rsegs _ _ _ RA4 (proj1 (proj2 IMG4))).
          - exact (bytes_at_normalize rsegs _ _ _ RA4 (c8_bytes _ _ _ GG4)).
          - exists canary4. exact (bytes_at_normalize rsegs _ _ _ RA4 (c8_bytes _ _ _ GD4)).
          - rewrite ?SP. lia.
          - rewrite ?SP. lia.
          - unfold off_stack. rewrite ?SP, Lst4. lia.
          - unfold off_stack. rewrite ?SP, Lsu4. lia.
          - unfold off_stack. rewrite ?SP. lia.
          - unfold off_stack, readings_scan_c.PREFIX_LC_AT. rewrite ?SP. lia.
          - unfold off_stack, readings_scan_c.PREFIX_UC_AT. rewrite ?SP. lia.
          - cbn [disjoint_from]. unfold readings_scan_c.PREFIX_LC_AT, readings_scan_c.PREFIX_UC_AT.
            rewrite Lst4, Lsu4. repeat split; lia. }
        intros ms5 (can5 & (s5 & POST5 & REL5 & ROS5) & EQV5).
        destruct POST5 as (u0 & u1 & u2 & a05 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m5' &
          E5 & MU5 & WM5 & MI5 & ST5 & R5 & RB5).
        subst s5.
        destruct (ms_rel_MS _ _ _ _ _ _ _ _ REL5) as [Ecan5 HR5]. rewrite Ecan5 in EQV5.
        destruct (rd_back m4 (ms_mem can5) m5' _ RA4 HR5 ROS5 MU5 WM5) as (MU5' & WM5' & RA5).
        pose proof (proj2 (bytes_at_rel rsegs (ms_mem can5) m5' _ _ HR5) RB5) as RB5'.
        pose proof (eqv_shape (mkFP F' fc') _ _ _ _ _ EQV5) as [Ems5 XR5]. rewrite Ems5.
        set (m5 := ms_mem can5) in *.
        change (bv_unsigned (reg_get regs 2)) with (spZ regs) in *.
        clear SP. assert (SP : bv_unsigned (reg_get regs 2) = spZ regs) by reflexivity.
        pose proof (rd_rp_final regs (ms_regs ms5) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ XR5) as RP5.
        pose proof (rd_sandwich L A regs mem md m1 regs1 L4 A4 m4 md2 (ms_regs ms5) PRE S1' MU1 WM1 BPi RP5) as BPs.
        assert (BP5 : bpost B (aa_MR API) READINGS_KB (rd_writes (bv_unsigned (reg_get regs 12))) L A regs mem md L4 A4
                  (ms_regs ms5) m5 md2).
        { pose proof (rd_bpost_ext B API) as BE. rfeed BE.
          apply (BE READINGS_KB (rd_writes (bv_unsigned (reg_get regs 12))) L A regs mem md L4 A4 (ms_regs ms5) m4 md2
            [(spZ regs - readings_scan_c.READINGS_K, spZ regs);
             (bv_unsigned (reg_get regs 12), bv_unsigned (reg_get regs 12) + 8)] m5).
          - eapply (rd_bpost_weak B API); [|exact BPs]. intros a Ha. left. exact Ha.
          - exact MU5'.
          - rewrite SEG. exact WM5'.
          - rewrite SEG. exact RA5.
          - intros x Hx HO. apply not_outside2 in HO.
            destruct HO as [HO|HO]; (split; [lia|]); [left; unfold scratch_k; left; lia | right; unfold rd_writes; right; lia]. }
        apply SR_ret.
        apply (rd_post_intro L A regs mem md b tb ts ub us Lam peak cnt fail v (mkFP F' fc') L4 A4 (ms_regs ms5) m5 md2
          (ManifestModel.scan (ManifestMem.zbytes tb) (ManifestMem.zbytes ub) 0 0 (S (length tb)))).
        -- exact HM.
        -- exact RA.
        -- exact CT.
        -- exact CU.
        -- exact HT.
        -- exact HU.
        -- rewrite (ret_pc_ok _ HRA). rewrite SEG. reflexivity.
        -- exact FRM3.
        -- exact INIT5.
        -- exact BP5.
        -- exact (wr_at_wmono _ _ _ _ RPW4 WM5').
        -- rewrite <- (getr_eqv _ _ XR5). exact R5.
        -- right. right. split; [exact UNE|]. split; [exact Ncf|]. split.
           { unfold ManifestModel.names. rewrite LZ, WH, LTB. reflexivity. }
           split.
           { apply (ledger_munch B API L4 A4 m4 md2 m5 _ Lam _ _ fail HM4 LED4 MU5'). intros x Hx. cbn [outside].
             split; [lia | split; [lia | exact I]]. }
           replace (ManifestModel.nreadings (ManifestMem.zbytes tb) (ManifestMem.zbytes ub))
             with (ManifestModel.readings (ManifestMem.zbytes tb) (ManifestMem.zbytes ub) 0 0 (S (length tb)))
             by (unfold ManifestModel.nreadings; rewrite LZ, WH, LTB; reflexivity).
           exact RB5'.
        -- exact SL5.
      * assert (WH : whole (ManifestMem.zbytes tb) (ManifestMem.zbytes ub) = true).
        { destruct (whole (ManifestMem.zbytes tb) (ManifestMem.zbytes ub)) eqn:Wh; [reflexivity|].
          exfalso. apply F0. exact (proj2 (rd_found_zero _ tb ub TB0 TB64) Wh). }
        eapply evt_SR_canon; [ | exact Hh4 | exact Hl4 | ].
        { rewrite canon_mkst. rewrite SEG. unfold mkR_of. rewrite E4_2, E4_3, E4_4, E4_21.
          eapply rd_hit with (ra := reg_get regs 1) (sp := reg_get regs 2) (gp := reg_get regs 3) (tp := reg_get regs 4)
            (s0 := reg_get regs 8) (s1 := reg_get regs 9) (s2 := reg_get regs 18) (s3 := reg_get regs 19)
            (s4 := reg_get regs 20) (s5 := reg_get regs 21) (s6 := reg_get regs 22) (s7 := reg_get regs 23)
            (s8 := reg_get regs 24) (s9 := reg_get regs 25) (s10 := reg_get regs 26) (s11 := reg_get regs 27)
            (m := m4) (lo := spZ regs - READINGS_KB) (junk := junk).
          - rewrite ?SP. lia.
          - exact F0.
          - rewrite ?SP. exact FR4.
          - rewrite ?SP. exact ST4.
          - rewrite ?SP. lia. }
        intros ms5 (can5 & (Ecan5 & ST5) & EQV5). subst can5.
        pose proof (eqv_shape (mkFP F' fc') _ _ _ _ _ EQV5) as [Ems5 XR5]. rewrite Ems5.
        pose proof (rd_rp_final regs (ms_regs ms5) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ XR5) as RP5.
        pose proof (rd_sandwich L A regs mem md m1 regs1 L4 A4 m4 md2 (ms_regs ms5) PRE S1' MU1 WM1 BPi RP5) as BPs.
        apply SR_ret.
        apply (rd_post_intro L A regs mem md b tb ts ub us Lam peak cnt fail v (mkFP F' fc') L4 A4 (ms_regs ms5) m4 md2 1).
        -- exact HM.
        -- exact RA.
        -- exact CT.
        -- exact CU.
        -- exact HT.
        -- exact HU.
        -- rewrite (ret_pc_ok _ HRA). rewrite SEG. reflexivity.
        -- exact FRM3.
        -- exact INIT5.
        -- eapply (rd_bpost_weak B API); [|exact BPs]. intros a Ha. left. exact Ha.
        -- exact RPW4.
        -- rewrite <- (getr_eqv _ _ XR5). reflexivity.
        -- right. right. split; [exact UNE|]. split; [exact Ncf|]. split.
           { unfold ManifestModel.names. rewrite LZ, WH. reflexivity. }
           split; [exact LED4|].
           replace (ManifestModel.nreadings (ManifestMem.zbytes tb) (ManifestMem.zbytes ub)) with O
             by (unfold ManifestModel.nreadings; rewrite LZ, WH; reflexivity).
           cbn [Z.of_nat]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact RPB4.
        -- exact SL5.
Qed.

End R.

Theorem readings_holds {fx : YK11.FPState} {rc : YM05.RunCeil} (B : malloc_syms) (API : AllocAPI B) :
  statics_free B (aa_MR API) -> statics_facts B -> ManifestB.ctx_owned B (aa_MR API) -> AllocExtra B (aa_MR API) ->
  block_slack_present B API -> errno_low B -> guard_syms B ->
  LibcNeeds_c.strlen_contract -> LibcNeeds_c.strncmp_contract -> LibcNeeds_c.strncasecmp_contract ->
  LibcNeeds_c.strchr_contract -> LibcNeeds_c.isalnum_contract -> has_prefixed_c.has_prefixed_contract ->
  snprintf_contract -> LibcNeeds_c.strstr_contract ->
  (forall fx' : FPState, @fuzz_malloc_contract fx' rc B API) ->
  (forall fx' : FPState, @fuzz_free_contract fx' rc B API) ->
  readings_contract B API.
Proof.
  intros SF SFA CTX AX BSP ERR GS LEN NCMP NCASE CHR ALNUM HP SNPc STRSc MALLOCc FREEc.
  pose proof (readings_scan.readings_scan_holds LEN NCMP NCASE CHR ALNUM HP) as SCANc.
  unfold readings_contract.
  intros L A regs mem md b tb ts ub us Lam peak cnt fail v SEG.
  pose proof (rd_core B API) as H. rfeed H.
  exact (H L A regs mem md b tb ts ub us Lam peak cnt fail v SEG).
Qed.
