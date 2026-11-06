From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame Step Tac
  Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotInv write_uint_c reac_identity_fw_str_c
  reac_identity_reac_ver_str_c put_dec_c reac_box_family_of_c.
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.SlotInv(bsz, z8, zlen, fw_res, fw_out, id_VER, ver_res,
  ver_out, HWT_ADDR).
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.reac_identity_fw_str_c(FW, L, reac_identity_fw_str_c3,
  reac_identity_fw_str_c3_len, reac_identity_fw_str_c3_nz, reac_identity_fw_str_dec_h, reac_identity_fw_str_dec_f).
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.reac_identity_reac_ver_str_c(reac_ver_str_VER,
  reac_ver_str_LV, reac_ver_str_DEC2).
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.put_dec_c(dec_len).
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14 YI04.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import SlotInvU.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.Seg Require Import UTac_ucg.
Import ListNotations.
Open Scope Z_scope.

Lemma d01_ov1 : forall segs m y, ov_read_bytes segs m y 1 = match mrd segs m y with Some b => Some [b] | None => None end.
Proof. intros segs m y. rewrite ov_rdn, rdn_unfold. destruct (mrd segs m y); reflexivity. Qed.

Lemma d01_zero : forall inp j, 0 <= j -> nlen inp <= cT inp + j -> tb inp j = 0.
Proof.
  intros inp j Hj H. pose proof (rec_c_range inp (nrecn inp)) as Hc. unfold cT in *.
  unfold tb, inb, RcIdentModel.bz, RcIdentModel.nthb, cT. unfold nlen in *.
  rewrite nth_overflow by lia. reflexivity.
Qed.

Lemma d01_ne : forall x k, 0 <= x < 2 ^ 64 -> 0 <= k < 2 ^ 64 -> x <> k ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 k) = false.
Proof. intros x k Hx Hk H. unfold bv_eqb. rewrite !MState.unsigned_lit by lia. apply Z.eqb_neq. exact H. Qed.

Lemma d01_eq : forall x k, x = k -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 k) = true.
Proof. intros x k ->. unfold bv_eqb. apply Z.eqb_refl. Qed.

Lemma d1_ltu1 : forall y, 2 <= y < 2 ^ 64 -> bv_ltu (Z_to_bv 64 1) (Z_to_bv 64 y) = true.
Proof. intros y Hy. unfold bv_ltu. rewrite !MState.unsigned_lit by lia. apply Z.ltb_lt. lia. Qed.

Lemma d01_rdw : forall m a v x b, ov_read_bytes rsegs m (wa x) 1 = Some [b] -> 0 <= a ->
  a + 8 <= 2 ^ 64 -> 0 <= x < 2 ^ 64 -> x < a \/ a + 8 <= x ->
  ov_read_bytes rsegs (write_to_mem m (Z_to_bv 64 a) (le8 v)) (wa x) 1 = Some [b].
Proof.
  intros m a v x b H Ha Hl Hx Hd. rewrite d01_ov1 in *. unfold mrd in *.
  assert (Hu : bv_unsigned (wa x) = x) by (unfold wa; apply MState.unsigned_lit; lia).
  change (Z_to_bv 64 a) with (wa a).
  rewrite write_to_mem_spec by (rewrite ?length_le8; lia). rewrite Hu, length_le8.
  destruct (Z.leb_spec a x); destruct (Z.ltb_spec x (a + Z.of_nat 8)); cbn [andb]; try lia; exact H.
Qed.

Lemma d01_af2 : forall x, 0 <= x < 256 -> x - x * 205 / 8192 * 40 = x mod 40.
Proof.
  intros x Hx.
  pose proof (z_all_spec (fun x => (x - x * 205 / 8192 * 40) =? x mod 40) 256 0 ltac:(vm_compute; reflexivity) x
    ltac:(lia)) as H.
  cbv beta in H. apply Z.eqb_eq in H. exact H.
Qed.

Lemma d01_m40 : forall b : byte,
  Z_to_bv 64 (bv_unsigned (zxb b) - bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned
    (Z_to_bv 64 (bv_unsigned (zxb b) * 205)) ≫ 13)) * 40))) = Z_to_bv 64 (bv_unsigned b mod 40).
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
  unfold zxb. rewrite (MState.unsigned_lit (bv_unsigned b)) by lia.
  rewrite (MState.unsigned_lit (bv_unsigned b * 205)) by lia.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 13) with 8192.
  rewrite (MState.unsigned_lit (bv_unsigned b * 205 / 8192)) by (Z.div_mod_to_equations; lia).
  rewrite (MState.unsigned_lit (bv_unsigned b * 205 / 8192 * 40)) by (Z.div_mod_to_equations; lia).
  f_equal. apply d01_af2. exact R.
Qed.

Lemma d01_land : forall b : byte, forall n, 0 <= n ->
  Z_to_bv 64 (Z.land (bv_unsigned (zxb b)) (Z.ones n)) = Z_to_bv 64 (bv_unsigned b mod 2 ^ n).
Proof.
  intros b n Hn. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
  unfold zxb. rewrite (MState.unsigned_lit (bv_unsigned b)) by lia. rewrite Z.land_ones by exact Hn. reflexivity.
Qed.

Lemma d01_m16 : forall b : byte, Z_to_bv 64 (Z.land (bv_unsigned (zxb b)) 15) = Z_to_bv 64 (bv_unsigned b mod 16).
Proof. intros b. exact (d01_land b 4 ltac:(lia)). Qed.
Lemma d01_m32 : forall b : byte, Z_to_bv 64 (Z.land (bv_unsigned (zxb b)) 31) = Z_to_bv 64 (bv_unsigned b mod 32).
Proof. intros b. exact (d01_land b 5 ltac:(lia)). Qed.
Lemma d01_m64 : forall b : byte, Z_to_bv 64 (Z.land (bv_unsigned (zxb b)) 63) = Z_to_bv 64 (bv_unsigned b mod 64).
Proof. intros b. exact (d01_land b 6 ltac:(lia)). Qed.

Lemma d1_wtm : forall (m1 m2 : word -> option byte) (a1 a2 : word) (v1 v2 : list byte),
  m1 = m2 -> a1 = a2 -> v1 = v2 -> write_to_mem m1 a1 v1 = write_to_mem m2 a2 v2.
Proof. intros. subst. reflexivity. Qed.

Lemma d1_rdin : forall mem p inp i,
  (forall j, 0 <= j < nlen inp -> mbyte rsegs mem (p + j) = nth_error inp (Z.to_nat j)) -> 0 <= i < nlen inp ->
  ov_read_bytes rsegs mem (wa (p + i)) 1 = Some [RcIdentModel.nthb inp (Z.to_nat i)].
Proof.
  intros mem p inp i H Hi. rewrite d01_ov1. change (mrd rsegs mem (wa (p + i))) with (mbyte rsegs mem (p + i)).
  rewrite H by exact Hi. unfold RcIdentModel.nthb. unfold nlen in Hi.
  rewrite (nth_error_nth' inp (RcIdentModel.zb 0)) by lia. reflexivity.
Qed.

Definition d1_K (x2 x3 x4 : word) (sp : Z) (inp : list byte) (m : word -> option byte)
    (R : bvmap 5 word) (pc' : word) (m' : word -> option byte) : Prop :=
  pc' = Z_to_bv 64 0x13784 /\
  m' = write_to_mem (write_to_mem m (Z_to_bv 64 (sp + 56)) (le8 (Z_to_bv 64 (t_out inp))))
         (Z_to_bv 64 (sp + 48)) (le8 (Z_to_bv 64 (t_row inp))) /\
  getr R 2 = x2 /\ getr R 3 = x3 /\ getr R 4 = x4 /\
  getr R 24 = Z_to_bv 64 (t_fam_raw inp) /\ getr R 9 = Z_to_bv 64 (t_in inp) /\
  getr R 25 = Z_to_bv 64 (t_cap_name inp) /\ getr R 27 = Z_to_bv 64 (t_cap_tok inp) /\
  getr R 19 = Z_to_bv 64 (t_cap_disp inp) /\ getr R 20 = Z_to_bv 64 (t_cap_fw inp) /\
  getr R 21 = Z_to_bv 64 (t_cap_ver inp) /\ getr R 11 = Z_to_bv 64 (tb inp 9) /\
  getr R 10 = Z_to_bv 64 (tb inp 10).

Ltac d01_getr :=
  repeat match goal with
  | |- context [getr ?R ?r] =>
      is_concrete_map R;
      let p := eval vm_compute in (bv_key r) in
      change (getr R r) with (Sem.reg_get R r)
  end.

Ltac d01_z :=
  unfold t_fam_raw, t_in, t_out, t_row, t_cap_fw, t_cap_ver, t_cap_name, t_cap_tok, t_cap_disp;
  rewrite d01_zero by lia; reflexivity.

Ltac d01_val :=
  first [ reflexivity
        | etransitivity; [apply d01_m16 | reflexivity]
        | etransitivity; [apply d01_m32 | reflexivity]
        | etransitivity; [apply d01_m40 | reflexivity]
        | etransitivity; [apply d01_m64 | reflexivity]
        | d01_z
        | f_equal; unfold t_fam_raw, t_in, t_out, t_row, t_cap_fw, t_cap_ver, t_cap_name, t_cap_tok, t_cap_disp;
          rewrite d01_zero by lia; rewrite ?Zmod_0_l; lia ].

Ltac d01_reg := d01_getr; simp_regs; d01_val.

Ltac d01_splits :=
  lazymatch goal with
  | |- _ /\ _ => split; [d01_reg | d01_splits]
  | _ => d01_reg
  end.

Ltac d1_addr := first [ reflexivity | f_equal; lia ].

Ltac d1_mem :=
  apply d1_wtm; [apply d1_wtm; [reflexivity | d1_addr | f_equal; d01_val] | d1_addr | f_equal; d01_val].

Ltac d1_rds m p inp RD k :=
  let H := fresh "HR" in
  assert (H : ov_read_bytes rsegs m (wa (p + cT inp + k)) 1 =
              Some [RcIdentModel.nthb inp (Z.to_nat (cT inp + k))]) by (apply RD; lia).

Ltac d01_tr :=
  repeat match goal with
  | |- Exec.evt _ _ (MS _ _ _ _ _ (write_to_mem ?m (Z_to_bv 64 ?a) (le8 ?v)) _) =>
      match goal with H : ov_read_bytes rsegs m (wa _) 1 = Some _ |- _ =>
        apply (d01_rdw m a v) in H; [| lia | lia | lia | lia] end
  end.

Ltac d1_st sp :=
  lazymatch goal with
  | |- Exec.evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with
    | _ : store_ok rsegs mm (wa (sp + 48)) 8 = true |- _ => idtac
    | _ =>
      lazymatch mm with
      | write_to_mem ?m0 ?a ?bs =>
          lazymatch goal with
          | W0 : wr_at rsegs m0 sp 384 |- _ =>
              let W1 := fresh "W" in
              assert (W1 : wr_at rsegs mm sp 384) by (apply wr_at_write; exact W0);
              pose proof (wr_at_store_ok rsegs mm sp 384 48 8 W1 ltac:(lia) ltac:(lia));
              pose proof (wr_at_store_ok rsegs mm sp 384 56 8 W1 ltac:(lia) ltac:(lia))
          end
      | _ => idtac
      end
    end
  end.

Ltac d1_brk :=
  lazymatch goal with
  | |- Exec.evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
      first [ match goal with
              | |- context [bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 ?k)] =>
                  first [ rewrite (d01_ne x k) by lia | rewrite (d01_eq x k) by lia ]
              end
            | match goal with
              | |- context [bv_ltu (Z_to_bv 64 1) (Z_to_bv 64 ?y)] => rewrite (d1_ltu1 y) by lia
              end ]
  end.

Ltac d1_go sp :=
  repeat (d01_tr; d1_st sp;
    lazymatch goal with
    | |- Exec.evt _ _ (MS _ _ (Z_to_bv 64 79748) _ _ _ _) => fail
    | |- Exec.evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => step
    | |- Exec.evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => d1_brk; cbv beta iota delta [negb]
    end).

Ltac d1_fin :=
  apply evt_done; do 3 eexists; split; [reflexivity|];
  unfold d1_K; split; [reflexivity|]; split; [d1_mem|]; d01_splits.

Section KA.
Context {fx : lib.Reusable.YK11.FPState}.

Lemma D01_x : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (m : word -> option byte) (sp p : Z) (inp : list byte),
  x2 = Z_to_bv 64 sp -> x26 = Z_to_bv 64 (p + cT inp) -> x25 = Z_to_bv 64 (nlen inp - cT inp) ->
  0 <= cT inp <= nlen inp -> (nlen inp - cT inp = 0 \/ 4096 <= p) -> 0 <= p -> p + nlen inp <= sp ->
  0 <= sp -> sp + 384 <= 2 ^ 64 -> wr_at rsegs m sp 384 ->
  (forall k, 0 <= k < nlen inp - cT inp ->
     ov_read_bytes rsegs m (wa (p + cT inp + k)) 1 = Some [RcIdentModel.nthb inp (Z.to_nat (cT inp + k))]) ->
  Exec.evt rsegs
    (fun ms => exists R pc' m', ms = MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
       d1_K x2 x3 x4 sp inp m R pc' m')
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31)
        fp_regs (Z_to_bv 64 0x13704) fp_csr None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 m sp p inp E2 E26 E25 Hc Hp Hp0 Hpn Hsp Hsp2 WR RD.
  subst x2 x26 x25.
  pose proof (wr_at_store_ok rsegs m sp 384 48 8 WR ltac:(lia) ltac:(lia)) as HS48.
  pose proof (wr_at_store_ok rsegs m sp 384 56 8 WR ltac:(lia) ltac:(lia)) as HS56.
  assert (Hcases : nlen inp - cT inp <= 10 \/ 11 <= nlen inp - cT inp) by lia.
  destruct Hcases as [E|E].
  - assert (Hk : nlen inp - cT inp = 0 \/ nlen inp - cT inp = 1 \/ nlen inp - cT inp = 2 \/
                 nlen inp - cT inp = 3 \/ nlen inp - cT inp = 4 \/ nlen inp - cT inp = 5 \/
                 nlen inp - cT inp = 6 \/ nlen inp - cT inp = 7 \/ nlen inp - cT inp = 8 \/
                 nlen inp - cT inp = 9 \/ nlen inp - cT inp = 10) by lia.
    clear E.
    destruct Hk as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]];
      try (destruct Hp as [Hp|Hp]; [exfalso; lia|]);
      try d1_rds m p inp RD 0; try d1_rds m p inp RD 1; try d1_rds m p inp RD 2;
      try d1_rds m p inp RD 3; try d1_rds m p inp RD 4; try d1_rds m p inp RD 5;
      try d1_rds m p inp RD 6; try d1_rds m p inp RD 7; try d1_rds m p inp RD 8;
      try d1_rds m p inp RD 9.
    all: d1_go sp; d1_fin.
  - destruct Hp as [Hp|Hp]; [exfalso; lia|].
    d1_rds m p inp RD 0. d1_rds m p inp RD 1. d1_rds m p inp RD 2. d1_rds m p inp RD 3.
    d1_rds m p inp RD 4. d1_rds m p inp RD 5. d1_rds m p inp RD 6. d1_rds m p inp RD 7.
    d1_rds m p inp RD 8. d1_rds m p inp RD 9. d1_rds m p inp RD 10.
    d1_go sp. d1_fin.
Qed.

End KA.

Section D01.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.

Lemma seg_D01 : Hcut B APIf ra (Inv_U13784 B APIf ra empty) -> Hcut B APIf ra (Inv_U13704 B APIf ra empty).
Proof.
  intros HX g c (L & A & regs & mem & md & -> & HF & HP & HCUR & HTID & HFAM).
  pose proof (uf_segs B APIf ra empty FF) as SEG.
  pose proof HF as (HGV & Hsp & Hgp & Htp & Hsv & Hstk & HMI & Hrel & HMR & HWF & HBD & HIN & Hmd & Hhi & Himg & HB0
    & Her & Hsk & HRS & Hwin).
  pose proof HGV as (Hn & Hpd & Hbd & HS16 & HSc & HS47 & Hroom & HgS & HgT & HPB).
  destruct (uf_stk_fsp B APIf ra empty g _ _ L A regs mem md HF) as (ST & HI & HL & Hfs & HSc' & HS47' & HK & _).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_val rc) as HAC.
  destruct (mr_model B _ (aa_laws (APIf rc)) L A mem md HMR) as (Hh & Hl & _).
  destruct HCUR as (Hc0 & H26 & H25).
  assert (Hgn : g_n g = nlen (g_in g)) by reflexivity.
  assert (WR : wr_at rsegs mem (fsp g) 384).
  { split; [lia|]. split; [lia|]. intros i Hi. pose proof (Hwin (fsp g + i) ltac:(lia)) as W.
    rewrite SEG in W. exact W. }
  assert (RDI : forall j, 0 <= j < nlen (g_in g) -> mbyte rsegs mem (g_p g + j) = nth_error (g_in g) (Z.to_nat j)).
  { intros j Hj. destruct Hpd as [(Hn0 & _)|(Hnp & Hin)]; [lia|].
    rewrite <- SEG. rewrite (HB0 _ _ j Hin ltac:(lia)). apply Hbd. unfold nlen in Hj. lia. }
  eapply (uf_kA_run0 B APIf ra empty FF regs (Z_to_bv 64 0x13704) mem md); [exact Hh | exact Hl | |].
  { unfold mkR_of.
    pose proof FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & EMP & _).
    apply (D01_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem (fsp g) (g_p g) (g_in g)).
    - rewrite <- (uf_getr_reg regs 2) by reflexivity. exact Hsp.
    - rewrite <- (uf_getr_reg regs 26) by reflexivity. exact H26.
    - rewrite <- (uf_getr_reg regs 25) by reflexivity. exact H25.
    - lia.
    - destruct HPB as [Z0|(P1 & P2)]; [left; lia | right; lia].
    - destruct Hpd as [(Hn0 & Hpe)|(Hnp & _)]; [rewrite Hpe, EMP; lia | destruct HPB as [Z0|(P1 & P2)]; lia].
    - destruct Hpd as [(Hn0 & Hpe)|(Hnp & _)]; [rewrite Hpe, EMP; lia | destruct HPB as [Z0|(P1 & P2)]; lia].
    - lia.
    - lia.
    - exact WR.
    - intros k Hk. rewrite <- Z.add_assoc. apply d1_rdin; [exact RDI | lia]. }
  intros R pc' m' regs1 (-> & -> & K2 & K3 & K4 & K24 & K9 & K25 & K27 & K19 & K20 & K21 & K11 & K10) XR.
  assert (GR : forall (r : bv 5) v, getr R r = v -> is_x0 r = false -> getr regs1 r = v).
  { intros r v H H0. rewrite (uf_getr_x _ _ r XR H0). rewrite <- (uf_getr_reg R r H0). exact H. }
  set (m1 := write_to_mem mem (Z_to_bv 64 (fsp g + 56)) (le8 (Z_to_bv 64 (t_out (g_in g))))).
  set (m2 := write_to_mem m1 (Z_to_bv 64 (fsp g + 48)) (le8 (Z_to_bv 64 (t_row (g_in g))))).
  assert (MU : munch [(fsp g + 48, fsp g + 64)] mem m2).
  { unfold m2. apply munch_write; [| lia | rewrite length_le8; lia |].
    - unfold m1. apply munch_write; [apply munch_refl | lia | rewrite length_le8; lia |].
      rewrite length_le8. cbn [Frame.inside]. lia.
    - rewrite length_le8. cbn [Frame.inside]. lia. }
  assert (WM : wmono rsegs mem m2) by (unfold m2, m1; apply wmono_write; apply wmono_write; apply wmono_refl).
  assert (BT : forall a bs, bytes_at rsegs mem a bs -> (a + Z.of_nat (length bs) <= fsp g + 48 \/ fsp g + 64 <= a) ->
                 bytes_at rsegs m2 a bs).
  { intros a bs Hb Hd. pose proof Hb as (B1 & B2 & _). unfold m2, m1.
    apply bytes_at_write_other; [apply bytes_at_write_other; [exact Hb | lia | rewrite length_le8; lia |] | lia |
      rewrite length_le8; lia |]; rewrite length_le8; lia. }
  apply HX. exists L, A, regs1, m2, md. split; [reflexivity|].
  split.
  { apply (uf_FR_munch B APIf ra empty FF g _ _ L A regs mem md regs1 m2 _ HF HP
             (GR _ _ K2 eq_refl) (GR _ _ K3 eq_refl) (GR _ _ K4 eq_refl) MU WM).
    intros lo hi y Hy Hr. destruct Hy as [Hy|[]]. injection Hy as <- <-. left. lia. }
  split; [exact HP|].
  pose proof HTID as (HG24 & HID).
  split.
  { split; [unfold G24, q64, spk in *; apply BT; [exact HG24 | rewrite length_le8; lia]|].
    unfold IDb, spk in *. apply BT; [exact HID | rewrite rec_id_length; unfold RcIdentModel.ID_SIZE; lia]. }
  split.
  { split; [exact (GR _ _ K24 eq_refl)|]. split; [exact (GR _ _ K9 eq_refl)|].
    split.
    { unfold q64, spk, m2, m1. apply bytes_at_write_other; [apply bytes_at_write_same; rewrite ?length_le8; lia | lia |
        rewrite length_le8; lia | rewrite !length_le8; lia]. }
    split.
    { unfold q64, spk, m2. apply bytes_at_write_same; rewrite ?length_le8; lia. }
    split; [exact (GR _ _ K25 eq_refl)|]. split; [exact (GR _ _ K27 eq_refl)|]. exact (GR _ _ K19 eq_refl). }
  split; [exact (GR _ _ K20 eq_refl)|]. split; [exact (GR _ _ K21 eq_refl)|].
  split; [exact (GR _ _ K11 eq_refl) | exact (GR _ _ K10 eq_refl)].
Qed.

End D01.
