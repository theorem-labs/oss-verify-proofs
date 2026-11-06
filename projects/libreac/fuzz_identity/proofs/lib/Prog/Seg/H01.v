From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac ZBridge Image.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0 MemNorm FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel put_dec_c reac_box_family_stem_c reac_box_family_stem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Import Tac_sh1.
Import ListNotations.
Open Scope Z_scope.

Local Ltac OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib.Step.mem_after_store_opt ::= idtac.

Definition wokb (i o : Z) : Z := if okw i && okw o && negb ((i =? 0) && (o =? 0)) then 1 else 0.
Definition WH01 (S0 : Z) : list ivl :=
  [(S0 + 16, S0 + 24); (S0 + 48, S0 + 49); (S0 + 168, S0 + 176); (S0 + 200, S0 + 208); (S0 + 226, S0 + 227)].
Definition stemA (S0 hmn mn0 fam : Z) : Z :=
  if negb (hmn =? 0) && negb (mn0 =? 0) then S0 + 133 else STEM_Addr fam.
Definition qw (m : word -> option byte) (a v : Z) : Prop := bytes_at rsegs m a (le8 (Z_to_bv 64 v)).

Lemma r_ok_branch : forall r, r = 0 \/ r = -1 ->
  negb (bv_ltu (Z_to_bv 64 (-3)) (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 r) + -1)))) = false.
Proof. intros r [-> | ->]; vm_compute; reflexivity. Qed.

Lemma lor_small : forall i o, 0 <= i < 256 -> 0 <= o < 256 -> 0 <= Z.lor i o < 256.
Proof.
  intros i o Hi Ho.
  assert (H : z_all (fun i => z_all (fun o => (0 <=? Z.lor i o) && (Z.lor i o <? 256)) 256 0) 256 0 = true)
    by (vm_compute; reflexivity).
  pose proof (z_all_spec _ _ _ H i ltac:(lia)) as H1. cbv beta in H1.
  pose proof (z_all_spec _ _ _ H1 o ltac:(lia)) as H2. cbv beta in H2.
  apply andb_prop in H2 as [H3 H4]. apply Z.leb_le in H3. apply Z.ltb_lt in H4. lia.
Qed.

Lemma snez_or : forall i o, 0 <= i < 256 -> 0 <= o < 256 ->
  v_sltu (Z_to_bv 64 0) (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 i)) (bv_unsigned (Z_to_bv 64 o)))) =
  Z_to_bv 64 (if (i =? 0) && (o =? 0) then 0 else 1).
Proof.
  intros i o Hi Ho. rewrite (unsigned_lit i), (unsigned_lit o) by lia.
  pose proof (lor_small i o Hi Ho) as HL.
  unfold v_sltu, c_ltu, bv_ltu. rewrite (unsigned_lit 0), (unsigned_lit (Z.lor i o)) by lia.
  destruct (Z.eqb_spec i 0) as [->|Hi0]; destruct (Z.eqb_spec o 0) as [->|Ho0]; cbn [andb].
  - reflexivity.
  - assert (Z.lor 0 o <> 0) by (rewrite Z.lor_eq_0_iff; lia). destruct (Z.ltb_spec 0 (Z.lor 0 o)); [reflexivity|lia].
  - assert (Z.lor i 0 <> 0) by (rewrite Z.lor_eq_0_iff; lia). destruct (Z.ltb_spec 0 (Z.lor i 0)); [reflexivity|lia].
  - assert (Z.lor i o <> 0) by (rewrite Z.lor_eq_0_iff; lia). destruct (Z.ltb_spec 0 (Z.lor i o)); [reflexivity|lia].
Qed.

Lemma even_land1 : forall x, 0 <= x -> Z.even x = (Z.land x 1 =? 0).
Proof.
  intros x Hx. change (Z.land x 1) with (Z.land x (Z.ones 1)). rewrite (Z.land_ones x 1) by lia. change (2 ^ 1) with 2.
  pose proof (Z.div_mod x 2 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 2 ltac:(lia)) as Bd.
  rewrite D at 1. rewrite Z.even_add, Z.even_mul. cbn [Z.even orb].
  assert (C : x mod 2 = 0 \/ x mod 2 = 1) by lia. destruct C as [C|C]; rewrite C; reflexivity.
Qed.

Lemma land1_mod : forall x, Z.land x 1 = x mod 2.
Proof. intros x. change (Z.land x 1) with (Z.land x (Z.ones 1)). rewrite Z.land_ones by lia. reflexivity. Qed.

Ltac wsolve i o :=
  rewrite ?land1_mod in *;
  unfold wokb, okw; rewrite ?(even_land1 i), ?(even_land1 o) by lia; rewrite ?land1_mod;
  repeat match goal with
  | |- context [Z.eqb ?x ?y] => destruct (Z.eqb_spec x y)
  | |- context [Z.leb ?x ?y] => destruct (Z.leb_spec x y)
  end; cbn [andb orb negb]; lia.

Ltac wclose i o :=
  apply evt_done; do 2 eexists; split; [reflexivity|];
  rewrite ?snez_or by lia; f_equal; wsolve i o.

Lemma h01_a : forall (x1 x3 x4 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25
    x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (S0 i o r hmn fam : Z),
  0 <= i < 256 -> 0 <= o < 256 -> (r = 0 \/ r = -1) ->
  Exec.evt rsegs (fun s => exists y10 y11 : word,
    s = MS (mkR x1 (Z_to_bv 64 S0) x3 x4 x5 x6 x7 (Z_to_bv 64 hmn) (Z_to_bv 64 i) y10 y11 x12 x13 x14 x15 x16 x17
                (Z_to_bv 64 o) x19 x20 x21 x22 x23 x24 (Z_to_bv 64 r) (Z_to_bv 64 fam) x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x13808) fc None m (seg_rom rsegs) /\ y10 = Z_to_bv 64 (wokb i o))
    (MS (mkR x1 (Z_to_bv 64 S0) x3 x4 x5 x6 x7 (Z_to_bv 64 hmn) (Z_to_bv 64 i) (Z_to_bv 64 r) x11 x12 x13 x14 x15
             x16 x17 (Z_to_bv 64 o) x19 x20 x21 x22 x23 x24 x25 (Z_to_bv 64 fam) x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x137c0) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x3 x4 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25
    x27 x28 x29 x30 x31 F fc m S0 i o r hmn fam Hi Ho Hr.
  step. step. step. step. if_false_by (r_ok_branch r Hr).
    step. if_cases Hc1; zify_cond Hc1.
    - step. if_cases Hc2; zify_cond Hc2.
      + step. step. wclose i o.
      + step. step. step. if_cases Hc3; zify_cond Hc3.
        * wclose i o.
        * step. step. if_cases Hc4; zify_cond Hc4.
          -- wclose i o.
          -- step. step. wclose i o.
    - step. step. step. if_cases Hc5; zify_cond Hc5.
      + wclose i o.
      + step. step. if_cases Hc6; zify_cond Hc6.
        * wclose i o.
        * step. if_cases Hc2; zify_cond Hc2.
          -- step. step. wclose i o.
          -- step. step. step. if_cases Hc3; zify_cond Hc3.
             ++ wclose i o.
             ++ step. step. if_cases Hc4; zify_cond Hc4.
                ** wclose i o.
                ** step. step. wclose i o.
Qed.

Lemma u8_lit : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.

Ltac stem_fin S0 HSA :=
  apply evt_done; do 4 eexists; split; [reflexivity|]; split; [eassumption|]; split; [eassumption|];
  unfold qw; rewrite HSA;
  match goal with
  | NW : bytes_at rsegs ?mm (S0 + 16) (le8 ?w) |- bytes_at rsegs ?mm (S0 + 16) _ =>
      eapply bytes_at_ext; [exact NW|]; f_equal; apply bv_eq; vm_compute; reflexivity
  end.

Ltac stemof S0 fam HSA :=
  step; step; step;
  let Hc := fresh "Hc" in
  assert (Hc : fam = 1 \/ fam = 2 \/ fam = 3 \/ ~ (1 <= fam <= 3)) by lia;
  let Ef := fresh "Ef" in let Hn := fresh "Hn" in
  destruct Hc as [Ef | [Ef | [Ef | Hn]]];
  [ subst fam; if_false;
    match goal with T : bytes_at rsegs ?mm 0x105cc _ |- _ => pose proof (rd_all _ _ _ T) as RT; rewrite length_le4 in RT end;
    step; step; step; step; step; step; step; st_ok (S0 + 16) 8%nat; step; after_st; stem_fin S0 HSA
  | subst fam; if_false;
    match goal with T : bytes_at rsegs ?mm 0x105d0 _ |- _ => pose proof (rd_all _ _ _ T) as RT; rewrite length_le4 in RT end;
    step; step; step; step; step; step; step; st_ok (S0 + 16) 8%nat; step; after_st; stem_fin S0 HSA
  | subst fam; if_false;
    match goal with T : bytes_at rsegs ?mm 0x105d4 _ |- _ => pose proof (rd_all _ _ _ T) as RT; rewrite length_le4 in RT end;
    step; step; step; step; step; step; step; st_ok (S0 + 16) 8%nat; step; after_st; stem_fin S0 HSA
  | if_true_by (stem_bltu fam ltac:(lia) Hn); step; step; st_ok (S0 + 16) 8%nat; step; after_st;
    rewrite (STEM_Addr_other fam Hn) in HSA; stem_fin S0 HSA ].

Lemma h01_run : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (S0 i o r hmn mn0 fam : Z),
  x2 = Z_to_bv 64 S0 -> x9 = Z_to_bv 64 i -> x18 = Z_to_bv 64 o -> x10 = Z_to_bv 64 r ->
  x8 = Z_to_bv 64 hmn -> x26 = Z_to_bv 64 fam ->
  LOWTOP <= S0 -> S0 + 368 <= 2 ^ 64 -> 0 <= i < 256 -> 0 <= o < 256 -> 0 <= hmn < 256 -> 0 <= mn0 < 256 ->
  0 <= fam < 128 -> (r = 0 \/ r = -1) -> (r = 0 -> wokb i o = 1) ->
  wr_at rsegs m S0 264 -> bytes_at rsegs m (S0 + 133) [Z_to_bv 8 mn0] -> qw m (S0 + 16) (S0 + 133) ->
  bytes_at rsegs m 0x105cc (le4 (Z_to_bv 64 (-764))) -> bytes_at rsegs m 0x105d0 (le4 (Z_to_bv 64 (-552))) ->
  bytes_at rsegs m 0x105d4 (le4 (Z_to_bv 64 (-227))) ->
  Exec.evt rsegs
    (fun ms' => exists m' (y10 y11 y26 : word), mfr (WH01 S0) m m' /\
       ((wokb i o = 0 /\ r = -1 /\
         ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 y10 y11 x12 x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 r) x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x13b18) fc None m' (seg_rom rsegs)) \/
        (wokb i o = 1 /\
         ms' = MS (mkR (Z_to_bv 64 0x138bc) x2 x3 x4 x5 x6 x7 (Z_to_bv 64 (S0 + 176)) x9 (Z_to_bv 64 (S0 + 176))
                       (Z_to_bv 64 (S0 + 200)) x9 (Z_to_bv 64 2) x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 r) y26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 PUT_DEC) fc None m' (seg_rom rsegs) /\
         wr_at rsegs m' S0 264 /\ qw m' (S0 + 16) (stemA S0 hmn mn0 fam) /\ qw m' (S0 + 200) 0 /\
         qw m' (S0 + 168) 0)))
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31)
        F (Z_to_bv 64 0x137c0) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 F fc m S0 i o r hmn mn0 fam E2 E9 E18 E10 E8 E26 HS0 HS1 Hi Ho Hh Hmn Hf Hr Hw
    WR HM G16 T1 T2 T3.
  subst x2 x9 x18 x10 x8 x26.
  eapply evt_cut; [apply h01_a; assumption|].
  intros s (y10 & y11 & -> & ->).
  assert (HW : wokb i o = 0 \/ wokb i o = 1) by (unfold wokb; destruct (_ && _ && _); auto).
  eapply (evt_cut rsegs (fun s => exists y11 : word,
    s = MS (mkR x1 (Z_to_bv 64 S0) x3 x4 x5 x6 x7 (Z_to_bv 64 hmn) (Z_to_bv 64 i) (Z_to_bv 64 (wokb i o)) y11
                x12 x13 x14 x15 x16 x17
                (Z_to_bv 64 o) x19 x20 x21 x22 x23 x24 (Z_to_bv 64 r) (Z_to_bv 64 fam) x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x13814) fc None m (seg_rom rsegs))).
  { destruct Hr as [-> | ->].
    - rewrite (Hw eq_refl). step. step. if_false. step. if_false. apply evt_done. eexists. reflexivity.
    - step. step. if_true. apply evt_done. eexists. reflexivity. }
  intros s (y11' & ->).
  unfold qw in G16.
  pose proof (mfr_refl [(S0 + 16, S0 + 24); (S0 + 48, S0 + 49); (S0 + 168, S0 + 176); (S0 + 200, S0 + 208);
                        (S0 + 226, S0 + 227)] m) as MF.
  st_ok (S0 + 48) 1%nat. step. after_st.
  st_ok (S0 + 226) 1%nat. step. after_st.
  step. destruct HW as [HW|HW]; rewrite HW.
  - if_true. apply evt_done. exists m1. do 3 eexists. split; [exact MF|].
    left. split; [reflexivity|]. split; [destruct Hr as [->| ->]; [rewrite (Hw eq_refl) in HW; discriminate|reflexivity]|].
    reflexivity.
  - if_false.
    eapply (evt_cut rsegs (fun s => exists (y10 y11 y26 : word) m',
       s = MS (mkR x1 (Z_to_bv 64 S0) x3 x4 x5 x6 x7 (Z_to_bv 64 hmn) (Z_to_bv 64 i) y10 y11 x12 x13 x14 x15 x16 x17
                   (Z_to_bv 64 o) x19 x20 x21 x22 x23 x24 (Z_to_bv 64 r) y26 x27 x28 x29 x30 x31)
              F (Z_to_bv 64 0x1389c) fc None m' (seg_rom rsegs) /\
       mfr [(S0 + 16, S0 + 24); (S0 + 48, S0 + 49); (S0 + 168, S0 + 176); (S0 + 200, S0 + 208);
            (S0 + 226, S0 + 227)] m m' /\ wr_at rsegs m' S0 264 /\ qw m' (S0 + 16) (stemA S0 hmn mn0 fam))).
    { step. if_cases Hd1; zify_cond Hd1.
      - assert (HSA : stemA S0 hmn mn0 fam = STEM_Addr fam) by (unfold stemA; rewrite Hd1; reflexivity).
        stemof S0 fam HSA.
      - pose proof (rd_b1 _ _ _ HM) as RD. step. step. if_cases Hd2; zify_cond Hd2;
          rewrite (unsigned_lit (bv_unsigned (Z_to_bv 8 mn0))), u8_lit in Hd2 by (rewrite ?u8_lit; lia).
        + apply evt_done. do 4 eexists. split; [reflexivity|]. split; [exact MF|]. split; [exact WR|].
          unfold qw, stemA. rewrite (proj2 (Z.eqb_neq hmn 0) Hd1), (proj2 (Z.eqb_neq mn0 0) Hd2). exact G16.
        + assert (HSA : stemA S0 hmn mn0 fam = STEM_Addr fam)
            by (unfold stemA; rewrite Hd2; cbn [Z.eqb negb]; rewrite andb_false_r; reflexivity).
          stemof S0 fam HSA. }
    intros s (z10 & z11 & z26 & m2 & -> & MF2 & WR2 & HQ2). unfold qw in HQ2.
    clear dependent m1.
    st_ok (S0 + 200) 8%nat. step. after_st.
    st_ok (S0 + 168) 8%nat. step. after_st.
    step. step. step. step. step. step.
    apply evt_done. do 4 eexists. split; [unfold WH01; eassumption|]. right. split; [reflexivity|].
    split; [reflexivity|]. split; [eassumption|]. unfold qw. split; [eassumption|]. split; eassumption.
Unshelve. all: exact (Z_to_bv 64 0).
Qed.
From Stdlib Require Import Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Contract KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import RcIdentModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import URzP.

Ltac djt := unfold WH01, PUT_DEC_FRAME; cbn [disjoint_from]; rewrite ?length_le8, ?length_app; cbn [length];
  repeat match goal with H : length _ = _ |- _ => rewrite H end; unfold ID_SIZE; repeat split; lia.

Ltac outlo := let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; unfold WH01, PUT_DEC_FRAME in Hx; cbn [outside] in Hx; lia.

Section H01.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis PD : put_dec_contract.

Lemma seg_H01 :
  Hcut B APIf ra (Inv_K138bc B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13b18 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K137c0 B APIf ra empty).
Proof.
  intros H8bc H18 g c (nm & tk & dp & Hc).
  destruct Hc as (L & A & regs & mem & md & -> & HF & HP & HG & H10 & HO).
  destruct HG as ((HG16 & HID) & H8 & H9 & H18' & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 &
                  HC40 & HC0 & HC8).
  destruct (s1_frame_facts B APIf ra empty FF _ _ _ _ _ _ _ _ HF) as (HLO & HHI & H16 & HRO & HWR & HSTK & Hsp).
  pose proof HF as (HGV & _ & Hgp & Htp & _ & _ & _ & _ & HMR & _).
  unfold IDb, G16, q64, spk in *.
  set (S0 := fsp g) in *.
  set (inp := g_in g) in *.
  pose proof (rec_id_length inp (NRn g)) as HIL.
  pose proof (inb_range inp (cT inp + 1)) as Ri. pose proof (inb_range inp (cT inp + 2)) as Ro.
  change (inb inp (cT inp + 1)) with (t_in inp) in Ri. change (inb inp (cT inp + 2)) with (t_out inp) in Ro.
  pose proof (bz_range (nthb (rec_id inp (NRn g)) 20)) as Rh.
  pose proof (bz_range (nthb (rec_id inp (NRn g)) 3)) as Rm.
  pose proof (n_fam_range inp) as Rf.
  assert (HM : bytes_at rsegs mem (S0 + 133) [Z_to_bv 8 (bz (nthb (rec_id inp (NRn g)) 3))]).
  { rewrite zb_bz. pose proof (s1_bytes_sub mem (S0 + 130) _ 3 HID ltac:(rewrite HIL; unfold ID_SIZE; lia)) as X.
    replace (S0 + 130 + Z.of_nat 3) with (S0 + 133) in X by lia. exact X. }
  assert (HAC : alloc_ceiling + 16016 <= S0)
    by (destruct HGV as (_ & _ & _ & _ & HSK & _); unfold S0, fsp, SLOT_FRAME; unfold SLOT_K, SLOT_STACK in HSK; lia).
  pose proof (n_r_cases inp) as Hr01.
  assert (Hrw : n_r inp = 0 -> wokb (t_in inp) (t_out inp) = 1).
  { intros H0. destruct (n_r_zero inp H0) as [Hw _]. unfold wokb. unfold n_wok in Hw. rewrite Hw. reflexivity. }
  assert (Hwk : wokb (t_in inp) (t_out inp) = if n_wok inp then 1 else 0) by reflexivity.
  pose proof (wr_sub mem _ _ S0 264 HWR ltac:(lia) ltac:(lia) ltac:(lia)) as WR0.
  assert (T1 : bytes_at rsegs mem 0x105cc (le4 (Z_to_bv 64 (-764))))
    by (apply s1_img_bytes; [exact HRO | lia | rewrite length_le4; lia | vm_compute; reflexivity]).
  assert (T2 : bytes_at rsegs mem 0x105d0 (le4 (Z_to_bv 64 (-552))))
    by (apply s1_img_bytes; [exact HRO | lia | rewrite length_le4; lia | vm_compute; reflexivity]).
  assert (T3 : bytes_at rsegs mem 0x105d4 (le4 (Z_to_bv 64 (-227))))
    by (apply s1_img_bytes; [exact HRO | lia | rewrite length_le4; lia | vm_compute; reflexivity]).
  assert (HSA : stemA S0 (has_model_name (idT inp)) (bz (nthb (rec_id inp (NRn g)) 3)) (n_fam inp) = stem_addr g).
  { unfold stemA, stem_addr, n_use_said, n_said, spk. fold S0. fold inp.
    rewrite (nthb_mn0 (idT inp) HIL). reflexivity. }
  assert (HSP : (stem_addr g = S0 + 133 /\ (length (n_stem inp) <= 16)%nat) \/
                (0 <= stem_addr g /\ stem_addr g + 8 <= LOWTOP /\ (length (n_stem inp) <= 7)%nat)).
  { unfold stem_addr, n_stem, spk. fold S0. fold inp. destruct (n_use_said inp).
    - left. split; [reflexivity | apply name_str_len].
    - right. pose proof (stem_img_len (n_fam inp)). unfold STEM_Addr.
      destruct (n_fam inp =? 1); [|destruct (n_fam inp =? 2); [|destruct (n_fam inp =? 3)]]; lia. }
  assert (HCS : cstr mem (stem_addr g) (n_stem inp)).
  { unfold stem_addr, n_stem, spk. fold S0. fold inp. destruct (n_use_said inp).
    - replace (S0 + 133) with (S0 + 130 + 3) by lia. apply name_cstr; [exact HID | exact HIL | apply rec_id_b19].
    - unfold cstr. replace (stem_img (n_fam inp) ++ [z8]) with (STEM (n_fam inp)) by reflexivity.
      apply bytes_at_ro_agree; [exact HRO | | | apply STEM_ro].
      + unfold STEM_Addr. destruct (n_fam inp =? 1); [|destruct (n_fam inp =? 2); [|destruct (n_fam inp =? 3)]]; lia.
      + unfold STEM_Addr, STEM, STEM_cstr. rewrite length_app, length_map.
        destruct (n_fam inp =? 1); [|destruct (n_fam inp =? 2); [|destruct (n_fam inp =? 3)]]; cbn; lia. }
  apply (s1_run B APIf ra empty FF regs (Z_to_bv 64 0x137c0) mem md L A
    (fun R pc' mem' =>
       getr R 2 = Z_to_bv 64 S0 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 9 = Z_to_bv 64 (t_in inp) /\ getr R 18 = Z_to_bv 64 (t_out inp) /\
       getr R 19 = Z_to_bv 64 (t_row inp) /\
       getr R 20 = Z_to_bv 64 nm /\ getr R 21 = Z_to_bv 64 tk /\ getr R 22 = Z_to_bv 64 dp /\
       getr R 23 = Z_to_bv 64 (t_cap_tok inp) /\ getr R 24 = Z_to_bv 64 (t_cap_name inp) /\
       getr R 25 = Z_to_bv 64 (n_r inp) /\ getr R 27 = Z_to_bv 64 (t_cap_disp inp) /\
       mfr [(S0 - 64, S0 + 264)] mem mem' /\ bytes_at rsegs mem' (S0 + 130) (rec_id inp (NRn g)) /\
       bytes_at rsegs mem' (S0 + 40) (le8 (Z_to_bv 64 (t_cap_disp inp))) /\ OUTS g nm tk dp mem' /\
       ((pc' = Z_to_bv 64 0x13b18 /\ n_wok inp = false) \/
        (pc' = Z_to_bv 64 0x138bc /\ n_wok inp = true /\ getr R 8 = Z_to_bv 64 (S0 + 176) /\
         bytes_at rsegs mem' (S0 + 16) (le8 (Z_to_bv 64 (stem_addr g))) /\ cstr mem' (stem_addr g) (n_stem inp) /\
         bytes_at rsegs mem' (S0 + 200) (le8 (Z_to_bv 64 2)) /\
         bytes_at rsegs mem' (S0 + 168) (le8 (Z_to_bv 64 0)) /\
         bytes_at rsegs mem' (S0 + 176) (DEC (t_in inp) 2)))) _ HMR).
  - unfold rmk. rewrite Hsp, H9, H18', H19, H20, H21, H22, H23, H24, H10, H8, H26, H27.
    eapply Exec.evt_cut.
    { eapply (h01_run _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fp_regs fp_csr mem S0
                (t_in inp) (t_out inp) (n_r inp) (has_model_name (idT inp)) (bz (nthb (rec_id inp (NRn g)) 3))
                (n_fam inp)); try reflexivity; try lia; try assumption. }
    intros ms (m1 & y10 & y11 & y26 & MF1 & [(HW0 & Hr & ->) | (HW1 & -> & WR1 & HQ16 & HQ200 & HQ168)]).
    + apply Exec.evt_done. do 3 eexists. split; [reflexivity|].
      repeat (split; [reflexivity|]).
      split; [eapply mfr_weaken; [exact MF1 | unfold WH01; subfp]|].
      split; [eapply mfr_bytes; [exact MF1 | exact HID | djt]|].
      split; [eapply mfr_bytes; [exact MF1 | exact HC40 | djt]|].
      split; [eapply (s1_OUTS B APIf); [exact HMR | exact HP | exact HO | exact MF1 | outlo]|].
      left. split; [reflexivity|]. rewrite Hwk in HW0. destruct (n_wok inp); [discriminate | reflexivity].
    + assert (Hwok : n_wok inp = true) by (rewrite Hwk in HW1; destruct (n_wok inp); [reflexivity | discriminate]).
      destruct (wok_chans inp Hwok) as [Hi40 Ho40].
      pose proof (DEC2_len _ Hi40) as HD2.
      assert (HDL : dec_len (t_in inp) 2 = 2) by (unfold dec_len; rewrite HD2; reflexivity).
      unfold qw in HQ16, HQ200, HQ168.
      eapply (pd_call PD) with (lo := S0 - 16016) (b := S0 + 176) (p := S0 + 200) (v := t_in inp) (mn := 2)
        (N := Z_to_bv 64 0); rewrite ?(unsigned_lit S0), ?(unsigned_lit 0), ?HDL by lia.
      * reflexivity.
      * reflexivity.
      * rewrite unsigned_lit by lia. apply Z.mod_small. lia.
      * left. rewrite unsigned_lit by lia. lia.
      * reflexivity.
      * lia.
      * exact HQ200.
      * eapply wr_sub; [exact WR1 | lia | lia | lia].
      * Z.div_mod_to_equations. lia.
      * eapply wr_sub; [exact WR1 | lia | lia | lia].
      * eapply mfr_ro; [exact HRO | exact MF1 | outlo].
      * destruct (stk_split rsegs m1 (S0 - 16016) S0 (S0 + 368) (mfr_stk _ _ _ _ _ MF1 HSTK) ltac:(lia)) as [X _].
        exact X.
      * unfold PUT_DEC_FRAME. lia.
      * lia.
      * lia.
      * lia.
      * lia.
      * lia.
      * lia.
      * unfold PUT_DEC_FRAME. lia.
      * unfold PUT_DEC_FRAME. lia.
      * intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 MF2 HRO2 HDEC HN.
        rewrite ?(unsigned_lit S0), ?(unsigned_lit 0), ?HDL, ?Z.add_0_r, ?Z.add_0_l in * by lia.
        retpc.
        assert (MFa : mfr [(S0 - 64, S0 + 264)] mem m1) by (eapply mfr_weaken; [exact MF1 | unfold WH01; subfp]).
        assert (MFb : mfr [(S0 - 64, S0 + 264)] m1 m2)
          by (eapply mfr_weaken; [exact MF2 | unfold PUT_DEC_FRAME; subfp]).
        apply Exec.evt_done. do 3 eexists. split; [reflexivity|].
        repeat (split; [reflexivity|]).
        split; [exact (mfr_trans _ _ _ _ MFa MFb)|].
        split; [eapply mfr_bytes; [exact MF2 | eapply mfr_bytes; [exact MF1 | exact HID | djt] | djt]|].
        split; [eapply mfr_bytes; [exact MF2 | eapply mfr_bytes; [exact MF1 | exact HC40 | djt] | djt]|].
        split.
        { eapply (s1_OUTS B APIf); [exact HMR | exact HP | | exact MF2 | outlo].
          eapply (s1_OUTS B APIf); [exact HMR | exact HP | exact HO | exact MF1 | outlo]. }
        right. split; [reflexivity|]. split; [exact Hwok|]. split; [reflexivity|].
        split; [rewrite <- HSA; eapply mfr_bytes; [exact MF2 | exact HQ16 | djt]|].
        split.
        { unfold cstr in *. destruct HSP as [(HA & HL) | (HA1 & HA2 & HL)].
          - rewrite HA in *. eapply mfr_bytes; [exact MF2 | eapply mfr_bytes; [exact MF1 | exact HCS | djt] | djt].
          - eapply mfr_bytes; [exact MF2 | eapply mfr_bytes; [exact MF1 | exact HCS | djt] | djt]. }
        split; [exact HN|].
        split; [eapply mfr_bytes; [exact MF2 | exact HQ168 | djt]|].
        exact HDEC.
  - intros R pc' mem' regs' (E2 & E3 & E4 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E27 & MFt &
                             HID' & HC40' & HO' & HX) Hg.
    assert (HF' : FR B APIf ra empty g (2 * NR g + 5) (NMB g nm tk dp) L A regs' mem' md).
    { apply (s1_FRx B APIf ra empty FF g _ _ L A regs regs' mem mem' md _ HF HP MFt).
      - unfold S0, fsp, SLOT_FRAME, SLOT_K, SLOT_STACK. subfp.
      - rewrite Hg, E2, Hsp. reflexivity.
      - rewrite Hg. exact E3.
      - rewrite Hg. exact E4. }
    destruct HX as [(-> & Hwf) | (-> & Hwt & E8 & HQ16' & HCS' & HQ200' & HQ168' & HDEC')].
    + apply H18. exists nm, tk, dp. apply (s1_cut B APIf ra empty g _ _ _ _ L A regs' mem' md HF' HP).
      unfold IRb, IDb, spk. fold S0. rewrite !Hg.
      split; [exact HID'|]. split; [exact E9|]. split; [exact E18|]. split; [exact E19|]. split; [exact E20|].
      split; [exact E21|]. split; [exact E22|]. split; [exact E23|]. split; [exact E24|]. split; [exact E25|].
      split; [exact E27|]. split; [exact HO'|].
      intros Hr0. destruct (n_r_zero inp Hr0) as [Hw _]. rewrite Hw in Hwf. discriminate.
    + apply H8bc. exists nm, tk, dp. apply (s1_cut B APIf ra empty g _ _ _ _ L A regs' mem' md HF' HP).
      unfold N0, NB, IDb, q64, spk. fold S0. rewrite !Hg.
      split; [|split; [exact E19|]; split; [exact E8|]; split; [exact HQ200'|]; split; [exact HQ168'|]; exact HDEC'].
      split; [|split; [exact E9|]; split; [exact E18|]; split; [exact HQ16'|]; exact HCS'].
      split; [exact HID'|]. split; [exact Hwt|]. split; [exact E20|]. split; [exact E21|]. split; [exact E22|].
      split; [exact E23|]. split; [exact E24|]. split; [exact E25|]. split; [exact HC40'|]. exact HO'.
Qed.


End H01.
