(* Segment S5 of the walk of reac_segconf_declared (fuzz_segconf.asan, image A): from the cut KX (0x89a78) to the
   `ret` at 0x89b50, given INV_KX, reaching dc_post (reac_segconf_declared_d.v dc_S5P).
   The stretch: frame[0] = 0x45e0360e (0x89a84); `beqz a1` at 0x89a8c not taken, a1 = 24(s1) = F >= 4096 (the
   frame's bound, frames_bounds), so the arm 0x89ae0-0x89b0c is not walked; the 16 shadow bytes of the frame = 0xf5
   (0x89a94-0x89ad0); the flag byte through frame[120] = 0 (0x89ad4-0x89ad8), which frees the frame
   (PaLibF.v aj_flag_store_pi); a0 = 56(s1); the 13 saved registers loaded back from sp0 - 8 .. sp0 - 104;
   sp = sp0; `ret` (SegPaLib.v paj_ret_at).
   The symbolic state at KX. Atoms 0..31 are the registers at KX (s1 = the realigned sp, s0 = sp0,
   s3 = SB + F / 8); 32 F, 33 FL (the frame's flag cell), 34 the result word (mod 2 ^ 64), 35 .. 47 the entry's
   ra, s0, s1, s2 .. s11 (dc_saved order). The regions: the flag cell (writable), the words of s1 at 16, 24, 56,
   the 13 saved words below sp0, the frame's word [F, F + 8) (writable), the frame's flag pointer at F + 120, the
   frame's 16 shadow bytes (writable). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YG0p YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaDenot PaSB PaLibG PaLibH PaLibF.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
reac_declared_vlan_split_c reac_declared_vlan_add_c reac_segconf_declared_c reac_segconf_declared_d SegInstA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the regions of the state at KX *)
Definition dcs5_flr : YP09.region := YP09.mkRegion (Some 33%nat) 0 1 0 1 [].
Definition dcs5_s1r : YP09.region := YP09.mkRegion (Some 9%nat) 16 64 0 0
  [YP09.mkChunk 16 (CVal 8 (SOff 32 0)); YP09.mkChunk 24 (CVal 8 (SOff 32 0)); YP09.mkChunk 56 (CVal 8 (SOff 34 0))].
Definition dcs5_svr : YP09.region := Eval vm_compute in
  YP09.mkRegion (Some 8%nat) (-104) 0 0 0
  (map (fun j => YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (35 + j) 0))) (seq 0 13)).
Definition dcs5_frh : YP09.region := YP09.mkRegion (Some 32%nat) 0 8 0 8 [].
Definition dcs5_frt : YP09.region := YP09.mkRegion (Some 32%nat) 120 128 0 0 [YP09.mkChunk 120 (CVal 8 (SOff 33 0))].
Definition dcs5_frs : YP09.region := YP09.mkRegion (Some 19%nat) 0 16 0 16 [].
Definition dcs5_regions : smem := [dcs5_flr; dcs5_s1r; dcs5_svr; dcs5_frh; dcs5_frt; dcs5_frs].
Definition dcs5_facts : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (8%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF 4096 (2 ^ 47) 5)] [] [].
Definition dcs5_ss : sstate := mkSS DC_KX sr_atoms dcs5_regions None dcs5_facts.
(* the atoms 32 .. 47 *)
Definition dcs5_extra (F FL res : Z) (regs : bvmap 5 word) : list word :=
  map (Z_to_bv 64) [F; FL; res] ++ map (fun r => getr regs (Z_to_bv 5 r)) dc_saved.

Lemma dcs5_sep1 : forall x lo n, (forall a, lo <= a < lo + n -> x <> a) -> x + 1 <= lo \/ lo + n <= x.
Proof.
intros x lo n H. destruct (Z_lt_le_dec x lo) as [h | h]; [left; lia|].
destruct (Z_lt_le_dec x (lo + n)) as [h' | h']; [exfalso; exact (H x ltac:(lia) eq_refl) | right; lia].
Qed.

Lemma dcs5_w64_mod : forall x, Z_to_bv 64 (x mod 2 ^ 64) = Z_to_bv 64 x.
Proof.
intros x. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
apply Z.mod_mod. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ seg_listing PI).
#[local] Abbreviation VAL := (@pa_val _ seg_listing PI).
#[local] Abbreviation BASE := (@pa_val _ seg_listing PI A_TEXT).
Section e.
Variable B : asyms.
Variables RLO RHI GOTW GUARD : Z.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUNF := aj_flag_store_pi B LAWS ML ASF FFL.
Let RET := paj_ret_at (PL := PL_seg) (PI := PI).

Lemma dc_S5 : dc_S5P B STK_reac_segconf_declared RLO RHI GOTW GUARD.
Proof using ML ASF FFL LAWS.
intros c HPRE ly3 S3 W3 regs3 mem3 md3 HINV.
destruct HINV as (HFI & HUN & HTAB & HRES).
destruct HFI as [HJ R2 R3 R4 R8 R9 R19 R20 VSV V16 V24 _ _ _ VFL].
destruct HUN as [HPerm Ely HFS]. subst ly3.
destruct HPRE as [HAFN _ _ _ _ _ _ _ _ _ HDPRE _ _].
destruct HDPRE as (_ & _ & _ & _ & _ & HVT & _).
destruct HVT as (_ & _ & _ & _ & HHEAP & _ & _ & _ & _ & _ & HDST & _ & HDISJ).
destruct HHEAP as (bt & mt & Hbt & Hbt1 & Hbt2).
destruct HTAB as (HRT & HNV & HLEN & HMAXL).
pose proof HAFN as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : STK_reac_segconf_declared = 12560) by reflexivity.
assert (Hfin : In (1, x_fpos c) (frames S3)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 (x_fpos c) HAR Hfin) as (HFal & HFapp & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 (x_fpos c) HAR Hfin) as (HF4096 & HFceil & _).
destruct (FFL _ _ _ _ _ 1 (x_fpos c) HAR Hfin) as (HFLp & HFLo & _ & (HFL4096 & _ & HFLc)).
change (fs_frame_bytes 1) with 128 in HFapp, HFpres, HFSpres, HFceil. change (128 / 8) with 16 in HFSpres.
unfold dc_F, dc_FL in *.
set (F := frame_addr (x_ly c) 1 (x_fpos c)) in *.
set (FL := flag_addr (x_ly c) 1 (x_fpos c)) in *.
change (dc_s1 c) with (dc_sp1 (spZ (x_regs c))) in *.
change (dc_sp0 c) with (spZ (x_regs c)) in *.
set (sp0 := spZ (x_regs c)) in *.
destruct (dc_sp1_facts sp0 Hal16) as (Hs1al & Hs1).
set (s1 := dc_sp1 sp0) in *.
assert (Hs1b : sp0 - 208 <= s1 <= sp0 - 192) by lia. clear Hs1.
assert (Hsp0 : alloc_ceiling + 12560 <= sp0 <= 2 ^ 47) by lia.
(* the frame is 32-aligned, so F / 8 is linear in F *)
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HFm : F / 8 = 4 * (F / 32))
  by (rewrite HFq at 1; replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by lia; apply Z.div_mul; lia).
assert (HF8 : F = 8 * (F / 8)) by lia.
(* the flag cell is outside the frame and its shadow: it is owned, they are not *)
assert (NF : forall a, F <= a < F + 128 -> FL <> a)
  by (intros a Ha Heq; apply (proj2 (HFpres a Ha)); rewrite <- Heq; exact HFLo).
assert (NS : forall a, SB + F / 8 <= a < SB + F / 8 + 16 -> FL <> a).
{ intros a Ha Heq. apply (proj2 (HFSpres (a - (SB + F / 8)) ltac:(lia))).
  unfold shadow_addr. rewrite <- SB_SHADOW_OFF.
  replace (SB + F / 8 + (a - (SB + F / 8))) with a by lia. rewrite <- Heq. exact HFLo. }
pose proof (dcs5_sep1 _ _ _ NF) as SF. pose proof (dcs5_sep1 _ _ _ NS) as SS.
(* the environment *)
set (E := Eimg (Ereg regs3 (dcs5_extra F FL (fst (dc_res c) mod 2 ^ 64) (x_regs c)))).
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (HRO : regs_ok E sr_atoms regs3) by (unfold E; apply regs_ok_Eimg_Ereg).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs3 r)
  by (intros; unfold E; apply ew_Eimg_Ereg_nat; assumption).
assert (EX : forall j, (j < 16)%nat ->
  ew E (32 + j) = nth j (dcs5_extra F FL (fst (dc_res c) mod 2 ^ 64) (x_regs c)) (Z_to_bv 64 0)).
{ intros j Hj. unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
clearbody E.
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34.
cbn [Nat.add nth dcs5_extra map app] in E32, E33, E34.
assert (ES : forall j r, nth_error dc_saved j = Some r -> ew E (35 + j) = getr (x_regs c) (Z_to_bv 5 r)).
{ intros j r Hj.
  assert (Hj13 : (j < 13)%nat).
  { pose proof (proj1 (nth_error_Some dc_saved j)) as Hs. rewrite Hj in Hs. specialize (Hs ltac:(discriminate)).
    exact Hs. }
  replace (35 + j)%nat with (32 + (3 + j))%nat by lia. rewrite EX by lia.
  unfold dcs5_extra. cbn [map app Nat.add nth].
  apply nth_error_nth. rewrite (map_nth_error (fun r0 => getr (x_regs c) (Z_to_bv 5 r0)) j dc_saved Hj). reflexivity. }
assert (U9 : bv_unsigned (ew E 9) = s1)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
assert (U8 : bv_unsigned (ew E 8) = sp0)
  by (rewrite (EE 8%nat 8%bv eq_refl), R8; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = SB + F / 8)
  by (rewrite (EE 19%nat 19%bv eq_refl), R19; apply unsigned_lit_small; unfold SB; lia).
assert (U32 : bv_unsigned (ew E 32) = F) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = FL) by (rewrite E33; apply unsigned_lit_small; lia).
(* the state at KX *)
assert (HS : st_ok_pi SEGS VAL E dcs5_ss
  (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (BASE + DC_KX)) mem3 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold dcs5_ss. apply pa_entry_st_ok_full.
  - exact HRO.
  - vm_compute. reflexivity.
  - unfold dcs5_regions, dcs5_flr, dcs5_s1r, dcs5_svr, dcs5_frh, dcs5_frt, dcs5_frs.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
    rewrite ?U33, ?U9, ?U8, ?U32, ?U19.
    + split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. replace (FL + o) with FL by lia. apply (apresent_writable SEGS). exact HFLp.
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val SEGS E _ s1 16 8 (SOff 32 0) F);
        [ cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia
        | eapply val_mem_of_rdword; exact V16 ].
      * apply (chunk_ok_val SEGS E _ s1 24 8 (SOff 32 0) F);
        [ cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia
        | eapply val_mem_of_rdword; exact V24 ].
      * apply (chunk_ok_val SEGS E _ s1 56 8 (SOff 34 0) (fst (dc_res c) mod 2 ^ 64));
        [ cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply Z.mod_pos_bound; lia | cbn; lia
        | eapply val_mem_of_rdword; exact HRES ].
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil;
      lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 8 (SOff ?n 0))) =>
        let j := eval compute in (n - 35)%nat in
        let r := eval compute in (nth j dc_saved 0) in
        let X := fresh "X" in
        pose proof (ES j r eq_refl) as X; cbn [Nat.add] in X;
        apply (chunk_ok_val SEGS E _ sp0 off 8 (SOff n 0) (bv_unsigned (ew E n)));
        [ cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | let HR := fresh in pose proof (bv_unsigned_in_range 64 (ew E n)) as HR;
          change (bv_modulus 64) with (2 ^ 64) in HR; change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia
        | cbn; lia
        | replace (sp0 + off) with (sp0 - 8 - 8 * Z.of_nat j) by (cbn; lia);
          rewrite X; eapply val_mem_of_rdword; exact (VSV j r eq_refl) ] end.
    + split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply (proj1 (HFpres (F + o) ltac:(lia))).
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ F 120 8 (SOff 33 0) FL);
        [ cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia
        | eapply val_mem_of_rdword; exact VFL ].
    + split; [unfold SB; lia|]. split; [unfold SB; lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS).
      unfold shadow_addr in HFSpres. rewrite <- SB_SHADOW_OFF in HFSpres. exact (proj1 (HFSpres o ltac:(lia))).
  - apply pairwise_disjoint_of_extents.
    unfold dcs5_regions, dcs5_flr, dcs5_s1r, dcs5_svr, dcs5_frh, dcs5_frt, dcs5_frs, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U33, U9, U8, U32, U19.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold in_app, kLowShadowBeg, kHighMemBeg, SB in *.
    repeat split; lia.
  - split; [|split; exact I].
    cbn [dcs5_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9, U8, U32.
    change (2 ^ 5) with 32. change (2 ^ 4) with 16.
    repeat split; lia. }
(* the run from KX to the `ret` *)
change (cfg_at SEGS (BASE + DC_KX) regs3 mem3 md3)
  with (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + DC_KX)) mem3 (seg_rom SEGS)) md3).
paj_run_flag_sh RUNF HS HJ.
- lia.
- intros a (r & Hr & Ha).
  change (ss_mem dcs5_ss) with dcs5_regions in Hr. unfold dcs5_regions in Hr.
  destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]];
  unfold dcs5_flr, dcs5_s1r, dcs5_svr, dcs5_frh, dcs5_frt, dcs5_frs in Ha;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
  rewrite ?U33, ?U9, ?U8, ?U32, ?U19 in Ha.
  + right. change (flag_addr (x_ly c) 1 (x_fpos c)) with FL. lia.
  + lia.
  + lia.
  + left. unfold awr_byte. right; right; right; left. exists 1, (x_fpos c). split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 1) with 128.
    change (frame_addr (x_ly c) 1 (x_fpos c)) with F. lia.
  + lia.
  + left. unfold awr_byte. right; right; right; left. exists 1, (x_fpos c). split; [left; reflexivity|].
    right. unfold in_zr, shadow_addr. cbn [fst snd]. change (fs_frame_bytes 1 / 8) with 16.
    change (frame_addr (x_ly c) 1 (x_fpos c)) with F. rewrite <- SB_SHADOW_OFF. lia.
- intros msr HSr.
  lazymatch type of HSr with st_ok_pi _ _ ?Ex ?ssx _ =>
    pose proof (st_ok_pi_region_nth Ex ssx msr 0 _ HSr eq_refl) as HR end.
  lazymatch type of HR with region_ok _ _ _ (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
    pose proof (field_of_region E (ms_mem msr) n _ cs lo hi wlo whi 0 1%N (SLit 0) 0 HR U33
      ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V end.
  rewrite Z.add_0_r in V. pose proof (V 0%nat ltac:(lia)) as V0. cbn [Z.of_nat] in V0.
  rewrite Z.add_0_r in V0. change (flag_addr (x_ly c) 1 (x_fpos c)) with FL. exact V0.
- (* the return *)
  clear HF HG.
  cbn [ms_mem mkst] in HFr.
  pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _
    (fun a => (F <= a < F + 8) \/ (SB + F / 8 <= a < SB + F / 8 + 16) \/ a = FL) HFr
    ltac:(let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
    let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
    intros b wlo whi a Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin];
    [ injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U33, ?U9, ?U8, ?U32, ?U19 in Hrr; cbv beta; lia |]);
    destruct Hin)) as UNCH.
  (* a byte of a live block is outside the release's three windows *)
  assert (HBW : forall b m a, In (b, m) (ablocks B (x_ly c) (x_S c)) -> b <= a < b + m ->
    0 <= a < 2 ^ 64 /\ ~ ((F <= a < F + 8) \/ (SB + F / 8 <= a < SB + F / 8 + 16) \/ a = FL)).
  { intros b m a Hb Ha.
    assert (Hb3 : In (b, m) (ablocks B (x_ly c) S3))
      by (apply (Permutation_in _ (Permutation_sym HPerm)); exact Hb).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb3) as (_ & Hb4096 & Hbceil & Hbapp & Hbpres & _ & Hm).
    pose proof (req_size_pos m (proj1 Hm)) as [_ Hrq].
    pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b m 1 (x_fpos c) HAR Hb3 Hfin) as Hsep.
    unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. change (fs_frame_bytes 1) with 128 in Hsep.
    change (frame_addr (x_ly c) 1 (x_fpos c)) with F in Hsep.
    unfold in_app, kLowShadowBeg, kHighMemBeg in Hbapp.
    split; [lia|]. intros [Hw | [Hw | Hw]].
    - lia.
    - unfold SB in Hw. lia.
    - subst a. exact (proj2 (Hbpres FL ltac:(lia)) HFLo). }
  (* the count cell is outside them too: every arm of sa_dst *)
  assert (HNW : forall k, 0 <= k < 4 -> 0 <= x_n c + k < 2 ^ 64 /\
    ~ ((F <= x_n c + k < F + 8) \/ (SB + F / 8 <= x_n c + k < SB + F / 8 + 16) \/ x_n c + k = FL)).
  { destruct HDST as [(HFF & _) | [(HHP & _) | (Hn1 & Hn2 & _)]].
    - destruct HFF as (cid & p & Hcp & Hcid & Hc1 & Hc2).
      assert (HcpS3 : In (cid, p) (frames S3)) by (rewrite Hfrs; right; exact Hcp).
      destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid p HAR HcpS3) as (Hc0 & Hcc & Hcapp).
      destruct (al_frames _ _ LAWS _ _ _ _ _ cid p HAR HcpS3) as (_ & _ & Hcpres & _).
      destruct (in_split _ _ Hcp) as (l1 & l2 & Hsp).
      pose proof (sep_frames_pos SEGS B LAWS (x_ly c) S3 W3 mem3 md3 (1, x_fpos c) (cid, p) [] l1 l2 HAR
        ltac:(rewrite Hfrs, Hsp; reflexivity)) as Hdj.
      unfold zdisjoint, frame_rng in Hdj. cbn [fst snd] in Hdj. change (fs_frame_bytes 1) with 128 in Hdj.
      change (frame_addr (x_ly c) 1 (x_fpos c)) with F in Hdj.
      unfold in_app, kLowShadowBeg, kHighMemBeg in Hcapp.
      intros k Hk. split; [lia|]. intros [Hw | [Hw | Hw]].
      + lia.
      + unfold SB in Hw. lia.
      + exact (proj2 (Hcpres (x_n c + k) ltac:(lia)) ltac:(rewrite Hw; exact HFLo)).
    - destruct HHP as (bn & mn & Hbn & Hbn1 & Hbn2).
      intros k Hk. apply (HBW bn mn); [exact Hbn | lia].
    - intros k Hk. split; [lia|]. unfold SB. lia. }
  prreg HS (1%bv : bv 5) Q1.
  pose proof (ES 0%nat 1 eq_refl) as S35. cbn [Nat.add] in S35.
  eapply (RET W3 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. unfold dc_post, apost_base.
  lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ =>
    exists (x_ly c), (stack_free_state 1 (x_fpos c) S3), r, m, d end.
  split.
  { rewrite Q1, S35. change (getr (x_regs c) (Z_to_bv 5 1)) with (getr (x_regs c) 1).
    unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
  split; [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ|].
  split.
  { apply aregs_preserved_eqs.
    - prreg HS (2%bv : bv 5) Rq. rewrite Rq, (EE 8%nat 8%bv eq_refl), R8. apply Z_to_bv_bv_unsigned.
    - prreg HS (3%bv : bv 5) Rq. rewrite Rq, (EE 3%nat 3%bv eq_refl), R3, Hgp. reflexivity.
    - prreg HS (4%bv : bv 5) Rq. rewrite Rq, (EE 4%nat 4%bv eq_refl), R4, Htp. reflexivity.
    - prreg HS (8%bv : bv 5) Rq. pose proof (ES 1%nat 8 eq_refl) as X. cbn [Nat.add] in X. rewrite Rq, X; reflexivity.
    - prreg HS (9%bv : bv 5) Rq. pose proof (ES 2%nat 9 eq_refl) as X. cbn [Nat.add] in X. rewrite Rq, X; reflexivity.
    - prreg HS (18%bv : bv 5) Rq. pose proof (ES 3%nat 18 eq_refl) as X. cbn [Nat.add] in X. rewrite Rq, X; reflexivity.
    - prreg HS (19%bv : bv 5) Rq. pose proof (ES 4%nat 19 eq_refl) as X. cbn [Nat.add] in X. rewrite Rq, X; reflexivity.
    - prreg HS (20%bv : bv 5) Rq. pose proof (ES 5%nat 20 eq_refl) as X. cbn [Nat.add] in X. rewrite Rq, X; reflexivity.
    - prreg HS (21%bv : bv 5) Rq. pose proof (ES 6%nat 21 eq_refl) as X. cbn [Nat.add] in X. rewrite Rq, X; reflexivity.
    - prreg HS (22%bv : bv 5) Rq. pose proof (ES 7%nat 22 eq_refl) as X. cbn [Nat.add] in X. rewrite Rq, X; reflexivity.
    - prreg HS (23%bv : bv 5) Rq. pose proof (ES 8%nat 23 eq_refl) as X. cbn [Nat.add] in X. rewrite Rq, X; reflexivity.
    - prreg HS (24%bv : bv 5) Rq. pose proof (ES 9%nat 24 eq_refl) as X. cbn [Nat.add] in X. rewrite Rq, X; reflexivity.
    - prreg HS (25%bv : bv 5) Rq. pose proof (ES 10%nat 25 eq_refl) as X. cbn [Nat.add] in X. rewrite Rq, X; reflexivity.
    - prreg HS (26%bv : bv 5) Rq. pose proof (ES 11%nat 26 eq_refl) as X. cbn [Nat.add] in X. rewrite Rq, X; reflexivity.
    - prreg HS (27%bv : bv 5) Rq. pose proof (ES 12%nat 27 eq_refl) as X. cbn [Nat.add] in X. rewrite Rq, X; reflexivity. }
  unfold dc_Q. split; [|split; [|split; [|split]]].
  + (* a0: the result word 56(s1) *)
    prreg HS (10%bv : bv 5) Q10. rewrite Q10, E34. exact (dcs5_w64_mod _).
  + (* the table: INV_KX's bytes, outside the three windows *)
    destruct HRT as (bs & Hbs & Henc). exists bs. split; [|exact Henc].
    pose proof (proj1 Henc) as Hlbs. unfold seg_spec.RVLAN_SIZE in Hbt2.
    intros i Hi.
    destruct (HBW bt mt (x_tab c + Z.of_nat i) Hbt ltac:(lia)) as (Hr64 & Hnz).
    rewrite (UNCH _ Hr64 Hnz). exact (Hbs i Hi).
  + (* the count cell *)
    intros k Hk. destruct (HNW (Z.of_nat k) ltac:(lia)) as (Hr64 & Hnz).
    rewrite (UNCH _ Hr64 Hnz). exact (HNV k Hk).
  + (* the guard entry: the final journal's block clause, from the entry *)
    intros HG0. unfold sa_guardtab, sa_bytes in HG0 |- *. intros i Hi.
    assert (Hlg : length seg_spec.GUARD_BYTES = 18%nat) by reflexivity.
    pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HBLK & _).
    assert (Hbt3 : In (bt, mt) (ablocks B (x_ly c) S3))
      by (apply (Permutation_in _ (Permutation_sym HPerm)); exact Hbt).
    assert (HinF : In (bt, mt) (ablocks B (x_ly c) (stack_free_state 1 (x_fpos c) S3)))
      by (unfold ablocks; rewrite blocks_stack_free_state; exact Hbt3).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ bt mt HAR Hbt3) as (_ & _ & _ & _ & _ & _ & Hm).
    pose proof (req_size_pos mt (proj1 Hm)) as [_ Hrq].
    unfold seg_spec.RVLAN_SIZE in *. unfold sa_disj in HDISJ.
    assert (HNF : ~ inFP (dc_FP c) (bt + (x_tab c + 18 * x_max c + Z.of_nat i - bt))).
    { intros (r & Hr & Hfp). unfold dc_FP, declared_W, vtab_W in Hr.
      rewrite in_app_iff in Hr. destruct Hr as [Hr | Hr].
      - destruct Hr as [<- | []]. cbn [fst snd] in Hfp. unfold seg_spec.RVLAN_SIZE in Hfp. lia.
      - destruct (length (x_tb c) <? length (snd (dc_res c)))%nat; [destruct Hr as [<- | []] | destruct Hr].
        cbn [fst snd] in Hfp. lia. }
    pose proof (HBLK bt mt (x_tab c + 18 * x_max c + Z.of_nat i - bt) Hbt HinF ltac:(lia) HNF) as HK.
    replace (bt + (x_tab c + 18 * x_max c + Z.of_nat i - bt)) with (x_tab c + 18 * x_max c + Z.of_nat i) in HK
      by lia.
    rewrite HK. exact (HG0 i Hi).
  + (* no allocation: the frame taken at the entry is the frame freed here *)
    split; [unfold ablocks; rewrite blocks_stack_free_state; exact HPerm|].
    split; [reflexivity|].
    destruct HFS as (f & ES3). exists (st_fs (stack_free_state 1 (x_fpos c) S3)). rewrite ES3. reflexivity.
Qed.
End e.
End f.
End d.
