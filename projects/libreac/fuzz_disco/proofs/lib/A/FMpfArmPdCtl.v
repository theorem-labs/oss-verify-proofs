(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/FMpfArmPdCtl.v (a working branch 0ddf65fd8cc); relocated to libreac/fuzz_disco.asan by reloc.py (target disco-A): module paths changed; 1 address numerals moved (port_addr_check 0767e70e074a predict, fm.asan -> fuzz_disco.asan, symbol + offset; table: this file's rows in provenance/evidence/g9-gxa/g9tool/g9-table-disco-A.tsv); names: record RT_IImgA -> A_img RecAsanVfA.N_img_asan_vf; YImgTop zify_pre_hook added after the last Require. *)
(* R-1 row R-d (a Theorem Labs lane's analyses/rtprintf/design/R1-FREE-PIECES.md (a working branch 952598da9f3b)): fm's pieces widened by %d (Pd), with the four arms the route asks for
   (FMsnprintfFmI.v fm_snprintf_gxaP: seam_text_arm, seam_pargs_arm, seam_bytes_arm and pcom_pcx_arm, each for every
   piece of the predicate), and the NON-VACUITY CONTROL on the printf_common side.
   - pf_fm_pc_d: literals, %s, %.*s (RT_pf_sh.v pf_fm_pc) and %d;
   - its arms: fm's own (FMgxaSeamPf.v pf_fm_*_arms' lemmas, RT_pf_sh.v pcom_pcx_arm_lit / _ps / _pps), the seam arms of
     Pd from a Theorem Labs lane's lib/A/FMpfArmPdSeam.v (seam_text_arm_pd, seam_pargs_arm_pd, seam_bytes_arm_pd), and the pcom arm
     of Pd from lib/A/RT_pf_d.v (pcom_pcx_arm_Pd);
   - the instances: printf_common's contract for FF_pcomK pf_fm_pc_d (RT_pf_shU.v pcom_shzK) and fm's snprintf for
     FF_fmP pf_fm_pc_d (FMsnprintfFmI.v fm_snprintf_gxaP);
   - the control, at a REAL fuzz_disco %d format: libreac fuzz/fuzz_disco.c:621
     `snprintf(width, sizeof width, "%dx%d", e->decl_in, e->decl_out)`, the 5 bytes 25 64 78 25 64 (and its NUL) at .rodata
     0x20fe0 of both the pinned libreac fuzz_disco binary and .../asan-ubsan/fuzz_disco (read with pyelftools
     0.33; site 2 of provenance/evidence/g9-gxa/gates/call-sites.tsv). It parses to [Pd; PLit 120; Pd]; fm's own
     predicate refuses it; printf_common's grammar reads 'd' as an int conversion and its walk consumes BOTH argument
     words, each with the coverage entry None (through pcomx_K and pcom_pcx_arm_Pd); for every pair of 32-bit values the
     format with those two arguments is in printf_common's family FF_pcomK pf_fm_pc_d and in the route's family
     FF_fmP pf_fm_pc_d, with the text pf_dec v1 ++ "x" ++ pf_dec v2; one instance takes a slot word whose upper 32 bits
     are not zero (the %d argument is the low 32 bits: 4) and prints "4x2".
   The seam-side control is a Theorem Labs lane's FMpfArmPdSeam.v seam_pd_control ("%d" at -42 -> "-42" through pt_text_eqP).
   New file; nothing else is edited. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AE20 AE2y.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SnUpoison.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require Import FMH_Base FMsnprintfImg.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import PfFacts SnShared SnSx.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SnFF.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require Import FMpfStep.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Bz.A Require I_pcxgram.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require RT_pf_Tbl RT_pf_sh RT_pf_shU RT_pf_d.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require FMgxaSeamPf FMpfArmPdSeam.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require FMsnprintfFm FMsnprintfCr FMsnprintfFmI.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GX Require G_printf_core_common.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.I Require Import RecAsanVfA.
#[local] Ltac Zify.zify_pre_hook ::= try unfold YImgTop.IMG_TOP, YImgTop.IMG_LO in *.
Import ListNotations.
Local Open Scope Z_scope.

Module BzG := OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Bz.A.I_pcxgram.
Module RTS := OSSVerify.Proofs.libreac.fuzz_disco.lib.A.RT_pf_sh.
Module RTU := OSSVerify.Proofs.libreac.fuzz_disco.lib.A.RT_pf_shU.
Module SPf := OSSVerify.Proofs.libreac.fuzz_disco.lib.A.FMgxaSeamPf.
Module SPd := OSSVerify.Proofs.libreac.fuzz_disco.lib.A.FMpfArmPdSeam.
Module FMI := OSSVerify.Proofs.libreac.fuzz_disco.lib.A.FMsnprintfFmI.

(* ---- fm's pieces and %d ---- *)
Definition pf_fm_pc_d (p : pf_piece) : Prop := match p with PLit _ | Ps | Pps | Pd => True | _ => False end.

Lemma pf_fm_pc_d_of : forall p, RTS.pf_fm_pc p -> pf_fm_pc_d p.
Proof. intros p Hp. destruct p; cbn in Hp |- *; tauto. Qed.

(* ---- the four arms of every piece of pf_fm_pc_d ---- *)
Lemma pf_fm_text_arms_d : forall p, pf_fm_pc_d p -> SPf.seam_text_arm p.
Proof.
intros p Hp. destruct p; try (exfalso; exact Hp).
- apply SPf.seam_text_arm_lit.
- exact SPd.seam_text_arm_pd.
- exact SPf.seam_text_arm_ps.
- exact SPf.seam_text_arm_pps.
Qed.
Lemma pf_fm_pargs_arms_d : forall p, pf_fm_pc_d p -> SPf.seam_pargs_arm p.
Proof.
intros p Hp. destruct p; try (exfalso; exact Hp).
- apply SPf.seam_pargs_arm_lit.
- exact SPd.seam_pargs_arm_pd.
- exact SPf.seam_pargs_arm_ps.
- exact SPf.seam_pargs_arm_pps.
Qed.
Lemma pf_fm_bytes_arms_d : forall p, pf_fm_pc_d p -> SPf.seam_bytes_arm p.
Proof.
intros p Hp. destruct p; try (exfalso; exact Hp).
- apply SPf.seam_bytes_arm_lit.
- exact SPd.seam_bytes_arm_pd.
- exact SPf.seam_bytes_arm_ps.
- exact SPf.seam_bytes_arm_pps.
Qed.
Lemma pf_fm_pcx_arms_d : forall p, pf_fm_pc_d p -> RTS.pcom_pcx_arm p.
Proof.
intros p Hp. destruct p; try (exfalso; exact Hp).
- apply RTS.pcom_pcx_arm_lit.
- exact RT_pf_d.pcom_pcx_arm_Pd.
- exact RTS.pcom_pcx_arm_ps.
- exact RTS.pcom_pcx_arm_pps.
Qed.

(* ---- the instances: printf_common's contract and fm's snprintf at pf_fm_pc_d ---- *)
Module GXC := OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.
#[local] Existing Instance N_img_asan_vf.

Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem pcom_shz_d : forall B, AR_laws tfibsegs B -> TfibSyms B -> forall K, 2320 <= K ->
  sh_apcommon_realizesUz tfibsegs B (RTS.FF_pcomK pf_fm_pc_d) K RTU.PCM_CR RT_pf_Tbl.PF_PRINTF_COMMON.
Proof. intros B LAWS TB K HK. exact (RTU.pcom_shzK B LAWS TB pf_fm_pc_d pf_fm_pcx_arms_d K HK). Qed.

Theorem fm_snprintf_gxa_d : forall B, AR_laws tfibsegs B -> TfibSyms B ->
  forall img_lo img_hi K, img_lo <= 65536 -> @GXC.GLOBALS_TOP N_img_asan_vf <= img_hi ->
  FMsnprintfFm.fm_glue_img + FMsnprintfFm.GXA_VF_DEPTH <= K ->
  sh_asnprintf_realizesU tfibsegs B (FMI.FF_fmP pf_fm_pc_d) K FM_GOT_canary FM_canary img_lo img_hi
    FMsnprintfCr.fm_cr PC_snprintf.
Proof.
intros B LAWS TB.
exact (FMI.fm_snprintf_gxaP B LAWS TB pf_fm_pc_d pf_fm_text_arms_d pf_fm_pargs_arms_d pf_fm_bytes_arms_d
  pf_fm_pcx_arms_d).
Qed.
End f.

(* ==== NON-VACUITY CONTROL: fuzz_disco.c:621's "%dx%d" (.rodata 0x20fe0, both disco ASan images) ==== *)
Definition ctl_fmt : list Z := [37; 100; 120; 37; 100].
Definition ctl_ps : list pf_piece := [Pd; PLit 120; Pd].
Definition ctl_f : Z := 0x20fe0.
(* a memory reading the format and its NUL at ctl_f, and 0 (an addressable shadow byte) everywhere else *)
Definition ctl_rd : reader := fun a =>
  if (ctl_f <=? a) && (a <=? ctl_f + 5) then Some (nth (Z.to_nat (a - ctl_f)) (ctl_fmt ++ [0]) 0) else Some 0.

(* the format parses to %d, 'x', %d *)
Lemma ctl_parse : pf_parse ctl_fmt = Some ctl_ps.
Proof. reflexivity. Qed.

(* fm's own predicate refuses it: only the widening admits it *)
Lemma ctl_not_fm : ~ Forall RTS.pf_fm_pc ctl_ps.
Proof. intros H. inversion H as [|? ? Hp _]. exact Hp. Qed.

Lemma ctl_pk : Forall pf_fm_pc_d ctl_ps.
Proof. repeat constructor. Qed.

(* the text is a function of both arguments *)
Lemma ctl_text : forall v1 v2, pf_text ctl_ps [AInt v1; AInt v2] = Some (pf_dec v1 ++ 120 :: pf_dec v2).
Proof. intros v1 v2. cbn [pf_text ctl_ps option_map]. rewrite app_nil_r. reflexivity. Qed.

(* printf_common's grammar reads "d" as an int conversion: no flag, width, precision or length modifier *)
Lemma ctl_dir_d : forall rest, BzG.pcx_dir (100 :: rest) = Some (false, BzG.PP_none, BzG.PK_int, rest).
Proof. intros rest. reflexivity. Qed.

(* the scan accepts the format with the two int arguments, through pcomx_K and pcom_pcx_arm_Pd, and gives each
   argument its coverage entry None *)
Lemma ctl_pcomx : forall v1 v2,
  BzG.pcomx_ok (ctl_fmt ++ [0]) (map RTS.pa_of [AInt v1; AInt v2]) = true /\
  BzG.pcx_covs (length (ctl_fmt ++ [0])) (ctl_fmt ++ [0]) (map RTS.pa_of [AInt v1; AInt v2]) (RTS.pc_cinK ctl_ps)
    = [None; None].
Proof.
intros v1 v2.
destruct (RTS.pcomx_K pf_fm_pc_d pf_fm_pcx_arms_d ctl_fmt ctl_ps [AInt v1; AInt v2] _ ctl_parse ctl_pk (ctl_text v1 v2))
  as [OK C].
split; [exact OK|]. rewrite C. reflexivity.
Qed.

(* the walk consumes BOTH argument words *)
Lemma ctl_walk2 : forall v1 v2,
  BzG.pcx_walk (length (ctl_fmt ++ [0])) (ctl_fmt ++ [0]) (map RTS.pa_of [AInt v1; AInt v2]) = Some 2%nat.
Proof. intros v1 v2. reflexivity. Qed.

(* the format at ctl_f, for any written regions rs that avoid its 6 bytes *)
Lemma ctl_fmt_at : forall rs, Forall (zdisjoint (ctl_f, 6)) rs -> fmt_at ctl_rd rs ctl_f ctl_fmt.
Proof.
intros rs Hrs. unfold fmt_at.
split; [unfold ctl_f; lia|].
split.
{ intros i Hi. change (Z.of_nat (length ctl_fmt)) with 5 in Hi. unfold ctl_rd.
  replace ((ctl_f <=? ctl_f + i) && (ctl_f + i <=? ctl_f + 5)) with true
    by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia).
  replace (ctl_f + i - ctl_f) with i by lia. reflexivity. }
split; [exact Hrs|].
split; [left; apply Z.leb_le; vm_compute; reflexivity|].
split.
{ intros x Hx. change (Z.of_nat (length ctl_fmt)) with 5 in Hx. exists 0. split; [|left; reflexivity].
  unfold ctl_rd, shadow_of_addr, SHADOW_OFF.
  assert (D : 0 <= x / 8) by (apply Z.div_pos; unfold ctl_f in Hx; lia).
  replace (0x7fff8000 + x / 8 <=? ctl_f + 5) with false
    by (symmetry; apply Z.leb_gt; unfold ctl_f; lia).
  rewrite andb_false_r. reflexivity. }
intros s _. unfold ctl_rd. destruct (_ && _); discriminate.
Qed.

(* the arguments: two 32-bit ints read from two 64-bit slot words (pf_arg_asan's AInt case) *)
Lemma ctl_args_asan : forall rs w1 v1 w2 v2,
  -2 ^ 31 <= v1 < 2 ^ 31 -> w1 mod 2 ^ 32 = v1 mod 2 ^ 32 -> -2 ^ 31 <= v2 < 2 ^ 31 -> w2 mod 2 ^ 32 = v2 mod 2 ^ 32 ->
  pf_args_asan ctl_rd rs [w1; w2] [AInt v1; AInt v2].
Proof. intros rs w1 v1 w2 v2 H1 E1 H2 E2. cbn [pf_args_asan pf_arg_asan]. tauto. Qed.

(* in printf_common's family at pf_fm_pc_d, for every pair of 32-bit arguments *)
Lemma ctl_in_pcomK : forall rs w1 v1 w2 v2, Forall (zdisjoint (ctl_f, 6)) rs ->
  -2 ^ 31 <= v1 < 2 ^ 31 -> w1 mod 2 ^ 32 = v1 mod 2 ^ 32 -> -2 ^ 31 <= v2 < 2 ^ 31 -> w2 mod 2 ^ 32 = v2 mod 2 ^ 32 ->
  RTS.FF_pcomK pf_fm_pc_d ctl_rd rs ctl_f [w1; w2] (pf_dec v1 ++ 120 :: pf_dec v2).
Proof.
intros rs w1 v1 w2 v2 Hrs H1 E1 H2 E2.
assert (E : TFIB_IMG_END = 0x5fe000) by (vm_compute; reflexivity).
exists ctl_fmt, ctl_ps, [AInt v1; AInt v2].
split; [exact (ctl_fmt_at rs Hrs)|].
split; [discriminate|].
split; [rewrite E; unfold ctl_f; change (Z.of_nat (length ctl_fmt)) with 5; lia|].
split; [exact ctl_parse|].
split; [exact ctl_pk|].
split; [exact (ctl_args_asan rs w1 v1 w2 v2 H1 E1 H2 E2)|].
split; [cbn; exact I|].
split; [exact (ctl_text v1 v2)|].
cbn. exact I.
Qed.

(* and in the route's family FF_fmP pf_fm_pc_d (fm_snprintf_gxa_d's), for every pair of 32-bit arguments *)
Lemma ctl_in_route : forall rs w1 v1 w2 v2, Forall (zdisjoint (ctl_f, 6)) rs ->
  -2 ^ 31 <= v1 < 2 ^ 31 -> w1 mod 2 ^ 32 = v1 mod 2 ^ 32 -> -2 ^ 31 <= v2 < 2 ^ 31 -> w2 mod 2 ^ 32 = v2 mod 2 ^ 32 ->
  FMI.FF_fmP pf_fm_pc_d ctl_rd rs ctl_f [w1; w2] (pf_dec v1 ++ 120 :: pf_dec v2).
Proof.
intros rs w1 v1 w2 v2 Hrs H1 E1 H2 E2.
exists ctl_fmt, ctl_ps, [AInt v1; AInt v2].
split; [exact (ctl_fmt_at rs Hrs)|].
split; [exact ctl_parse|].
split; [exact ctl_pk|].
split; [exact (ctl_args_asan rs w1 v1 w2 v2 H1 E1 H2 E2)|].
split; [exact (ctl_text v1 v2)|].
split; [cbn; exact I|].
split; [unfold ctl_f; lia|].
split; [unfold ctl_f; change (Z.of_nat (length ctl_fmt)) with 5; lia|].
split; [cbn; exact I|].
split; [discriminate|].
cbn. exact I.
Qed.

(* one instance: the first slot word carries 0x7fffffff in its upper 32 bits; the %d argument is its low 32 bits, 4;
   the text is "4x2" *)
Lemma ctl_instance_pcom : RTS.FF_pcomK pf_fm_pc_d ctl_rd [] ctl_f [0x7fffffff00000004; 2] [52; 120; 50].
Proof. exact (ctl_in_pcomK [] 0x7fffffff00000004 4 2 2 (Forall_nil _) ltac:(lia) eq_refl ltac:(lia) eq_refl). Qed.
Lemma ctl_instance_route : FMI.FF_fmP pf_fm_pc_d ctl_rd [] ctl_f [0x7fffffff00000004; 2] [52; 120; 50].
Proof. exact (ctl_in_route [] 0x7fffffff00000004 4 2 2 (Forall_nil _) ltac:(lia) eq_refl ltac:(lia) eq_refl). Qed.
