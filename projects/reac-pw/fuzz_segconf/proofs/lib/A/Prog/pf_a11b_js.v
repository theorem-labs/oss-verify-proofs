(* reac-pw/fuzz_segconf, ASan image A: the "%s%s" format fact that the join loop of segment A11b of
   reac_segconf_parse_file's walk (0x8865c .. 0x886c4, lib/A/Prog/pf_a11b_d.v's H_KLOOP) needs at its call
   0x88698, snprintf(known + kn, 240 - kn, "%s%s", sep, token). Part of segment A11b's proof, by the G3 walk owner,
   2026-10-30.

   proves no function (kind: segment lemma of reac_segconf_parse_file's walk): no function of the binary is walked
   here; the rule-24 record of reac_segconf_parse_file is the unit's internal record,
   commit dfb49d6ad789, path records/segp/g3-lookup.md (CONFIRMed
   2026-10-30T15:42:08Z, reuse verdict none: written new).

   Row 4 as released is RtFormat.asnprintf_realizes = RtPFCmd.asnprintf_sh, i.e. cmd_asnprintf_realizes at the
   family FR_cmd. The snprintf step itself is the A8b proof's lib/A/Prog/pf_a8b_t.v (pfa8b_aj_snprintf_atSF, in the
   shared base), Required here; this file adds only the family at the loop's format:
   - pfj_F_ss_len, pfj_parse_F_ss: "%s%s" is 4 bytes and parses to [Ps; Ps].
   - pfj_arg_s: one string argument's pf_arg_asan from SegABase's sa_str / sa_addr facts.
   - pfj_FR_ss / pfj_FR_ss_regs: FR_cmd at "%s%s" with two string arguments s1 at w1 and s2 at w2 (built by
     hand: RtPFCmd.FR_cmd_intro's boolean fr_lit_ok forbids APtr), text s1 ++ s2. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegABase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtPFPf RtPFShared RtPFSx RtPFCmd RtFormat.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI04 YI16 YA0n YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaArt PaFx pf_a8b_t.

(* ======== the format "%s%s" ======== *)
Lemma pfj_F_ss_len : Z.of_nat (length SegModel.F_ss) = 4.
Proof. vm_compute. reflexivity. Qed.
Lemma pfj_parse_F_ss : pf_parse SegModel.F_ss = Some [Ps; Ps].
Proof. vm_compute. reflexivity. Qed.

(* one string argument s at w: its bytes, NUL and slack word (sa_str), its amem and shadow (sa_addr), its read span
   apart from rs (pfa8b_FR_s's argument part) *)
Lemma pfj_arg_s : forall (rd : reader) (rs : list (Z * Z)) (w : Z) (s : list Z),
  0 < w -> Forall (fun c => 0 < c < 256) s -> Z.of_nat (length s) + 8 < 2 ^ 31 ->
  sa_str rd w s -> sa_addr rd w (Z.of_nat (length s) + 1) ->
  Forall (zdisjoint (w, seg_spec.cstr_span w s)) rs ->
  pf_arg_asan rd rs w (APtr s).
Proof.
intros rd rs w s Hw Hb Hl ((Hzs & _) & Htl) (_ & _ & Ham1 & Hra & Hhv) Hd.
split; [exact Hb|]. split; [exact Hw|]. split; [exact Hl|].
split.
{ intros i Hi. specialize (Hzs (Z.to_nat i) ltac:(rewrite length_app; cbn [length]; lia)).
  rewrite Z2Nat.id in Hzs by lia. exact Hzs. }
split; [exact Htl|].
split; [rewrite pfa8b_str_end_span; exact Hd|].
split; [exact Ham1|]. split; [exact Hra | apply Hhv; lia].
Qed.

(* FR_cmd at "%s%s" with the two string arguments s1 at w1 and s2 at w2: the format literal at fp (its bytes and NUL
   from sa_str, its amem and shadow from sa_addr, below the GOT word CMD_GOTW), each argument as pfj_arg_s, 8 bytes
   past each NUL in application memory *)
Lemma pfj_FR_ss : forall (rd : reader) (rs : list (Z * Z)) (fp w1 w2 : Z) (s1 s2 : list Z) (r3 r4 r5 : Z),
  0 < fp -> CMD_IMG_LO <= fp -> fp + 5 <= CMD_GOTW ->
  sa_str rd fp SegModel.F_ss -> sa_addr rd fp 5 ->
  Forall (zdisjoint (fp, 5)) rs ->
  0 < w1 -> Forall (fun c => 0 < c < 256) s1 -> Z.of_nat (length s1) + 8 < 2 ^ 31 ->
  sa_str rd w1 s1 -> sa_addr rd w1 (Z.of_nat (length s1) + 1) ->
  amem_range w1 (Z.of_nat (length s1) + 8) ->
  Forall (zdisjoint (w1, seg_spec.cstr_span w1 s1)) rs ->
  0 < w2 -> Forall (fun c => 0 < c < 256) s2 -> Z.of_nat (length s2) + 8 < 2 ^ 31 ->
  sa_str rd w2 s2 -> sa_addr rd w2 (Z.of_nat (length s2) + 1) ->
  amem_range w2 (Z.of_nat (length s2) + 8) ->
  Forall (zdisjoint (w2, seg_spec.cstr_span w2 s2)) rs ->
  FR_cmd rd rs fp [w1; w2; r3; r4; r5] (s1 ++ s2).
Proof.
intros rd rs fp w1 w2 s1 s2 r3 r4 r5 Hf0 Hflo Hfg ((Hfz & _) & _) (_ & _ & Hfam & Hfra & Hfhv) Hfd
  Hw1 Hb1 Hl1 HS1 HA1 Ham1 Hd1 Hw2 Hb2 Hl2 HS2 HA2 Ham2 Hd2.
pose proof pfj_F_ss_len as EF.
assert (E5 : Z.of_nat (length SegModel.F_ss) + 1 = 5) by (rewrite EF; reflexivity).
pose proof (Z.mod_pos_bound (w1 + Z.of_nat (length s1)) 8 ltac:(lia)) as Hm1.
pose proof (Z.mod_pos_bound (w2 + Z.of_nat (length s2)) 8 ltac:(lia)) as Hm2.
unfold FR_cmd. exists SegModel.F_ss, [Ps; Ps], [APtr s1; APtr s2].
split.
{ (* fmt_at *)
  split; [exact Hf0|]. rewrite E5. split.
  - intros i Hi. specialize (Hfz (Z.to_nat i) ltac:(rewrite length_app; cbn [length]; lia)).
    rewrite Z2Nat.id in Hfz by lia. exact Hfz.
  - split; [exact Hfd|]. split; [exact Hfam|]. split; [exact Hfra | apply Hfhv; lia]. }
split; [exact pfj_parse_F_ss|].
split; [apply pf_cmd_piece_all|].
split.
{ (* pf_args_asan: the two string arguments *)
  split; [exact (pfj_arg_s rd rs w1 s1 Hw1 Hb1 Hl1 HS1 HA1 Hd1)|].
  split; [exact (pfj_arg_s rd rs w2 s2 Hw2 Hb2 Hl2 HS2 HA2 Hd2) | exact I]. }
split; [cbn [pf_text option_map]; rewrite app_nil_r; reflexivity|].
split; [exact I|].
split; [exact Hflo|].
split; [lia|].
split; [split; [unfold amem_range, str_end in *; lia | split; [unfold amem_range, str_end in *; lia | exact I]]|].
split; [intros E; discriminate E|].
split; [exact Ham1 | split; [exact Ham2 | exact I]].
Qed.

(* the same at the step's argument words map (argZ regs) [3; 4; 5; 6; 7], with a3 = w1 and a4 = w2 *)
Lemma pfj_FR_ss_regs : forall (rd : reader) (rs : list (Z * Z)) (fp w1 w2 : Z) (s1 s2 : list Z) (regs : bvmap 5 word),
  argZ regs 3 = w1 -> argZ regs 4 = w2 ->
  0 < fp -> CMD_IMG_LO <= fp -> fp + 5 <= CMD_GOTW ->
  sa_str rd fp SegModel.F_ss -> sa_addr rd fp 5 ->
  Forall (zdisjoint (fp, 5)) rs ->
  0 < w1 -> Forall (fun c => 0 < c < 256) s1 -> Z.of_nat (length s1) + 8 < 2 ^ 31 ->
  sa_str rd w1 s1 -> sa_addr rd w1 (Z.of_nat (length s1) + 1) ->
  amem_range w1 (Z.of_nat (length s1) + 8) ->
  Forall (zdisjoint (w1, seg_spec.cstr_span w1 s1)) rs ->
  0 < w2 -> Forall (fun c => 0 < c < 256) s2 -> Z.of_nat (length s2) + 8 < 2 ^ 31 ->
  sa_str rd w2 s2 -> sa_addr rd w2 (Z.of_nat (length s2) + 1) ->
  amem_range w2 (Z.of_nat (length s2) + 8) ->
  Forall (zdisjoint (w2, seg_spec.cstr_span w2 s2)) rs ->
  FR_cmd rd rs fp (map (argZ regs) [3; 4; 5; 6; 7]) (s1 ++ s2).
Proof.
intros rd rs fp w1 w2 s1 s2 regs E3 E4. cbn [map]. rewrite E3, E4.
exact (pfj_FR_ss rd rs fp w1 w2 s1 s2 (argZ regs 5) (argZ regs 6) (argZ regs 7)).
Qed.
