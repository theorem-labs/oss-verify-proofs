(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/FMsnprintfCr.v; relocated to plugin-hostd/fuzz_command.asan by the GXA address relocator (target fuzz_command.asan): module paths changed; 7 address numerals moved (address checker 0767e70e074a, predict mode, fm.asan -> fuzz_command.asan, symbol + offset; the relocator's table for this file); names: TfibSyms -> SegBSyms. *)
(* The read-only constants of fm's snprintf chain: cr = fm's non-writable segments (the same expression as Pcommon's
   RT_pf_shU.PCM_CR), with its bounds (fm_cr_bounds, fm_cr_in_image), the static side condition GXA's seam asks of a
   contract's constant list (FMgxaSeamNorm.ro_covered), and consts_view over it from the harness's two read-only views
   (RtPFH.rom_viewN for the non-owned bytes, rom_viewO for the runtime-owned statics; errno lies above the image,
   AF0m's SegBSyms). New file. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YI04 YM05.

From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtPFupoison RtPFH.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtPFShared.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require FMgxaSeamNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib Require Mem.
Import ListNotations.
Local Open Scope Z_scope.

Module CJM := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Mem.

(* every read-only byte of fm's image: the non-writable segments *)
Definition fm_cr : list (Z * Z) :=
  map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) (List.filter (fun s => negb (seg_writable s)) tfibsegs).

(* a range of fm_cr is a non-writable segment's *)
Lemma fm_cr_seg : forall r, In r fm_cr ->
  exists s, In s tfibsegs /\ seg_writable s = false /\ r = (Z.of_N (seg_base s), Z.of_N (seg_size s)).
Proof.
intros r Hr. unfold fm_cr in Hr. apply in_map_iff in Hr as (s & <- & Hs). apply filter_In in Hs as [Hin Hw].
exists s. split; [exact Hin|]. split; [|reflexivity]. destruct (seg_writable s); [discriminate | reflexivity].
Qed.
Lemma fm_cr_of_seg : forall s, In s tfibsegs -> seg_writable s = false ->
  In (Z.of_N (seg_base s), Z.of_N (seg_size s)) fm_cr.
Proof.
intros s Hin Hw. unfold fm_cr. apply in_map_iff. exists s. split; [reflexivity|].
apply filter_In. split; [exact Hin | rewrite Hw; reflexivity].
Qed.

(* (a) the ranges lie in [0, 2^63) *)
Lemma fm_cr_bounds : Forall (fun r => 0 <= fst r /\ fst r + snd r <= 2 ^ 63) fm_cr.
Proof.
assert (Hb : forallb (fun r => (0 <=? fst r) && (fst r + snd r <=? 2 ^ 63)) fm_cr = true) by (vm_compute; reflexivity).
rewrite forallb_forall in Hb. apply Forall_forall. intros r Hr. specialize (Hb r Hr).
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

(* (d) and in the image's read-only part [0x10000, 0xa5000) *)
Lemma fm_cr_in_image : Forall (fun r => 0x10000 <= fst r /\ fst r + snd r <= 0xa1000) fm_cr.
Proof.
assert (Hb : forallb (fun r => (0x10000 <=? fst r) && (fst r + snd r <=? 0xa1000)) fm_cr = true)
  by (vm_compute; reflexivity).
rewrite forallb_forall in Hb. apply Forall_forall. intros r Hr. specialize (Hb r Hr).
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

(* (b) it covers every read-only byte (FMgxaSeamNorm.ro_covered; its instance ro_covered_fm is the one range
   [0x10000, 0xa5000)) *)
Lemma fm_cr_ro_covered : FMgxaSeamNorm.ro_covered fm_cr.
Proof.
intros a Ha. unfold CJM.ro_addr in Ha.
destruct (find_segment tfibsegs (bv_unsigned a) 1) as [s|] eqn:Hf; [|discriminate Ha].
destruct (find_segment_some_spec _ _ _ _ Hf) as (Hin & H1 & H2).
apply negb_true_iff in Ha.
apply Exists_exists. exists (Z.of_N (seg_base s), Z.of_N (seg_size s)).
split; [exact (fm_cr_of_seg s Hin Ha) | unfold in_zr; cbn [fst snd]; lia].
Qed.

(* membership in a list of ranges is decidable *)
Lemma in_zr_list_dec : forall a (l : list (Z * Z)), Exists (in_zr a) l \/ ~ Exists (in_zr a) l.
Proof.
intros a l. induction l as [|r l IH]; [right; intros X; inversion X|].
destruct (Z_le_gt_dec (fst r) a) as [L1|L1]; [destruct (Z_lt_ge_dec a (fst r + snd r)) as [L2|L2]|].
- left. apply Exists_cons_hd. unfold in_zr. lia.
- destruct IH as [IH|IH]; [left; apply Exists_cons_tl; exact IH|].
  right. intros X. inversion X as [? ? Hx|? ? Hx]; subst; [unfold in_zr in Hx; lia | exact (IH Hx)].
- destruct IH as [IH|IH]; [left; apply Exists_cons_tl; exact IH|].
  right. intros X. inversion X as [? ? Hx|? ? Hx]; subst; [unfold in_zr in Hx; lia | exact (IH Hx)].
Qed.

(* a byte of fm_cr is a read-only image byte below 0xa5000 *)
Lemma fm_cr_rom : forall a, Exists (in_zr a) fm_cr -> in_rom tfibsegs a /\ 0x10000 <= a < 0xa1000.
Proof.
intros a Ha. apply Exists_exists in Ha as (r & Hr & Hz).
pose proof (proj1 (Forall_forall _ _) fm_cr_in_image r Hr) as Hb.
destruct (fm_cr_seg r Hr) as (s & Hin & Hw & ->). unfold in_zr in Hz. cbn [fst snd] in Hz, Hb.
split; [|lia]. exists s. split; [exact Hin|]. split; [exact Hw | lia].
Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* (c) consts_view over fm_cr from the two read-only views: an owned static reads by rom_viewO, any other byte by
   rom_viewN, whose errno side condition holds because errno (SegBSyms: TFIB_ERRNO = 0x5e44f4) lies above 0xa5000 *)
Lemma fm_cr_consts_view : forall B (W : world tfibsegs) mem, SegBSyms B ->
  rom_viewN tfibsegs B W mem -> rom_viewO tfibsegs B W mem -> consts_view tfibsegs W mem fm_cr.
Proof.
intros B W mem TB HN HO a Ha. destruct (fm_cr_rom a Ha) as (Hrom & Hlo & Hhi).
destruct (in_zr_list_dec a (as_owned_static B)) as [Ho|Ho].
- exact (HO a Hrom Ho).
- apply (HN a Hrom Ho). rewrite (ts_errno B TB). unfold TFIB_ERRNO. lia.
Qed.
End c.
