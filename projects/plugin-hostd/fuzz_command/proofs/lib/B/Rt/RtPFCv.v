(* Modified by Theorem Labs, 2026-10: relocated from lib/A/Rt/RtPFCv.v to fuzz_command.asan-ubsan by the image-B address relocator (the A-to-B address mapper); replaces the pin-only B file *)
(* consts_view over the read-only list of fuzz_command's snprintf / sprintf contracts (RtPFCmd.CMD_CR, the image's
   non-writable loaded segments, pinned to tfibsegs by cmd_cr_segs; CMD_SNP_CR and CMD_SP_CR have the same body) from
   what a contract gives its proof:
   - the UNOWNED read-only bytes by RtDefs.rt_rom_view, the premise the contracts take;
   - the runtime-OWNED read-only bytes by AR, inside ecall_pre (RtBzAdapt.rom_viewO_of_ARm: every such byte is pinned
     by a constant cell of the per-binary record);
   - the errno cell 0x5e4074 (B/YF0m.v TFIB_ERRNO) lies outside both segments.
   The shared texts (fuzz_manifest's RtPFShared / RtPFSx) take consts_view; this is what lets our texts take rt_rom_view
   (RtPFCmd.cmd_asnprintf_of_sh, RtFSprintfW.spf_walk). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YB1v YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtPFShared RtPFCmd.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtDefs RtBzAdapt.
Import ListNotations.
Local Open Scope Z_scope.

(* CMD_CR is the image's non-writable loaded segments, fuzz_manifest's fm_cr expression over tfibsegs (one computation) *)
Lemma cmd_cr_segs : CMD_CR =
  map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) (List.filter (fun s => negb (seg_writable s)) tfibsegs).
Proof. vm_compute. reflexivity. Qed.

(* each range of CMD_CR lies inside a non-writable segment of the image (one computation) *)
Lemma cmd_cr_rom_b : forallb (fun r => existsb (fun s : Segment => negb (seg_writable s) &&
  (Z.of_N (seg_base s) <=? fst r) && (fst r + snd r <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) tfibsegs)
  CMD_CR = true.
Proof. vm_compute. reflexivity. Qed.

Lemma cmd_cr_rom : forall a, Exists (in_zr a) CMD_CR -> in_rom tfibsegs a.
Proof.
intros a Ha. apply Exists_exists in Ha as (r & Hr & Hz).
pose proof cmd_cr_rom_b as Hb. rewrite forallb_forall in Hb. specialize (Hb r Hr).
apply existsb_exists in Hb as (s & Hs & Hc).
apply andb_prop in Hc as [Hc Hhi]. apply andb_prop in Hc as [Hw Hlo].
apply negb_true_iff in Hw. apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
exists s. split; [exact Hs|]. split; [exact Hw|]. unfold in_zr in Hz. lia.
Qed.

(* the errno cell lies outside CMD_CR (one computation) *)
Lemma cmd_cr_errno_b : forallb (fun r => (fst r + snd r <=? TFIB_ERRNO) || (TFIB_ERRNO + 4 <=? fst r)) CMD_CR = true.
Proof. vm_compute. reflexivity. Qed.

(* membership in a list of ranges is decidable (fuzz_manifest's FMsnprintfCr.v:69-78) *)
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

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis TB : CmdBSyms B.

Lemma cmd_cr_consts_view : forall ly S (W : world tfibsegs) regs mem md,
  ecall_pre tfibsegs B ly S W regs mem md -> RtDefs.rt_rom_view tfibsegs B W mem -> consts_view tfibsegs W mem CMD_CR.
Proof.
intros ly S W regs mem md HPRE HR a Ha.
pose proof (cmd_cr_rom a Ha) as Hrom.
destruct (in_zr_list_dec a (as_owned_static B)) as [Ho|Ho].
- exact (RtBzAdapt.rom_viewO_of_ARm B TB ly S W mem (proj1 (proj1 HPRE)) a Hrom Ho).
- apply (HR a Hrom Ho). unfold RtDefs.aerrno_cell. rewrite (ts_errno B TB). intros He.
  apply Exists_exists in Ha as (r & Hr & Hz).
  pose proof cmd_cr_errno_b as Hb. rewrite forallb_forall in Hb. specialize (Hb r Hr).
  apply orb_prop in Hb as [Hb|Hb]; apply Z.leb_le in Hb; unfold in_zr in Hz; lia.
Qed.
End c.
