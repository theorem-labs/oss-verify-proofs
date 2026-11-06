(* The strlen contract of lib/A/Rt/RtString.v (astrlen_realizes, window ESTACK) at SL_ENTRY = 0x43044, the
   one-instruction trampoline `j 0x430e0` of ___interceptor_strlen. Proved input: lib/A/Rt/RtSStrlenWalk.v
   strlen_icpt_srr, the walk of the whole interceptor from its trampoline to its return (omx-clap-core's
   fuzz_manifest lib/A/FMstrlen.v walk, relocated to this image and stated at ESTACK; the measured depth is
   2,216 bytes: the frame 2,144 and the range check's 72).
   This file reads the walk's premises off the contract's: the string's bytes and its NUL (astr_at) give
   first_byte; aread_ok over astr_len s + 1 gives the visible bytes outside the window, amem_range,
   range_addressable and shadow_hull_vis; atail_vis gives the rest of the NUL's 8-byte word that musl's word loop
   reads; rt_rom_view gives the two word-loop constants 0x10360 and 0x10378 (the 32 bytes from 0x10360 are in
   the first, read-only segment of the image, and no range of Tfib_owned_static and not the errno cell meets
   them). The walk's post is art_post's: the scratch window is present after the call because it is present
   before it (ecall_pre_stk) and the walk keeps every present byte present. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YK0i YK1a YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YK06 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m AF0x.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require RtSStrlenWalk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the 32 bytes 0x10360 .. 0x10380 lie in the first loaded segment, which is read-only *)
Definition sl_rom_chk : bool :=
match nth_error tfibsegs 0 with
| Some s => negb (seg_writable s) && (Z.of_N (seg_base s) <=? 0x10360) && (0x10380 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))
| None => false
end.

Lemma sl_rom_in : forall a, 0x10360 <= a < 0x10380 -> in_rom tfibsegs a.
Proof.
intros a Ha. assert (Hchk : sl_rom_chk = true) by (vm_compute; reflexivity).
unfold sl_rom_chk in Hchk. destruct (nth_error tfibsegs 0) as [s|] eqn:E; [|discriminate].
apply andb_prop in Hchk as [Hchk Hhi]. apply andb_prop in Hchk as [Hw Hlo].
apply negb_true_iff in Hw. apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
exists s. split; [exact (nth_error_In tfibsegs 0 E)|]. split; [exact Hw | lia].
Qed.

(* ... and no owned static range and not the errno cell meets them *)
Lemma sl_rom_unowned : forall B, PcapSyms B -> forall a, 0x10360 <= a < 0x10380 ->
~ Exists (in_zr a) (as_owned_static B) /\ ~ aerrno_cell B a.
Proof.
intros B TB a Ha.
assert (Hown : forallb (fun r : Z * Z => (0x10380 <=? fst r) || (fst r + snd r <=? 0x10360)) Tfib_owned_static = true)
by (vm_compute; reflexivity).
split.
- intros HX. rewrite (ts_owned B TB) in HX. apply Exists_exists in HX as (r & Hr & Hin).
rewrite forallb_forall in Hown. specialize (Hown r Hr).
apply orb_prop in Hown as [H1|H1]; apply Z.leb_le in H1; unfold in_zr in Hin; lia.
- unfold aerrno_cell. rewrite (ts_errno B TB). unfold TFIB_ERRNO. lia.
Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma sl_mconsts : forall B, PcapSyms B -> forall (W : world tfibsegs) mem,
rt_rom_view tfibsegs B W mem -> RtSStrlenWalk.mconsts_view W mem.
Proof.
intros B TB W mem HROM a Ha. pose proof RtSStrlenWalk.mc_bounds as [MB1 MB2]. rewrite MB1, MB2 in Ha.
destruct (sl_rom_unowned B TB a Ha) as [U1 U2].
exact (HROM a (sl_rom_in a Ha) U1 U2).
Qed.

Theorem cmd_strlen : forall (B : asyms), AR_laws tfibsegs B -> PcapSyms B -> astrlen_realizes tfibsegs B RtSStrlenWalk.SL_ENTRY.
Proof.
intros B LAWS TB ly S W regs mem md x s HPRE G10 Hx HSTR HRD HTAIL HROM.
pose proof HPRE as (HEP & Hslo & Hpres).
destruct HRD as (Hx0 & Hxn & Hn & Hsrc & Ham & Hra & Hhull).
destruct HSTR as (HB & HNZ).
unfold astr_len in *.
assert (Hk0 : 0 <= Z.of_nat (length s)) by lia.
assert (Hk32 : Z.of_nat (length s) + 1 < 2 ^ 32) by lia.
assert (Hxk : x + Z.of_nat (length s) + 1 <= 2 ^ 63) by lia.
(* first_byte: the bytes before index len are visible and not NUL, the byte at len is the NUL *)
assert (Hfb : first_byte tfibsegs W mem x (Z.of_nat (length s) + 1) 0 (Z.of_nat (length s))).
{ split; [lia|]. split.
- intros i Hi. exists (bv_unsigned (nth (Z.to_nat i) (s ++ [Z_to_bv 8 0]) (Z_to_bv 8 0))). split.
+ replace (x + i) with (x + Z.of_nat (Z.to_nat i)) by lia. apply HB. rewrite length_app. cbn [length]. lia.
+ rewrite app_nth1 by lia. apply byte_nz_u. intros E. apply HNZ. rewrite <- E. apply nth_In. lia.
- intros _. rewrite (HB (length s) ltac:(rewrite length_app; cbn [length]; lia)).
rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity. }
(* src_ok and the band: every byte up to the NUL is visible and outside the scratch window *)
assert (Hsrc' : src_ok tfibsegs W regs mem x (Z.of_nat (length s) + 1)) by (intros a Ha; exact (Hsrc a Ha)).
assert (Hband : forall a, x <= a <= x + Z.of_nat (length s) -> ~ (spZ regs - ESTACK <= a < spZ regs))
by (intros a Ha; exact (proj2 (Hsrc a ltac:(lia)))).
eapply SRr_mono.
- exact (RtSStrlenWalk.strlen_icpt_srr B LAWS TB ly S W regs mem md x (Z.of_nat (length s)) HEP Hslo Hpres G10 Hx
Hk0 Hk32 Hxk Hfb Hsrc' Hband Ham Hra (Hhull ltac:(lia)) HTAIL (sl_mconsts B TB W mem HROM)).
- cbv beta. intros W' c' _ (-> & regs' & mem' & md' & Hc & HAR' & HKEEP & Hsbm & A10 & Hfr & Hpres').
unfold art_post. split; [reflexivity|]. exists regs', mem', md'.
split; [exact Hc|]. split; [exact HAR'|]. split; [exact HKEEP|]. split; [exact Hsbm|]. split; [exact A10|].
split; [intros a Ha Hs _; exact (Hfr a Ha Hs)|].
split; [exact Hpres'|].
intros a Ha. apply Hpres'. exact (Hpres a Ha).
Qed.

End c.
