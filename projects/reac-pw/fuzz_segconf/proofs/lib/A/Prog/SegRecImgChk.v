(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/Prog/CmdRecImgChk.v (origin/ossv/recipes 501c0d516c69) for reac-pw/fuzz_segconf's image A (fuzz_segconf.asan): module paths; Cmd*/cmd_* -> Seg*/seg_*; the stack guard 0x6045d8 -> SegInstA.guardA (0x5ff078); the read-only end 0xa7108 -> 0xa3748; musl's word-loop constants [0x10358, 0x10358 + 32) -> [SegInstA.memchr_loA, SegInstA.memchr_hiA) (0x10350, 0x10370). *)
(* The closed checks over the pinned image (tfibsegs) and the record's lists that cmd_img_facts_tfib uses
   (lib/A/Prog/CmdRecImg.v): one boolean computation each, closed by vm_compute. The slowest is crf_rom_all (every
   byte of the two read-only segments, 610,304 image reads, ~27 s and the same again at Qed). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YG0v YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import AF0m AB1v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegRo SegGlob SegRecBase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
(* every one of CmdRo's 209 objects is outside the record's owned ranges and the errno cell, in the image, and
   read-only (a read-only segment, or [CMD_RLO, CMD_RHI)); the image holds CmdRo's bytes *)
Lemma crf_ro_objs_sep : forallb (fun r => forallb (zr_disjointb r) Tfib_owned_static && zr_disjointb r (TFIB_ERRNO, 4)) seg_ro_objs = true.
Proof. vm_compute. reflexivity. Qed.
Lemma crf_ro_objs_img : forallb (crf_img_rangeb tfibsegs) seg_ro_objs = true.
Proof. vm_compute. reflexivity. Qed.
Lemma crf_ro_objs_ro : forallb (crf_ro_rangeb tfibsegs SEG_RLO SEG_RHI) seg_ro_objs = true.
Proof. vm_compute. reflexivity. Qed.
Lemma crf_ro_image_chk : forallb (fun e => crf_bytes_b (crf_rom tfibsegs) (fst e) (snd e)) seg_ro_list = true.
Proof. vm_compute. reflexivity. Qed.
(* every byte after a literal's end up to its word end is in a read-only segment *)
Lemma crf_tails_chk : forallb (fun e => crf_zallt (crf_rom_b tfibsegs) (e + 1) (Z.to_nat (7 - e mod 8))) seg_ro_ends = true.
Proof. vm_compute. reflexivity. Qed.
(* every byte of the read-only segments has an image byte (their file size is their memory size) *)
Lemma crf_rom_all : forallb (fun s => if seg_writable s then true else
crf_zallt (fun a => crf_some (seg_rom tfibsegs (Z_to_bv 64 a))) (Z.of_N (seg_base s)) (N.to_nat (seg_size s))) tfibsegs = true.
Proof. vm_compute. reflexivity. Qed.
(* every byte of the relro range has an image byte *)
Lemma crf_relro_some : crf_zallt (fun a => crf_some (seg_rom tfibsegs (Z_to_bv 64 a))) SEG_RLO (Z.to_nat (SEG_RHI - SEG_RLO)) = true.
Proof. vm_compute. reflexivity. Qed.
(* every segment starts and ends on an 8-byte boundary *)
Lemma crf_seg_al : forallb (fun s => (Z.of_N (seg_base s) mod 8 =? 0) && (Z.of_N (seg_size s) mod 8 =? 0)) tfibsegs = true.
Proof. vm_compute. reflexivity. Qed.
(* g_rec, record.spill and g_quitting: in the image, outside the owned ranges and the errno cell *)
Lemma crf_pg_img : forallb (fun r => crf_img_rangeb tfibsegs (fst r, snd r - fst r)) seg_PG = true.
Proof. vm_compute. reflexivity. Qed.
Lemma crf_pg_sep : forallb (fun r => forallb (zr_disjointb (fst r, snd r - fst r)) Tfib_owned_static) seg_PG = true.
Proof. vm_compute. reflexivity. Qed.
Lemma crf_pg_noerrno : forallb (fun r => zr_disjointb (fst r, snd r - fst r) (TFIB_ERRNO, 4)) seg_PG = true.
Proof. vm_compute. reflexivity. Qed.
(* the errno cell and the stack guard have image bytes; read-only bytes end before the end of RELRO *)
Lemma crf_tfib_errno_rom : crf_zallf (fun a => crf_some (seg_rom tfibsegs (Z_to_bv 64 a))) TFIB_ERRNO 4 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma crf_tfib_guard_rom : crf_zallf (fun a => crf_some (seg_rom tfibsegs (Z_to_bv 64 a))) SegInstA.guardA 8 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma crf_tfib_ro_end : crf_ro_endb tfibsegs 0x10000 0xa3748 = true.
Proof. vm_compute. reflexivity. Qed.
(* the strnlen wrapper's musl constants [0x10358, 0x10378) are in a read-only segment *)
Lemma crf_snl_rom : crf_zallt (crf_rom_b tfibsegs) SegInstA.memchr_loA (Z.to_nat (SegInstA.memchr_hiA - SegInstA.memchr_loA)) = true.
Proof. vm_compute. reflexivity. Qed.
