(* the release classifier image (sha256 ...), in the place of package 3's Plain/PImg.v.
   The image is the elf-snapshot X.v of (logical root N). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.ClsW.Lib Require Import PropExec MState Mem Image.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.ClsW.Snap Require Export X.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition psegs : list Segment := X.M.loaded_segments.
Definition p_init_pc : N := X.M.init_pc.
Definition p_phdrs : PhdrInfo := X.M.phdrs.

(* The four LOAD segments: base, size, read, write, execute. *)
Lemma p_seg_flags :
  map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_readable s, seg_writable s, seg_executable s)) psegs
  = [(0x10000, 0x1000, true, false, false); (0x11000, 0x2000, true, false, true);
     (0x13000, 0x1000, true, true, false); (0x14000, 0x21000, true, true, false)].
Proof. vm_compute. reflexivity. Qed.

Lemma reserved_top_cls : reserved_top (segments_reserved psegs) = 0x35000.
Proof. vm_compute. reflexivity. Qed.

Lemma p_init_pc_val : Z.of_N p_init_pc = 0x113a8.
Proof. reflexivity. Qed.

Lemma p_phdrs_val : p_phdrs = {| ph_addr := 0x10040%N; ph_ent := 56%N; ph_num := 10%N |}.
Proof. reflexivity. Qed.
