From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK0i YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import Mem Cells Step Frame.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import Img0 Contract FrameAPI OutForm.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import StdioModel pcap_source_struct
  pcap_source_struct_next pcap_source_next_c.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot Require Import PInv PWalkDef PWalk.
Import ListNotations.
Open Scope Z_scope.

(* The cuts of the plain slot (entry 0x12c04). A cut is a CUTST state at a pc of the slot with the slot's heap
   blocks hb and the facts P that the next segment and the next callee need beyond FR; its output function o is
   the output of the rest of the run (Hcut_o X o). Register numbers: s0 8, s1 9, a0 10, a1 11, a2 12, s2 18,
   s3 19, s4 20, s5 21, s6 22, s8 24, s9 25, s11 27. *)

(* Ghost values: the file F (the payload without its first byte), its length, the first byte d, cap = 8 d,
   the byte order of the file, the size of the record buffer, the source of the file copy. *)
Definition gF (g : ghost) : list byte := tl (g_in g).
Definition gn (g : ghost) : Z := Z.of_nat (length (gF g)).
Definition gd (g : ghost) : Z := match g_in g with [] => 0 | d :: _ => bv_unsigned d end.
Definition gcap (g : ghost) : Z := 8 * gd g.
Definition gswz (g : ghost) : Z := pcap_sw (gF g).
Definition gsw (g : ghost) : bool := gswz g =? 1.
Definition gbn (g : ghost) : Z := Z.max (gcap g) 1.
Definition gsrc (g : ghost) : Z := match g_in g with [] => g_p g | _ :: _ => g_p g + 1 end.

(* The record the reader stops at from position p, the reader's first answer, the output of the call after
   the reopen. *)
Definition gq (g : ghost) (p : Z) : Z := psn_q (gsw g) (gF g) (gcap g) p.
Definition gfirst (g : ghost) : Z := res_of (gsw g) (gF g) (gcap g) (gq g 24).
Definition out24 (g : ghost) : list byte := snd (fst (psn_chain (gsw g) (gF g) (gcap g) 24)).

(* The output of the walk after the call from p: the rest of the walk when the call found a fit record. *)
Definition wrest (g : ghost) (p : Z) : list byte :=
  if is_fit (kind (gsw g) (gF g) (gcap g) (gq g p))
  then walk_out (S (length (gF g))) (gsw g) (gF g) (gcap g) (pos_of (gsw g) (gF g) (gcap g) (gq g p))
  else [].

Definition oOUT (g : ghost) : list byte := OUT (g_in g).
Definition oKD (g : ghost) : list byte := wrest g 24 ++ out24 g.
Definition oK4 (p : Z) (g : ghost) : list byte :=
  walk_out (S (length (gF g))) (gsw g) (gF g) (gcap g) (pos_of (gsw g) (gF g) (gcap g) (gq g p)) ++ out24 g.
Definition oKL2 (p : Z) (g : ghost) : list byte := wrest g p ++ out24 g.
Definition oNil (g : ghost) : list byte := [].

(* Memory facts. sb_ok: the stdio state the reader's calls need; err_ok: the stderr FILE (its mode field is
   the output invariant GI). *)
Definition err_ok (m : word -> option byte) : Prop := exists fl md, errf m fl md.
Definition sb_ok (m : word -> option byte) : Prop := stdio_ok m /\ guard_ok m /\ err_ok m.

(* The reader's cells at fsp g + 32 with file h (h = 0: closed), after an open, and with any other cells. *)
Definition ps_on (g : ghost) (h : Z) (m : word -> option byte) : Prop :=
  exists (sw olen vtag vid : word) (pad : list byte),
    rw_cells rsegs m (fsp g + 32) (ps_cells (wz h) sw olen vtag vid pad).
Definition ps_open (g : ghost) (h : Z) (m : word -> option byte) : Prop :=
  exists pad, rw_cells rsegs m (fsp g + 32) (ps_cells (wz h) (wz (gswz g)) (wz 0) (wz 0) (wz 0) pad).

(* The post of pcap_source_next called from file position p with the slot's arguments (ps at fsp g + 32,
   ts at fsp g + 24, the reader's links 0). *)
Definition psn_post (g : ghost) (p h b buf : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  exists (lol lvt lvid tsv : word) (pad bj : list byte), Z.of_nat (length bj) = gbn g /\
    psn_open_post (gsw g) (gF g) (gcap g) p regs m (fsp g + 32) buf (fsp g + 24) h b (gswz g) lol lvt lvid pad
      (wz 0) (wz 0) bj tsv.

Definition hb_b (g : ghost) (b : Z) : list (Z * Z) := [(b, gn g)].
Definition hb_bh (g : ghost) (b h : Z) : list (Z * Z) := [(b, gn g); (h, 1304)].
Definition hb_bhu (g : ghost) (b h buf : Z) : list (Z * Z) := [(b, gn g); (h, 1304); (buf, gbn g)].
Definition hb_bu (g : ghost) (b buf : Z) : list (Z * Z) := [(b, gn g); (buf, gbn g)].
Definition hb_buh (g : ghost) (b buf h : Z) : list (Z * Z) := [(b, gn g); (buf, gbn g); (h, 1304)].

(* K1 0x12c7c: malloc answered the file copy b. *)
Definition P_K1 (g : ghost) (b : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  getr regs 10 = wz b /\ b <> 0 /\ getr regs 8 = wz (gd g) /\ getr regs 9 = wz (gsrc g) /\
  getr regs 18 = wz (gn g) /\ getr regs 22 = wz (symaddr Symbols.Plain.s_g_file_len) /\
  sb_ok m /\ ofl_empty m /\ q64 m (symaddr Symbols.Plain.s_g_file_len) (gn g) /\ q64 m (symaddr Symbols.Plain.s_g_file) (gsrc g) /\ bytes_at rsegs m (gsrc g) (gF g).

(* K2g 0x12cc4: the reader accepted the file. *)
Definition P_K2g (g : ghost) (b h : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  getr regs 10 = wz 0 /\ getr regs 8 = wz (gd g) /\ getr regs 20 = wz b /\ getr regs 22 = wz (symaddr Symbols.Plain.s_g_file_len) /\
  pcap_good (gF g) = true /\ sb_ok m /\ q64 m (symaddr Symbols.Plain.s_g_file_len) (gn g) /\ q64 m (symaddr Symbols.Plain.s_g_file) b /\
  ps_open g h m /\ mstl m h b (gF g) 24 (wz 0) (wz 0) /\ ofl_one m h.

(* K2r 0x12cc4: the reader refused the file (segment B reads the magic from b and the f cell, then frees b). *)
Definition P_K2r (g : ghost) (b : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  getr regs 10 = wz (-1) /\ getr regs 8 = wz (gd g) /\ getr regs 20 = wz b /\ getr regs 22 = wz (symaddr Symbols.Plain.s_g_file_len) /\
  pcap_good (gF g) = false /\ sb_ok m /\ ofl_empty m /\ q64 m (symaddr Symbols.Plain.s_g_file_len) (gn g) /\ bytes_at rsegs m b (gF g) /\
  ps_on g 0 m.

(* K3 0x12d74: malloc answered the record buffer buf. *)
Definition P_K3 (g : ghost) (b h buf : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  getr regs 10 = wz buf /\ buf <> 0 /\ getr regs 8 = wz (gd g) /\ getr regs 9 = wz (gcap g) /\
  getr regs 20 = wz b /\ getr regs 22 = wz (symaddr Symbols.Plain.s_g_file_len) /\
  pcap_good (gF g) = true /\ sb_ok m /\ q64 m (symaddr Symbols.Plain.s_g_file_len) (gn g) /\ q64 m (symaddr Symbols.Plain.s_g_file) b /\
  ps_open g h m /\ mstl m h b (gF g) 24 (wz 0) (wz 0) /\ ofl_one m h.

(* KD 0x12d9c: the first call of pcap_source_next (from position 24) returned. *)
Definition P_KD (g : ghost) (b h buf : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  getr regs 9 = wz (gcap g) /\ getr regs 18 = wz buf /\ getr regs 20 = wz b /\ getr regs 22 = wz (symaddr Symbols.Plain.s_g_file_len) /\
  pcap_good (gF g) = true /\ sb_ok m /\ q64 m (symaddr Symbols.Plain.s_g_file_len) (gn g) /\ q64 m (symaddr Symbols.Plain.s_g_file) b /\ q64 m (fsp g + 8) (gd g) /\
  ofl_one m h /\ psn_post g 24 h b buf regs m.

(* K4 i p 0x12dcc: the loop head for record i; the reader's call from position p found the fit record gq g p. *)
Definition P_K4 (g : ghost) (i p b h buf : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  getr regs 9 = wz (gcap g) /\ getr regs 18 = wz buf /\ getr regs 20 = wz b /\ getr regs 21 = wz 0xff00 /\
  getr regs 22 = wz (symaddr Symbols.Plain.s_g_file_len) /\ getr regs 24 = wz p /\ getr regs 25 = wz i /\
  getr regs 27 = wz (1000000 * 2 ^ 32) /\
  0 <= i /\ 24 + 17 * i <= p /\ kind (gsw g) (gF g) (gcap g) (gq g p) = KFit /\
  getr regs 12 = wz (rec_len (gsw g) (gF g) (gq g p)) /\
  (i = 0 /\ rec_len (gsw g) (gF g) (gq g p) = gfirst g \/ 0 < i /\ getr regs 11 = wz (gfirst g)) /\
  pcap_good (gF g) = true /\ sb_ok m /\ q64 m (symaddr Symbols.Plain.s_g_file_len) (gn g) /\ q64 m (symaddr Symbols.Plain.s_g_file) b /\ q64 m (fsp g + 8) (gd g) /\
  ofl_one m h /\ mstl m h b (gF g) (pos_of (gsw g) (gF g) (gcap g) (gq g p)) (wz 0) (wz 0) /\
  (exists pad, rw_cells rsegs m (fsp g + 32)
     (ps_cells (wz h) (wz (gswz g)) (wz (orig (gsw g) (gF g) (gq g p)))
        (if tagged (gsw g) (gF g) (gq g p) then wz 1 else wz 0)
        (if tagged (gsw g) (gF g) (gq g p) then wz (rec_vid (gF g) (gq g p)) else wz 0) pad)) /\
  rw_cells rsegs m (fsp g + 16) [C8 (wz (buf + 12))] /\
  rw_cells rsegs m (fsp g + 24) [C8 (wz (rec_ts (gsw g) (gF g) (gq g p)))] /\
  bytes_at rsegs m buf (rec_bytes (gsw g) (gF g) (gq g p)).

(* KL2 j p 0x13044: the loop's call of pcap_source_next from position p (s9 = j) returned. *)
Definition P_KL2 (g : ghost) (j p b h buf : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  getr regs 9 = wz (gcap g) /\ getr regs 18 = wz buf /\ getr regs 19 = wz (gfirst g) /\ getr regs 20 = wz b /\
  getr regs 21 = wz 0xff00 /\ getr regs 22 = wz (symaddr Symbols.Plain.s_g_file_len) /\ getr regs 24 = wz p /\ getr regs 25 = wz j /\
  getr regs 27 = wz (1000000 * 2 ^ 32) /\ 24 + 17 * j <= p /\ p <= gn g /\
  pcap_good (gF g) = true /\ sb_ok m /\ q64 m (symaddr Symbols.Plain.s_g_file_len) (gn g) /\ q64 m (symaddr Symbols.Plain.s_g_file) b /\ q64 m (fsp g + 8) (gd g) /\
  ofl_one m h /\ rw_cells rsegs m (fsp g + 16) [C8 (wz (buf + 12))] /\ psn_post g p h b buf regs m.

(* K5 p 0x1305c: the walk's end; the reader's call from position p found no fit record. *)
Definition P_K5 (g : ghost) (p b h buf : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  getr regs 12 = wz (res_of (gsw g) (gF g) (gcap g) (gq g p)) /\
  kind (gsw g) (gF g) (gcap g) (gq g p) <> KFit /\ getr regs 24 = wz p /\ 24 <= p /\ p <= gn g /\
  getr regs 9 = wz (gcap g) /\ getr regs 18 = wz buf /\ getr regs 19 = wz (gfirst g) /\ getr regs 20 = wz b /\
  getr regs 22 = wz (symaddr Symbols.Plain.s_g_file_len) /\
  pcap_good (gF g) = true /\ sb_ok m /\ q64 m (symaddr Symbols.Plain.s_g_file_len) (gn g) /\ q64 m (symaddr Symbols.Plain.s_g_file) b /\ q64 m (fsp g + 8) (gd g) /\
  ofl_one m h /\ mstl m h b (gF g) (pos_of (gsw g) (gF g) (gcap g) (gq g p)) (wz 0) (wz 0) /\
  (exists (lol lvt lvid : word) (pad : list byte),
     rw_cells rsegs m (fsp g + 32) (ps_cells (wz h) (wz (gswz g)) lol lvt lvid pad)).

(* K6 0x1310c: pcap_source_close returned. *)
Definition P_K6 (g : ghost) (b buf : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  getr regs 9 = wz (gcap g) /\ getr regs 18 = wz buf /\ getr regs 19 = wz (gfirst g) /\ getr regs 20 = wz b /\
  pcap_good (gF g) = true /\ sb_ok m /\ ofl_empty m /\ q64 m (symaddr Symbols.Plain.s_g_file_len) (gn g) /\ q64 m (symaddr Symbols.Plain.s_g_file) b /\
  bytes_at rsegs m b (gF g) /\ ps_on g 0 m.

(* K7 0x13124: the second pcap_source_open returned (file h). *)
Definition P_K7 (g : ghost) (b buf h : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  getr regs 10 = wz 0 /\ getr regs 9 = wz (gcap g) /\ getr regs 18 = wz buf /\ getr regs 19 = wz (gfirst g) /\
  getr regs 20 = wz b /\ sb_ok m /\ ps_open g h m /\ mstl m h b (gF g) 24 (wz 0) (wz 0) /\ ofl_one m h.

(* K8 0x1313c: the call of pcap_source_next after the reopen returned. *)
Definition P_K8 (g : ghost) (b buf h : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  getr regs 10 = wz (gfirst g) /\ getr regs 9 = wz (gcap g) /\ getr regs 18 = wz buf /\
  getr regs 19 = wz (gfirst g) /\ getr regs 20 = wz b /\ sb_ok m /\ ps_on g h m /\
  (exists q, mstl m h b (gF g) q (wz 0) (wz 0)) /\ ofl_one m h.

(* K9 0x13148: the second pcap_source_close returned. *)
Definition P_K9 (g : ghost) (b buf : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  getr regs 9 = wz (gcap g) /\ getr regs 18 = wz buf /\ getr regs 20 = wz b /\
  sb_ok m /\ ofl_empty m /\ ps_on g 0 m.

(* K10 0x1315c: the call of pcap_source_next on the closed reader returned. *)
Definition P_K10 (g : ghost) (b buf : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  getr regs 10 = wz (-1) /\ getr regs 18 = wz buf /\ getr regs 20 = wz b /\ sb_ok m /\ ofl_empty m.

(* K11 0x1316c: free(buf) returned. *)
Definition P_K11 (b : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  getr regs 20 = wz b /\ sb_ok m /\ ofl_empty m.

(* K12 0x13174: free(b) returned (also the end of the refused path). For the return (PGlue.post_FR):
   err_ok gives GI (PImg.GI_of_errf), ofl_empty the open-file head (PGlue.ofl_back), FR the saved bytes. *)
Definition P_K12 (regs : bvmap 5 word) (m : word -> option byte) : Prop := err_ok m /\ ofl_empty m.

Section Cuts.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.

(* The output of each cut: Inv_K1 .. Inv_K3 oOUT, Inv_KD oKD, Inv_K4 i p (oK4 p), Inv_KL2 j p (oKL2 p),
   Inv_K5 p .. Inv_K7 out24, Inv_K8 .. Inv_K12 oNil. *)
Definition Inv_K1 (g : ghost) (c : config) : Prop :=
  exists b km, CUTST B APIf ra empty g (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x78)%Z) km (hb_b g b) (P_K1 g b) c.
Definition Inv_K2g (g : ghost) (c : config) : Prop :=
  exists b h km, CUTST B APIf ra empty g (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0xc0)%Z) km (hb_bh g b h) (P_K2g g b h) c.
Definition Inv_K2r (g : ghost) (c : config) : Prop :=
  exists b km, CUTST B APIf ra empty g (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0xc0)%Z) km (hb_b g b) (P_K2r g b) c.
Definition Inv_K3 (g : ghost) (c : config) : Prop :=
  exists b h buf km, CUTST B APIf ra empty g (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x170)%Z) km (hb_bhu g b h buf) (P_K3 g b h buf) c.
Definition Inv_KD (g : ghost) (c : config) : Prop :=
  exists b h buf km, CUTST B APIf ra empty g (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x198)%Z) km (hb_bhu g b h buf) (P_KD g b h buf) c.
Definition Inv_K4 (i p : Z) (g : ghost) (c : config) : Prop :=
  exists b h buf km, CUTST B APIf ra empty g (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x1c8)%Z) km (hb_bhu g b h buf) (P_K4 g i p b h buf) c.
Definition Inv_KL2 (j p : Z) (g : ghost) (c : config) : Prop :=
  exists b h buf km, CUTST B APIf ra empty g (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x440)%Z) km (hb_bhu g b h buf) (P_KL2 g j p b h buf) c.
Definition Inv_K5 (p : Z) (g : ghost) (c : config) : Prop :=
  exists b h buf km, CUTST B APIf ra empty g (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x458)%Z) km (hb_bhu g b h buf) (P_K5 g p b h buf) c.
Definition Inv_K6 (g : ghost) (c : config) : Prop :=
  exists b buf km, CUTST B APIf ra empty g (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x508)%Z) km (hb_bu g b buf) (P_K6 g b buf) c.
Definition Inv_K7 (g : ghost) (c : config) : Prop :=
  exists b buf h km, CUTST B APIf ra empty g (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x520)%Z) km (hb_buh g b buf h) (P_K7 g b buf h) c.
Definition Inv_K8 (g : ghost) (c : config) : Prop :=
  exists b buf h km, CUTST B APIf ra empty g (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x538)%Z) km (hb_buh g b buf h) (P_K8 g b buf h) c.
Definition Inv_K9 (g : ghost) (c : config) : Prop :=
  exists b buf km, CUTST B APIf ra empty g (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x544)%Z) km (hb_bu g b buf) (P_K9 g b buf) c.
Definition Inv_K10 (g : ghost) (c : config) : Prop :=
  exists b buf km, CUTST B APIf ra empty g (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x558)%Z) km (hb_bu g b buf) (P_K10 g b buf) c.
Definition Inv_K11 (g : ghost) (c : config) : Prop :=
  exists b km, CUTST B APIf ra empty g (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x568)%Z) km (hb_b g b) (P_K11 b) c.
Definition Inv_K12 (g : ghost) (c : config) : Prop :=
  exists km, CUTST B APIf ra empty g (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x570)%Z) km [] P_K12 c.

(* The order of the heap blocks of a cut is free. *)
Lemma cutst_perm : forall g pc km hb hb' P c, Permutation hb hb' ->
  CUTST B APIf ra empty g pc km hb P c -> CUTST B APIf ra empty g pc km hb' P c.
Proof.
  intros g pc km hb hb' P c HPm (fx' & L & A & regs & mem & md & Hc & Hf & HF & HP & HPr).
  exists fx', L, A, regs, mem, md. split; [exact Hc|]. split; [exact Hf|]. split.
  - unfold FR, RESB in *. rewrite <- (sb_hb_perm (g_b g) hb hb' HPm). exact HF.
  - split; [|exact HPr]. eapply Permutation_trans; [exact HP|]. apply Permutation_app_tail. exact HPm.
Qed.

End Cuts.

(* The reader's FILE holds the file copy: K2g .. K5, K7 and K8 read the file bytes at b from mstl. *)
Lemma mstl_bytes : forall m h b F p pv nx, mstl m h b F p pv nx -> bytes_at rsegs m b F.
Proof. intros m h b F p pv nx (fl & md & q & rb & (buf & _ & _ & _ & HB & _) & _). exact HB. Qed.

Lemma gd_range : forall g, 0 <= gd g < 256.
Proof.
  intros g. unfold gd. destruct (g_in g) as [|d l]; [lia|].
  pose proof (bv_unsigned_in_range 8 d) as R. unfold bv_modulus in R. exact R.
Qed.

Lemma gcap_range : forall g, 0 <= gcap g <= 2040 /\ 1 <= gbn g <= 2040.
Proof. intros g. pose proof (gd_range g). unfold gbn, gcap. lia. Qed.

Lemma gswz_01 : forall g, gswz g = 0 \/ gswz g = 1.
Proof. intros g. unfold gswz, pcap_sw. destruct (pcap_magic (gF g) =? 0xD4C3B2A1); [right | left]; reflexivity. Qed.

Lemma oKD_eq : forall g, oKD g = oKL2 24 g.
Proof. reflexivity. Qed.

Lemma oKL2_split : forall p g, oKL2 p g =
  if is_fit (kind (gsw g) (gF g) (gcap g) (gq g p)) then oK4 p g else out24 g.
Proof. intros p g. unfold oKL2, oK4, wrest. destruct (is_fit _); reflexivity. Qed.

(* The output of a refused file. *)
Lemma OUT_refused : forall g, pcap_good (gF g) = false -> OUT (g_in g) = [].
Proof.
  intros g. unfold gF. destruct (g_in g) as [|d F]; intros H; [reflexivity|]. cbn [tl] in H.
  destruct (Z_lt_le_dec (Z.of_nat (length (d :: F))) (2 ^ 26)) as [L|L].
  - rewrite (OUT_cons d F L), H. reflexivity.
  - apply OUT_big. exact L.
Qed.

(* The output of an accepted file: the first call's chain output, then the rest (the output of KD). *)
Lemma OUT_good : forall g, g_n g < 2 ^ 26 -> pcap_good (gF g) = true ->
  OUT (g_in g) = snd (fst (psn_chain (gsw g) (gF g) (gcap g) 24)) ++ oKD g.
Proof.
  intros g. unfold g_n, oKD, wrest, out24, gq, gsw, gswz, gcap, gd, gF.
  destruct (g_in g) as [|d F]; intros Hn H; [discriminate H|]. cbn [tl] in *.
  rewrite (OUT_cons d F Hn), H.
  rewrite (walk_unfold_len (pcap_sw F =? 1) F (8 * bv_unsigned d) 24) by lia.
  rewrite app_assoc. reflexivity.
Qed.
