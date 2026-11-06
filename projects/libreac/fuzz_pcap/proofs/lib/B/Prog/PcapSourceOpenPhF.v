From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file, written for libreac/fuzz_pcap -- lib/B's own cut of pcap_source_open's head walk (fuzz_pcap.asan-ubsan
   0x811e0, listing offset AF_pcap_source_open = 0xa58, v1.9.0), at the RETURN OF libreac_fuzz_fopen:
   pc = BASE + OP_RET_FOPEN = 0x812f8, the instruction after `jal libreac_fuzz_fopen` (0x812f4).

   Why a second cut: PcapSourceOpen.v walks the entry, the class-1 frame request (__asan_stack_malloc_1 at
   0x81248), the frame header and its 12 shadow bytes (0x8127c..0x812e4) and the call itself, and hands the state
   on; PcapSourceOpenPhM.v walks from here to the two cuts of PcapSourceOpenPh.v (the UBSan guards on ps at
   0x812f8 and 0x81304, the four shadow-checked stores 0x81308..0x81360, the f test 0x81364, the header buffer in
   scope 0x8136c..0x81374 and the fread call 0x81388). The cut is semantic, as PcapSourceOpenPh.v's two are: this
   file states what holds of the machine at 0x812f8, so neither walk computes the other's symbolic state.

   `op_fopen_ret cx fpos h ly2 S2 W2 ms md` says: the pc; the caller's journal with this call's frame on top and
   libreac_fuzz_fopen's one allocator event charged (EV_FUZZ_FOPEN); the registers the rest of the body reads
   (sp = s1 = osp1, s0 = the entry sp, s2 = s6 = F, s3 = ps, s4 = the path literal, s5 = F's shadow,
   s7 = the shadow base, a0 = h, and gp / tp / s10 / s11 the entry's); the machine frame (ra and s0 .. s9), the
   frame's header, its flag pointer, its 16 shadow bytes (OSH_out: the buffer is still out of scope) and the
   unwinder slot *(s1) = F; that nothing of ps is written yet and its 24 bytes are still addressable; what the
   caller keeps (topen_kept with an empty written set, the read-only bytes, the meta region, the descriptors and
   the file system); the call chain at s1 with this call's frame record on top; and libreac_fuzz_fopen's own post,
   split on the input length (PcapFuzzFopenDefs.v tlibreac_fuzz_fopen_post), including the footprint fact the
   fclose calls of the tail need.

   Every number is read from the pin fuzz_pcap.asan-ubsan (sha256 9e66f771f22af67a...). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0s YI16 YG0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05 PcapImgEnd YC5d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym PaShadow.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaRun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSyms PcapList PcapAddr PcapPa PcapPaLib.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapBase.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta PFmemopenISpec.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapFuzzFopenDefs PcapSourceOpenDefs.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSourceOpenPh.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require PcapRelro.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* The cut's pc, as a listing offset (address - 0x80788): 0x812f8, the instruction after the call of
   libreac_fuzz_fopen (`jal -0xb6c` at 0x812f4). *)
Definition OP_RET_FOPEN : Z := Eval compute in ((Symbols.AsanUbsan.s_pcap_source_open + 0x118) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.
Lemma OP_RET_FOPEN_pin : pcap_text + OP_RET_FOPEN = (symaddr (Symbols.AsanUbsan.s_pcap_source_open + 0x118)%Z).
Proof. reflexivity. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg pcap_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ pcap_listing PI).
#[local] Abbreviation VAL := (@pa_val _ pcap_listing PI).
#[local] Abbreviation BASE := (@pa_val _ pcap_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Section e.
Variable B : asyms.
Variable K : asource_syms.
Variable MT : ameter_ops.
Variable FM_RA : Z.
Variable CTX : list (list Z).
Variable roimg : (word -> option byte) -> Prop.

(* What holds at 0x812f8, the return of libreac_fuzz_fopen. h is the handle it returned (a0). *)
Definition op_fopen_ret (cx : ocx) (fpos h : Z) (ly2 : alayout) (S2 : astate) (W2 : world SEGS)
  (ms : machine_state) (md : Model) : Prop :=
  let STK := o_STK cx in
  let sp0 := o_sp0 cx in
  let FP := o_FP cx in
  let ly := o_ly cx in
  let S := o_S cx in
  let W0 := o_W0 cx in
  let mem0 := o_mem0 cx in
  let md0 := o_md0 cx in
  let own := o_own cx in
  let lyc := o_lyc cx in
  let Sc := o_Sc cx in
  let W := o_W cx in
  let memc := o_memc cx in
  let mdc := o_mdc cx in
  let k := o_k cx in
  let regs := o_regs cx in
  let ch := o_ch cx in
  let ps := o_ps cx in
  let n := o_n cx in
  let b := o_b cx in
  let M := o_M cx in
  let C := o_C cx in
  let F := oF cx fpos in
  let R := ms_regs ms in
  let rd := aview SEGS (w_H W2) (ms_mem ms) in
  ms_pc_val ms = w64 (BASE + OP_RET_FOPEN) /\
  ms_resv ms = None /\ ms_svc_pending ms = None /\ ms_rom ms = seg_rom SEGS /\
  ms_fregs ms = fp_regs /\ ms_fcsr ms = fp_csr /\
  (* the caller's journal, with this call's frame on top and libreac_fuzz_fopen's one event charged *)
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 ((OP_CID, fpos) :: own) ly2 S2 W2 (ms_mem ms) md
    (k + EV_FUZZ_FOPEN) /\
  frames S2 = (OP_CID, fpos) :: frames Sc /\ ~ In (OP_CID, fpos) (frames Sc) /\
  st_nev S2 <= st_nev Sc + EV_FUZZ_FOPEN /\ (exists fs, S2 = set_fs fs S2) /\
  (* the registers the rest of the body reads *)
  getr R 2 = w64 (osp1 cx) /\ getr R 9 = w64 (osp1 cx) /\ getr R 8 = w64 (spZ regs) /\
  getr R 18 = w64 F /\ getr R 22 = w64 F /\ getr R 19 = w64 ps /\ getr R 20 = w64 (VAL (A_OBJ 3)) /\
  getr R 21 = w64 (oSH cx fpos) /\ getr R 23 = w64 SHADOW_OFF /\ getr R 10 = w64 h /\
  getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 25 = getr regs 25 /\
  getr R 26 = getr regs 26 /\ getr R 27 = getr regs 27 /\
  (* the machine frame: ra at sp0' - 8, then s0, s1, s2 .. s9 (0x811e8..0x81210) *)
  rdword rd (spZ regs - 8) = Some (raZ regs) /\
  (forall j, 0 <= j < 10 ->
     rdword rd (spZ regs - 16 - 8 * j) =
     Some (bv_unsigned (getr regs (Z_to_bv 5 (if j <? 2 then 8 + j else 16 + j))))) /\
  (* the frame: its header (0x812a4..0x812ac), its flag pointer, its 16 shadow bytes (the buffer still out of
     scope) and the unwinder slot *(s1) (0x8127c) *)
  rdword rd F = Some OP_MAGIC /\ rdword rd (F + 8) = Some (VAL (A_OBJ 10)) /\
  rdword rd (F + 16) = Some (VAL (A_OBJ 11)) /\ rdword rd (F + OP_FLAGPTR) = Some (oFL cx fpos) /\
  (forall i, (i < 16)%nat -> rd (oSH cx fpos + Z.of_nat i) = Some (nth i OSH_out 0)) /\
  rdword rd (osp1 cx) = Some F /\
  (forall a, F <= a < F + fs_frame_bytes OP_CID -> apresent (w_H W2) (ms_mem ms) a) /\
  (* ps: nothing of it is written yet, and its 24 bytes are still addressable *)
  (forall i, 0 <= i < 24 -> rd (ps + i) = aview SEGS (w_H W) memc (ps + i)) /\
  range_addressable rd SHADOW_OFF ps 24 /\
  (* what the caller keeps so far: no byte of its own is written *)
  topen_kept SK SEGS B lyc Sc W memc W2 (ms_mem ms) (spZ regs - TPCAP_SOURCE_OPEN_STK) (spZ regs)
    (fun _ => False) /\
  arodata_okP SEGS pa_relro_lo pa_relro_hi B rd /\
  asrc_meta_inv SEGS K ly2 (rdW W2 (ms_mem ms)) M /\
  m_fds md = m_fds mdc /\ m_fs md = m_fs mdc /\
  (* the call chain at s1 with this call's frame record (sp0', ra, s0) on top *)
  achain ly2 rd (osp1 cx) (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch) /\
  (* libreac_fuzz_fopen's post, split on the input length *)
  (n = 0 -> h = 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\ asource_none SEGS K (rdW W2 (ms_mem ms)) /\
     mo_le MT Sc S2 0) /\
  (* otherwise the stream is open, and fclose's footprint on the tail's paths is the caller's to spare or a block
     this call allocated *)
  (1 <= n -> 4096 <= h /\ h mod 16 = 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(h, SRC_FILE_BLOCK)] /\
     asource_unbuffered SEGS K (rdW W2 (ms_mem ms)) h b C 0 /\ mo_le MT Sc S2 (mo_malloc MT SRC_FILE_BLOCK) /\
     (forall x, inFP (asource_fp h) x -> inFP FP x \/ in_tmp_block (ablocks B ly S) (ablocks B ly2 S2) x)).

(* From the cut, the run reaches the post: what PcapSourceOpenPhM.v proves (given PcapSourceOpenPh.v's two
   `op_from`s), and what PcapSourceOpen.v consumes. *)
Definition op_from_fopen_stmt : Prop :=
  forall (cx : ocx) (fpos h : Z) ly2 S2 (W2 : world SEGS) (ms : machine_state) md,
  op_pre SK B K MT FM_RA CTX roimg cx -> op_fopen_ret cx fpos h ly2 S2 W2 ms md ->
  SRr SEGS W2 (mkCfg ms md) (op_post SK B K MT cx).

End e.
End d.
End b.

(* SK explicit on every exported name (a Theorem Labs lane ruling 21:57Z), with a positional guard. *)
Arguments op_fopen_ret {fx rc} SK {PI} B K MT cx fpos h ly2 S2 W2 ms md.
Arguments op_from_fopen_stmt {fx rc} SK {PI} B K MT FM_RA CTX roimg.
Check (fun (fx : YK11.FPState) (rc : YM05.RunCeil) (SK : YI16.sink_head) (PI : PAImg pcap_listing)
           B K MT cx fpos h ly2 S2 W2 ms md =>
         op_fopen_ret (fx := fx) (rc := rc) SK (PI := PI) B K MT cx fpos h ly2 S2 W2 ms md : Prop).
Check (fun (fx : YK11.FPState) (rc : YM05.RunCeil) (SK : YI16.sink_head) (PI : PAImg pcap_listing)
           B K MT FM_RA CTX roimg =>
         op_from_fopen_stmt (fx := fx) (rc := rc) SK (PI := PI) B K MT FM_RA CTX roimg : Prop).
