From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file, written for libreac/fuzz_pcap -- lib/B twin of lib/A/Prog/PcapSourceOpenPh.v (a working branch
   e57fbb09a40): pcap_source_open (fuzz_pcap.asan-ubsan 0x811e0, listing offset AF_pcap_source_open = 0xa58, 246
   instructions) on libreac v1.9.0's ASan+UBSan build, the cut between the two walk files.

   The code up to the fopen call is lib/A's ASan code at other pcs (0x811e0..0x812f4 here, 0x8145c..0x81570 there).
   After it the UBSan guards stand before the first use of ps and before the header read (measured:
   pcap-ubsan-inventory.md (sha256 5b607b62e337; internal record) rows G5 / G6): 0x812f8 `beqz s3` (ps null) and 0x81300 `andi a0,s3,7` /
   0x81304 `bnez a0` (ps not 8-aligned) branch to the `unimp` at 0x8153c, and so does 0x81390 `addi a0,zero,-3` /
   0x81394 `bgeu s4,a0` (the header buffer F + 32 within 3 bytes of the top). The f test moves to 0x81364 `beqz a3`.

   PcapSourceOpen.v walks the head: the prologue (0x811e0..), __asan_stack_malloc_1 (0x81248) and the class-1 frame
   F, its header and shadow (0x8127c..0x812e4), libreac_fuzz_fopen (0x812f4), the two guards on ps (0x812f8,
   0x81304), the four stores into ps (0x81308..0x81360) and the test of f (0x81364); on f = NULL it stops at the
   branch target 0x813f8 (listing offset OP_CUT_NULL), and otherwise it puts the header buffer in scope
   (0x8136c..0x81374), calls the fread wrapper (0x81388) and stops at its return address 0x8138c (OP_CUT_READ).
   PcapSourceOpenB.v walks the tail from those two cuts: the -1 of the empty input (0x813f8), the short read (0x8138c
   bne -> 0x81400, fclose 0x8140c), the guard on the header buffer (0x81394), the header test (0x81398..0x813d4),
   the bad magic (fclose 0x81450), ps->swapped (0x813f0 / 0x8143c), the epilogue (0x81464 / 0x81474 .. 0x81538) and
   the post. The cut states are lib/A's text: the registers at the cuts are lib/A's (s2 = s6 = F, s3 = ps, s4 / s9 by
   cut, s5 = F's shadow, s7 = the shadow base, s8 = ps's shadow), and the machine frame is lib/A's (ra and s0 .. s9
   at sp0 - 8 .. sp0 - 88, 0x811e8..0x81210).
   The two cuts are semantic (`op_from`), so neither file computes the other's symbolic state.

   Every number is read from the pin fuzz_pcap.asan-ubsan (sha256 9e66f771f22af67a...). The listing,
   its names and PAImg are lib/B's (PcapSyms, PcapList, PcapAddr, PcapPa, PcapPaLib); the text is otherwise lib/A's. *)
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
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapSourceOpenDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the cut pcs, as listing offsets (address - 0x80788) ---- *)
Definition OP_CUT_NULL : Z := Eval compute in ((Symbols.AsanUbsan.s_pcap_source_open + 0x218) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.   (* 0x813f8, `addi a0,zero,-1`: the target of 0x81364 `beqz a3` (f = NULL) *)
Definition OP_CUT_READ : Z := Eval compute in ((Symbols.AsanUbsan.s_pcap_source_open + 0x1ac) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.   (* 0x8138c, `bne a0,s9`: the return address of fread (jal 0x81388) *)
Lemma OP_CUTS_pin : pcap_text + OP_CUT_NULL = (symaddr (Symbols.AsanUbsan.s_pcap_source_open + 0x218)%Z) /\ pcap_text + OP_CUT_READ = (symaddr (Symbols.AsanUbsan.s_pcap_source_open + 0x1ac)%Z).
Proof. split; reflexivity. Qed.

(* ---- the frame ---- *)
Definition OP_CID : Z := 1.            (* jal __asan_stack_malloc_1 0x81248; a0 = 0x60 (0x81244) <= fs_frame_bytes 1 = 128 *)
Definition OP_MAGIC : Z := 0x41b58ab3. (* lui a0,0x41b59 0x81280; addiw a0,a0,-0x54d 0x81298; sd a0,0(s6) 0x812a4 *)
Definition OP_HDR : Z := 32.           (* the 24-byte header buffer: addi s4,s6,0x20 0x81368 *)
Definition OP_FLAGPTR : Z := 120.      (* ld a1,0x78(s2) 0x814c8: the slot's last word holds its flag's address *)
(* The 16 shadow bytes of F: 0xf1 x4 (the left redzone, 0x812c8..0x812d4), the buffer's 3 bytes 0xf8 out of scope
   (0x812b8..0x812c0) or 0 in scope (0x8136c..0x81374), 0xf3 x5 (0x812c4, 0x812d8..0x812e4), and 0 x4 as
   __asan_stack_malloc_1 leaves them (zero_shadow of the whole slot). *)
Definition OSH_out : list Z := [241;241;241;241; 248;248;248; 243; 243;243;243;243; 0;0;0;0].
Definition OSH_in : list Z := [241;241;241;241; 0;0;0; 243; 243;243;243;243; 0;0;0;0].

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
(* The read-only image predicate of the statement (ro_img on the ASan pin). *)
Variable roimg : (word -> option byte) -> Prop.

(* ---- the call's context: the variables of tpcap_source_open_specX ---- *)
Record ocx := mkOCX {
  o_STK : Z; o_sp0 : Z; o_FP : list (Z * Z); o_ly : alayout; o_S : astate; o_W0 : world SEGS;
  o_mem0 : word -> option byte; o_md0 : Model; o_own : list (Z * Z);
  o_lyc : alayout; o_Sc : astate; o_W : world SEGS; o_memc : word -> option byte; o_mdc : Model; o_k : Z;
  o_regs : bvmap 5 word; o_ch : list (Z * Z * Z); o_ps : Z; o_n : Z; o_b : Z; o_M : Z; o_C : list Z;
  o_cid : Z; o_pos : Z }.

(* The premises of tpcap_source_open_specX, in its order. *)
Definition op_pre (cx : ocx) : Prop :=
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
  let cid := o_cid cx in
  let pos := o_pos cx in
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) /\
  YK0s.ret_ok (getr regs 1) /\ 4096 <= raZ regs /\
  getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
  getr regs 10 = w64 ps /\ getr regs 11 = w64 (VAL (A_OBJ 3)) /\
  achain lyc (aview SEGS (w_H W) memc) (spZ regs) (s0Z regs) ch /\ In (raZ regs :: spine ch) CTX /\
  spZ regs mod 16 = 0 /\ sp0 - STK <= spZ regs - TPCAP_SOURCE_OPEN_STK /\ spZ regs <= sp0 /\
  spZ regs + 32 <= ly_top lyc /\ Z.of_nat (length (frames Sc)) <= 7 /\
  In (cid, pos) own /\ frame_addr lyc cid pos <= ps /\ ps + 24 <= frame_addr lyc cid pos + fs_frame_bytes cid /\
  ps <> 0 /\ ps mod 8 = 0 /\
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF ps 24 /\
  inFP FP 0 /\
  roimg (rdW W memc) /\
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (VAL (A_OBJ 3)) 13 /\
  shadow_hull_vis (aview SEGS (w_H W) memc) (VAL (A_OBJ 3)) 13 /\
  val_mem SEGS (rdW W memc) (VAL (A_OBJ 4)) 8 n /\ val_mem SEGS (rdW W memc) (VAL (A_OBJ 2)) 8 b /\
  0 <= b < 2 ^ 64 /\
  asource_none SEGS K (rdW W memc) /\
  n = Z.of_nat (length C) /\ n < 2 ^ 26 /\
  (1 <= n -> In (b, n) (ablocks B lyc Sc) /\ garr8 SEGS (rdW W memc) b C /\ bytes_ok C) /\
  asrc_meta_inv SEGS K lyc (rdW W memc) M /\
  st_nev Sc + EV_OPEN <= EV_MAX /\ blocks_bytes Sc + SRC_FILE_BLOCK <= LIVE_MAX /\
  mo_ok MT Sc (mo_malloc MT SRC_FILE_BLOCK) /\
  In [pc_malloc_ra0 (as_code B)] (as_universe B) /\
  (forall c, In c CTX -> In (firstn kUnwindMax (pc_malloc_ra0 (as_code B) ::
     flat_map (fun r => if r =? pc_malloc_ra0 (as_code B) then [] else [r]) (FM_RA :: c))) (as_universe B)).

(* The post the walk proves, for the context. *)
Definition op_post (cx : ocx) : world SEGS -> config -> Prop :=
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
  let cid := o_cid cx in
  let pos := o_pos cx in
  tpcap_source_open_post SK SEGS B K MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ps b C.

(* The frame F the call takes, its flag, and the shadow byte of its first 8 bytes. *)
Definition oF (cx : ocx) (fpos : Z) : Z := frame_addr (o_lyc cx) OP_CID fpos.
Definition oFL (cx : ocx) (fpos : Z) : Z := flag_addr (o_lyc cx) OP_CID fpos.
Definition oSH (cx : ocx) (fpos : Z) : Z := SHADOW_OFF + oF cx fpos / 8.
(* The realigned stack pointer s1 (0x81218, 0x8121c): every call of the body is made with sp = s1. *)
Definition osp1 (cx : ocx) : Z := 32 * ((spZ (o_regs cx) - OPEN_FRAME) / 32).

(* What both cuts hold. fpos: the frame's slot; f: the value stored in ps->f (0x81318); s4, s9: the two registers
   that differ between the cuts; sh: the frame's 16 shadow bytes; kk: the events so far. *)
Definition op_mid (cx : ocx) (fpos f s4v s9v : Z) (sh : list Z) (kk : Z)
  (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
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
  let cid := o_cid cx in
  let pos := o_pos cx in
  let F := oF cx fpos in
  let R := ms_regs ms3 in
  let rd := aview SEGS (w_H W3) (ms_mem ms3) in
  ms_resv ms3 = None /\ ms_svc_pending ms3 = None /\ ms_rom ms3 = seg_rom SEGS /\
  ms_fregs ms3 = fp_regs /\ ms_fcsr ms3 = fp_csr /\
  (* the caller's journal, with this call's frame on top of the caller's own frames *)
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 ((OP_CID, fpos) :: own) ly3 S3 W3 (ms_mem ms3) md3 (k + kk) /\
  0 <= kk <= 1 /\ st_nev S3 <= st_nev Sc + kk /\
  frames S3 = (OP_CID, fpos) :: frames Sc /\ ~ In (OP_CID, fpos) (frames Sc) /\
  (exists fs, S3 = set_fs fs S3) /\
  (* the registers: sp = s1, s0 = the entry sp, s2 = s6 = F, s3 = ps, s5 = F's shadow, s7 = the shadow base,
     s8 = ps's shadow, s4 and s9 by cut, gp, tp, s10, s11 the entry's *)
  getr R 2 = w64 (osp1 cx) /\ getr R 8 = w64 (spZ regs) /\ getr R 9 = w64 (osp1 cx) /\
  getr R 18 = w64 F /\ getr R 19 = w64 ps /\ getr R 20 = w64 s4v /\ getr R 21 = w64 (oSH cx fpos) /\
  getr R 22 = w64 F /\ getr R 23 = w64 SHADOW_OFF /\ getr R 24 = w64 (SHADOW_OFF + ps / 8) /\
  getr R 25 = w64 s9v /\
  getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 26 = getr regs 26 /\ getr R 27 = getr regs 27 /\
  (* the machine frame: ra at sp0' - 8, then s0, s1, s2 .. s9 (0x811e8..0x81210) *)
  rdword rd (spZ regs - 8) = Some (raZ regs) /\
  (forall j, 0 <= j < 10 ->
     rdword rd (spZ regs - 16 - 8 * j) =
     Some (bv_unsigned (getr regs (Z_to_bv 5 (if j <? 2 then 8 + j else 16 + j))))) /\
  (* the frame's header, its flag pointer and its shadow *)
  rdword rd F = Some OP_MAGIC /\ rdword rd (F + 8) = Some (VAL (A_OBJ 10)) /\
  rdword rd (F + 16) = Some (VAL (A_OBJ 11)) /\ rdword rd (F + OP_FLAGPTR) = Some (oFL cx fpos) /\
  length sh = 16%nat /\ (forall i, (i < 16)%nat -> rd (oSH cx fpos + Z.of_nat i) = Some (nth i sh 0)) /\
  (* the struct: f, three zeroed fields, swapped untouched *)
  val_mem SEGS (rdW W3 (ms_mem ms3)) ps 8 f /\ val_mem SEGS (rdW W3 (ms_mem ms3)) (ps + 12) 4 0 /\
  val_mem SEGS (rdW W3 (ms_mem ms3)) (ps + 16) 4 0 /\ val_mem SEGS (rdW W3 (ms_mem ms3)) (ps + 20) 2 0 /\
  (forall i, 8 <= i < 12 -> rd (ps + i) = aview SEGS (w_H W) memc (ps + i)) /\
  (* what is kept of the caller's memory, as the post states it *)
  topen_kept SK SEGS B lyc Sc W memc W3 (ms_mem ms3) (spZ regs - TPCAP_SOURCE_OPEN_STK) (spZ regs) (fun a => ps <= a < ps + 22) /\
  (* the model's descriptors and file system, the meta region, the read-only bytes *)
  m_fds md3 = m_fds mdc /\ m_fs md3 = m_fs mdc /\
  asrc_meta_inv SEGS K ly3 (rdW W3 (ms_mem ms3)) M /\
  arodata_okP SEGS pa_relro_lo pa_relro_hi B rd /\
  (* the call chain at s1 with this call's frame record (sp0', ra, s0) on top *)
  achain ly3 rd (osp1 cx) (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch).

(* The cut of the empty input: libreac_fuzz_fopen returned NULL (only for n = 0), the buffer never went in scope. *)
Definition op_gi_null (cx : ocx) (fpos : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  ms_pc_val ms3 = w64 (BASE + OP_CUT_NULL) /\
  op_mid cx fpos 0 (VAL (A_OBJ 3)) (bv_unsigned (getr (o_regs cx) 25)) OSH_out 1 ly3 S3 W3 ms3 md3 /\
  o_n cx = 0 /\
  ablocks B ly3 S3 = ablocks B (o_lyc cx) (o_Sc cx) /\
  asource_none SEGS K (rdW W3 (ms_mem ms3)) /\
  mo_le MT (o_Sc cx) S3 0.

(* The cut after fread: the stream f is open on the input, fread returned kr = min 24 n into F + 32. *)
Definition op_gi_read (cx : ocx) (fpos : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists f kr,
  ms_pc_val ms3 = w64 (BASE + OP_CUT_READ) /\
  op_mid cx fpos f (oF cx fpos + OP_HDR) 24 OSH_in 1 ly3 S3 W3 ms3 md3 /\
  1 <= o_n cx /\ 4096 <= f /\ f mod 16 = 0 /\
  ablocks B ly3 S3 = ablocks B (o_lyc cx) (o_Sc cx) ++ [(f, SRC_FILE_BLOCK)] /\
  getr (ms_regs ms3) 10 = w64 kr /\ kr = Z.min 24 (o_n cx) /\
  garr8 SEGS (rdW W3 (ms_mem ms3)) (oF cx fpos + OP_HDR) (firstn (Z.to_nat kr) (o_C cx)) /\
  asource_at SEGS K (rdW W3 (ms_mem ms3)) f (o_b cx) (o_C cx) kr /\
  (* fclose's footprint is the caller's to spare or a block this call allocated *)
  (forall x, inFP (asource_fp f) x ->
     inFP (o_FP cx) x \/ in_tmp_block (ablocks B (o_ly cx) (o_S cx)) (ablocks B ly3 S3) x) /\
  mo_le MT (o_Sc cx) S3 (mo_malloc MT SRC_FILE_BLOCK).

(* `op_from GI`: from every state GI describes, the run reaches the post. PcapSourceOpenB.v proves
   op_from op_gi_null and op_from op_gi_read. *)
Definition op_from (GI : ocx -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop) : Prop :=
  forall (cx : ocx) (fpos : Z) ly3 S3 W3 (ms3 : machine_state) md3,
  op_pre cx -> GI cx fpos ly3 S3 W3 ms3 md3 ->
  SRr SEGS W3 (mkCfg ms3 md3) (op_post cx).

End e.
End d.
End b.

(* SK explicit on every exported name that depends on it (a Theorem Labs lane ruling 21:57Z), with guards. *)
Arguments op_pre {rc} SK {PI} B K MT FM_RA CTX roimg cx.
Arguments op_post {fx rc} SK {PI} B K MT cx _ _.
Arguments op_mid {fx rc} SK {PI} B K cx fpos f s4v s9v sh kk ly3 S3 W3 ms3 md3.
Arguments op_gi_null {fx rc} SK {PI} B K MT cx fpos ly3 S3 W3 ms3 md3.
Arguments op_gi_read {fx rc} SK {PI} B K MT cx fpos ly3 S3 W3 ms3 md3.
Arguments op_from {fx rc} SK {PI} B K MT FM_RA CTX roimg GI.
(* Guards with full positional argument lists: each fails if SK becomes implicit. *)
Check (fun (fx : YK11.FPState) (rc : YM05.RunCeil) (SK : YI16.sink_head) (PI : PAImg pcap_listing) B K MT FM_RA CTX roimg GI =>
         op_from (fx := fx) (rc := rc) SK (PI := PI) B K MT FM_RA CTX roimg GI : Prop).
Check (fun (rc : YM05.RunCeil) (SK : YI16.sink_head) (PI : PAImg pcap_listing) B K MT FM_RA CTX roimg cx =>
         op_pre (rc := rc) SK (PI := PI) B K MT FM_RA CTX roimg cx : Prop).
Check (fun (fx : YK11.FPState) (rc : YM05.RunCeil) (SK : YI16.sink_head) (PI : PAImg pcap_listing) B K cx fpos f s4v s9v sh kk ly3 S3 W3 ms3 md3 =>
         op_mid (fx := fx) (rc := rc) SK (PI := PI) B K cx fpos f s4v s9v sh kk ly3 S3 W3 ms3 md3 : Prop).
