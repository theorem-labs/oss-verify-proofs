(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/B twin of lib/A/Prog/PcapSourceClose.v: pcap_source_close (fuzz_pcap.asan-ubsan
   0x81d4c, listing offset AF_pcap_source_close = 0x15c4, 31 instructions) on libreac v1.9.0's ASan+UBSan build, walked
   against lib/A's contract.

   The code is lib/A's ASan code (fuzz_pcap.asan 0x81e90, 27 instructions) with two UBSan guards and a register swap
   (measured: pcap-ubsan-inventory.md (sha256 5b607b62e337; internal record), row G6 and the pcap_source_close row of (c)). After
   the 32-byte frame and the saves of ra, s0 and s1, 0x81d5c `beqz a0` branches to the `unimp` at 0x81db4 when ps is
   null, 0x81d60 `mv s0,a0` (above the GOT load here), and 0x81d64 `andi a0,a0,7` / 0x81d68 `bnez a0` branch to the same
   `unimp` when ps is not 8-aligned. The shadow base is then loaded through the GOT word 0x996f8 (object 1; through a0,
   where the ASan code uses a1) from the cell 0xa17b8 (object 15). The rest is the ASan code at other pcs: the shadow
   check of ps's 8 bytes (0x81d80 `lbu`, 0x81d84 `bnez` to the error path at 0x81db8), f = ps->f (0x81d88), the test of
   f (0x81d8c `beqz` to 0x81da0), the call of the fclose wrapper's 4-byte jump (0x81d90 `jal
   __interceptor_trampoline_fclose`, 0x4161c), the second shadow check (0x81d94, 0x81d98 `bnez` to the error path at
   0x81dc0), ps->f = NULL (0x81d9c `sd zero,0(s0)`), the restores and the return (0x81db0).

   THE GUARDS. The walk's first symbolic run decides both, from the facts on a0 = ps that cl_entry proves (atom 10: ps
   >= 4096 and ps mod 2^3 = 0; ps >= 4096 because ps lies in a frame of the caller (frames_bounds), which gives the
   statement's ps <> 0; the alignment is the statement's ps mod 8 = 0):
     0x81d5c: decide_cond2 (Reusable/YP0e.v:932) through decide_eq (Reusable/YP0m.v:658-672), whose SOff / SLit arm
              (:665-666) tests ranges_disjoint (:653): ps's range [4096, ...] is disjoint from 0, so the branch is not
              taken;
     0x81d68: s_and_ptr (Reusable/YP0m.v:969-980) rewrites ps & 7 to 0 from the alignment fact, so `bnez` sees 0 and is
              not taken.
   These are the decisions of the released UBSan proof for the v1.8 image (proofs/libreac/fuzz_pcap/lib/U/Prog/
   pcap_source_close.v on origin/ossv/recipes c8557374ad2e): close_closed :43 (if_false, premise bv_unsigned a0 <> 0 at
   :23) and :45-46 (ub_align A8, premise bv_unsigned a0 mod 8 = 0 at :23), close_pro :82 and :84-85 (premises :58).

   The contract is lib/A's, not a copy (the shared-text rule): pb_pcap_source_closeX proves lib/A's image-generic
   AC.tpcap_source_close_specX (with AC.tpcap_source_close_post and AC.tclose_kept) at this image's segments SEGS and
   relro window pa_relro_lo / pa_relro_hi of the lib/B PAImg instance (on the pin PcapRelro.PCAP_RLO /
   PcapRelro.PCAP_RHI, lib/B/Prog/PcapRelro.v), at a = BASE + AF_pcap_source_close of the lib/B listing. The image-free constants
   (TPCAP_SOURCE_CLOSE_STK, EV_CLOSE, tclose_fblk) and lemmas are lib/A's too, through AC. The fclose wrapper's contract
   is the Section hypothesis AFCLOSE, of lib/A/Stdio/PFclose.v's image-generic afclose_source_spec type at this image.
   There is no lib/B/Stdio/PFclose.v (that statement takes the image as parameters). AFCLOSE is discharged by the
   asan-ubsan instance of a Theorem Labs lane's fclose walk lib/A/Stdio/WFclose.v, whose lib/B walk twin is
   lib/B/Stdio/WFclose.v (lib/B/Stdio/PFcloseInstB.v's inst_AFCLOSE_U composes it with lib/B/Stdio/WFcloseI.v).
   getr / mkst / seg_rom come from YK11; nothing from lib/Lib is imported. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/B/Prog/PcapSourceClose.v; 2625 of its 2690 lines of code are new or changed and 565 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* pcap_source_open (fuzz_pcap.asan 0x8145c) on libreac v1.9.0's ASan build: the SECOND half of the walk, from the
   two semantic cuts of lib/A/Prog/PcapSourceOpenPh.v to the post tpcap_source_open_post.  PcapSourceOpen.v
   walks the head (0x8145c..) and establishes the cuts; this file proves
   `op_from op_gi_null` and `op_from op_gi_read`.

   What it walks (listing offsets = address - 0x80738):
   - 0xf28 (0x81660) `addi a0,zero,-1` and the jump to the epilogue: libreac_fuzz_fopen returned NULL, which
     happens only for the empty input;
   - 0xec4 (0x815fc) `bne a0,s9`: the fread wrapper returned.  A short read goes to 0xf30 (0x81668), checks the
     shadow byte of ps, reloads ps->f and calls the fclose wrapper (0x81674);
   - 0xec8..0xf04 (0x81600..0x8163c): the little-endian magic of the 24-byte global header, 0xd4c3b2a1 (swapped,
     0xf50 = 0x81688) and 0xa1b2c3d4 (native, 0xf08 = 0x81640), both storing ps->swapped (0x816a4 / 0x81658);
     any other magic goes to 0xf74 (0x816ac) and closes the stream (0x816b8);
   - the epilogue 0xf94 / 0xfa4 (0x816cc / 0x816dc .. 0x817a0): the header buffer out of scope, the retired magic
     0x45e0360e at F, the frame's 16 shadow bytes set to 0xf5, its flag byte cleared (the class-1 side-stack frame
     is given back), the registers restored and `ret`.

   The MACHINE-STACK arm of the epilogue (0x8173c..0x81768, reached by `beqz s2` at 0x816e8) is REFUTED, not
   walked: under the current core AR_const_law (lib/Reusable/YG0d.v) pins the use-after-return cell to 1, so the
   prologue took __asan_stack_malloc_1's frame and s2 = F >= 4096 (a Theorem Labs lane 22:41Z on a Theorem Labs lane's measurement of the
   cell 0xa18c0 after start-up).

   Every ASan report path of this half (0x817a4..0x81818) is unreachable: each check reads the shadow byte of ps,
   and the cut carries range_addressable of ps's 24 bytes, so the shadow engine (lib/Reusable/YCbn.v, token runs
   over the entry mkSHE 19 0 24) decides every one of those branches without a report.

   Callees are Section hypotheses of their exact statement type (afclose_source_spec, asrc_file_meter,
   asource_img_laws, the frame laws).  Nothing from lib/Lib is imported, SK is explicit on every exported name,
   and every number is read from the pin fuzz_pcap.asan (sha256 b7a91d9b1fb0017d...; image root: the
   ORIGINAL v1.9.0 pins, capstone disassembly of the unstripped twin). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
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
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05 YImgTop PcapImgEnd YE00 YE01 YG0p YC5d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym PaShadow.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaRun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal PcapSyms PcapList PcapAddr PcapPa PcapPaLib PcapBase YC4b YC81 YC1g YC1h YC85 PcapFrame PcapSourceClose.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import
PSource PSourceMeta PSourceMeter PFclose.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import
PcapFuzzFopenDefs PcapSourceOpenDefs PcapSourceOpenPh.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* No global sink_head instance is in scope: every journal below uses the Section's SK. *)
Fail Definition opb_sink_head_probe : YI16.sink_head := _.

(* ---- the pcs of this half, as listing offsets ------------------------------------------------------------- *)
Definition OPB_EPI_A : Z := Eval compute in ((Symbols.Asan.s_pcap_source_open + 0x270) - Symbols.Asan.s_libreac_fuzz_fopen)%Z.     (* 0x816cc: the epilogue after a read (the buffer goes out of scope) *)
Definition OPB_EPI_B : Z := Eval compute in ((Symbols.Asan.s_pcap_source_open + 0x280) - Symbols.Asan.s_libreac_fuzz_fopen)%Z.     (* 0x816dc: the epilogue of the NULL path (the buffer never was in scope) *)
Definition OPB_SHORT : Z := Eval compute in ((Symbols.Asan.s_pcap_source_open + 0x20c) - Symbols.Asan.s_libreac_fuzz_fopen)%Z.     (* 0x81668: the short read, before the fclose wrapper *)
Definition OPB_HDR0  : Z := (symaddr ((Symbols.Asan.s_pcap_source_open + 0x1a4) - Symbols.Asan.s_libreac_fuzz_fopen)%Z).     (* 0x81600: the first byte of the magic *)
Definition OPB_SWAP  : Z := (symaddr ((Symbols.Asan.s_pcap_source_open + 0x22c) - Symbols.Asan.s_libreac_fuzz_fopen)%Z).     (* 0x81688: magic 0xd4c3b2a1, ps->swapped = 1 *)
Definition OPB_NATIVE : Z := Eval compute in ((Symbols.Asan.s_pcap_source_open + 0x1e4) - Symbols.Asan.s_libreac_fuzz_fopen)%Z.    (* 0x81640: magic 0xa1b2c3d4, ps->swapped = 0 *)
Definition OPB_BADMAGIC : Z := Eval compute in ((Symbols.Asan.s_pcap_source_open + 0x250) - Symbols.Asan.s_libreac_fuzz_fopen)%Z.  (* 0x816ac: neither magic, before the fclose wrapper *)
Definition OPB_RET1 : Z := Eval compute in ((Symbols.Asan.s_pcap_source_open + 0x21c) - Symbols.Asan.s_libreac_fuzz_fopen)%Z.      (* 0x81678: the return address of the short-read fclose *)
Definition OPB_RET2 : Z := Eval compute in ((Symbols.Asan.s_pcap_source_open + 0x260) - Symbols.Asan.s_libreac_fuzz_fopen)%Z.      (* 0x816bc: the return address of the bad-magic fclose *)
Lemma OPB_pcs_pin :
  pcap_text + OPB_EPI_A = (symaddr (Symbols.Asan.s_pcap_source_open + 0x270)%Z) /\ pcap_text + OPB_EPI_B = (symaddr (Symbols.Asan.s_pcap_source_open + 0x280)%Z) /\ pcap_text + OPB_SHORT = (symaddr (Symbols.Asan.s_pcap_source_open + 0x20c)%Z) /\
  pcap_text + OPB_HDR0 = (symaddr (Symbols.Asan.s_pcap_source_open + 0x1a4)%Z) /\ pcap_text + OPB_SWAP = (symaddr (Symbols.Asan.s_pcap_source_open + 0x22c)%Z) /\ pcap_text + OPB_NATIVE = (symaddr (Symbols.Asan.s_pcap_source_open + 0x1e4)%Z) /\
  pcap_text + OPB_BADMAGIC = (symaddr (Symbols.Asan.s_pcap_source_open + 0x250)%Z) /\ pcap_text + OPB_RET1 = (symaddr (Symbols.Asan.s_pcap_source_open + 0x21c)%Z) /\ pcap_text + OPB_RET2 = (symaddr (Symbols.Asan.s_pcap_source_open + 0x260)%Z).
Proof. repeat split; reflexivity. Qed.

(* ---- the symbolic state ------------------------------------------------------------------------------------
   Atoms 0..31 are the registers of the cut state; the extra atoms are
     32    ra                  33..34  s0, s1              35..42  s2 .. s9   (the words the prologue saved)
     43    ps->f at the cut    44      the frame's flag address
     45..48 the four header bytes C0..C3 (the read walk only).
   s2 (18) is aliased to s6 (22), both holding F, so a load through either resolves in F's region; s8 (24) is
   given the shadow form of ps, which is what the shadow engine matches (YCbn.match_x). *)
Definition OPB_SB : Z := 0x7fff8000.                      (* SHADOW_OFF, the value s7 holds *)
Definition OPB_Bx : sv := SOff 23 0.
Definition OPB_span : Z * Z := (OPB_SB, OPB_SB + 2 ^ 44 - 1).
Definition OPB_SH : list shent := [mkSHE 19 0 24].        (* ps's 24 bytes are addressable *)
Definition opb_sh8 : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 19 0) (SLit 3)) (SOff 23 0).
Definition opb_sr_epi : list sv := sr_set sr_atoms 18 (SOff 22 0).
Definition opb_sr : list sv := sr_set opb_sr_epi 24 opb_sh8.
Definition opb_sr_read : list sv := sr_set (sr_set opb_sr 20 (SOff 22 32)) 25 (SLit 24).
Definition opb_sr_read2 : list sv := sr_set opb_sr_read 10 (SLit 24).

Definition opb_stack_chunks : list YP09.chunk :=
  map (fun j => YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (32 + j) 0))) (seq 0 11).
Definition opb_stack : YP09.region := YP09.mkRegion (Some 8%nat) (-96) 0 0 0 opb_stack_chunks.
Definition opb_ps_lo : YP09.region := YP09.mkRegion (Some 19%nat) 0 24 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 43 0))].
Definition opb_ps_hi : YP09.region := YP09.mkRegion (Some 19%nat) 0 24 8 12 [YP09.mkChunk 0 (CVal 8 (SOff 43 0))].
Definition opb_hdr : YP09.region := YP09.mkRegion (Some 22%nat) 32 36 0 0
  [YP09.mkChunk 32 (CVal 1 (SOff 45 0)); YP09.mkChunk 33 (CVal 1 (SOff 46 0));
   YP09.mkChunk 34 (CVal 1 (SOff 47 0)); YP09.mkChunk 35 (CVal 1 (SOff 48 0))].
Definition opb_F : YP09.region := YP09.mkRegion (Some 22%nat) 0 128 0 128 [YP09.mkChunk 120 (CVal 8 (SOff 44 0))].
Definition opb_FS : YP09.region := YP09.mkRegion (Some 21%nat) 0 16 0 16 [].
Definition opb_FL : YP09.region := YP09.mkRegion (Some 44%nat) 0 1 0 1 [].
Definition opb_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46 - 512) (2 ^ 47) 5); (8%nat, mkAF (2 ^ 46) (2 ^ 47) 4);
           (19%nat, mkAF 4096 140737479966720 3); (21%nat, mkAF OPB_SB (OPB_SB + 2 ^ 44) 3);
           (22%nat, mkAF 4096 140737479966720 6); (23%nat, mkAF OPB_SB OPB_SB 0)] [] [].
Definition opb_ss (pc : Z) (sr : list sv) (rs : smem) (G : facts) : sstate := mkSS pc sr rs None G.

(* ---- generic facts ------------------------------------------------------------------------------------------ *)

Lemma opb_ms_eta `{fx : YK11.FPState} : forall ms : machine_state,
  ms_fregs ms = fp_regs -> ms_svc_pending ms = None -> ms_resv ms = None -> ms_fcsr ms = fp_csr ->
  ms = mkst (ms_regs ms) (ms_pc_val ms) (ms_mem ms) (ms_rom ms).
Proof. intros [] H1 H2 H3 H4; cbn in *; subst; reflexivity. Qed.

Lemma opb_div8_in : forall p x, p mod 8 = 0 -> p <= x < p + 8 -> x / 8 = p / 8.
Proof.
intros p x H Hx. pose proof (Z_div_mod_eq_full p 8) as E. rewrite H, Z.add_0_r in E.
symmetry. apply (Z.div_unique x 8 (p / 8) (x - p)); [left; lia | lia].
Qed.

Lemma opb_div8_mul64 : forall a, a mod 64 = 0 -> a / 8 = 8 * (a / 64) /\ a = 64 * (a / 64).
Proof.
intros a H. pose proof (Z_div_mod_eq_full a 64) as E. rewrite H, Z.add_0_r in E. split; [|exact E].
symmetry. apply (Z.div_unique a 8 (8 * (a / 64)) 0); [left; lia | lia].
Qed.

(* The realigned stack pointer (0x81494 `andi sp,sp,-0x20` after `addi sp,sp,-0x60`). *)
Lemma opb_sp1_facts : forall x, 0 <= x -> x mod 16 = 0 ->
  x - 112 <= 32 * ((x - 96) / 32) <= x - 96 /\ (32 * ((x - 96) / 32)) mod 32 = 0 /\
  (32 * ((x - 96) / 32)) mod 16 = 0.
Proof.
intros x Hx H16. pose proof (Z.div_mod (x - 96) 32 ltac:(lia)) as D.
pose proof (Z.mod_pos_bound (x - 96) 32 ltac:(lia)) as M. pose proof (Z.div_mod x 16 ltac:(lia)) as D16.
assert ((x - 96) mod 32 = 0 \/ (x - 96) mod 32 = 16) by lia.
split; [lia|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|].
replace (32 * ((x - 96) / 32)) with ((2 * ((x - 96) / 32)) * 16) by lia. apply Z_mod_mult.
Qed.

Lemma opb_vm_frame : forall segs (m m' : word -> option byte) a n v,
  (forall x, a <= x < a + Z.of_nat n -> mbyte segs m' x = mbyte segs m x) ->
  val_mem segs m a n v -> val_mem segs m' a n v.
Proof. intros segs m m' a n v Hfr H k Hk. rewrite Hfr by lia. exact (H k Hk). Qed.

Lemma opb_rdword_ext : forall (rd rd' : reader) a,
  (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) -> rdword rd' a = rdword rd a.
Proof.
intros rd rd' a H. unfold rdword.
assert (H0 : rd' a = rd a) by (specialize (H 0 ltac:(lia)); rewrite Z.add_0_r in H; exact H).
rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.

Lemma opb_wvb_fds_fs : forall l X m, m_fds (with_vm_backing l X m) = m_fds m /\ m_fs (with_vm_backing l X m) = m_fs m.
Proof. intros l X []. split; reflexivity. Qed.

Lemma opb_lay_F : forall n ly ly', layout_le n ly ly' -> ly_F ly' = ly_F ly.
Proof. intros n ly ly' (_ & _ & _ & _ & _ & EF & _). exact EF. Qed.

Lemma opb_nth_firstn : forall (l : list Z) n j d, (j < n)%nat -> nth j (firstn n l) d = nth j l d.
Proof.
induction l as [|x l IH]; intros n j d Hj.
- rewrite firstn_nil. destruct j; reflexivity.
- destruct n as [|n]; [lia|]. cbn [firstn]. destruct j as [|j]; [reflexivity|]. cbn [nth]. apply IH. lia.
Qed.

Lemma opb_land_shl : forall a b k, 0 <= k -> 0 <= a -> 0 <= b < 2 ^ k -> Z.land (a * 2 ^ k) b = 0.
Proof.
intros a b k Hk Ha Hb. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
destruct (Z.lt_ge_cases i k) as [Hlt|Hge].
- rewrite <- Z.shiftl_mul_pow2 by lia. rewrite Z.shiftl_spec_low by lia. reflexivity.
- rewrite (Z_testbit_high k b i) by lia. apply andb_false_r.
Qed.

Lemma opb_lor_disj : forall a b k, 0 <= k -> 0 <= a -> 0 <= b < 2 ^ k -> Z.lor (a * 2 ^ k) b = a * 2 ^ k + b.
Proof. intros a b k Hk Ha Hb. symmetry. apply Z.add_nocarry_lor. apply opb_land_shl; lia. Qed.

(* The little-endian magic the code assembles at 0x81600..0x81628: four `lbu`, two shifts, three `or`, with
   the top byte shifted by a 32-bit `slliw`, so the result is the SIGN-EXTENDED 32-bit word. *)
Lemma opb_magic_U : forall (E : env) n0 n1 n2 n3 c0 c1 c2 c3,
  ew E n0 = w64 c0 -> ew E n1 = w64 c1 -> ew E n2 = w64 c2 -> ew E n3 = w64 c3 ->
  0 <= c0 < 256 -> 0 <= c1 < 256 -> 0 <= c2 < 256 -> 0 <= c3 < 256 ->
  U E (SAlu ALU_OR
         (SAlu ALU_OR (SAlu ALU_SLL (SExt false 8 (SOff n1 0)) (SLit 8)) (SExt false 8 (SOff n0 0)))
         (SAlu ALU_OR (SAlu ALU_SLL (SExt false 8 (SOff n2 0)) (SLit 16))
                      (SAluw ALU_SLL (SExt false 8 (SOff n3 0)) (SLit 24))))
  = c0 + 256 * c1 + 65536 * c2 + 16777216 * c3 + (if c3 <? 128 then 0 else 2 ^ 64 - 2 ^ 32).
Proof.
intros E n0 n1 n2 n3 c0 c1 c2 c3 H0 H1 H2 H3 R0 R1 R2 R3.
assert (Ub : forall n c, ew E n = w64 c -> 0 <= c < 256 -> U E (SExt false 8 (SOff n 0)) = c).
{ intros n c Hn Rc. rewrite U_SExt. rewrite (U_atom E n c Hn ltac:(clear - Rc; lia)).
  change (2 ^ Z.of_N 8) with 256. rewrite (Z.mod_small c 256) by (clear - Rc; lia).
  apply zcanon_id. unfold M64. clear - Rc. lia. }
assert (Esl : forall n c k, ew E n = w64 c -> 0 <= c < 256 -> 0 <= k <= 32 ->
  U E (SAlu ALU_SLL (SExt false 8 (SOff n 0)) (SLit k)) = c * 2 ^ k).
{ intros n c k Hn Rc Rk. rewrite U_SAlu. cbn [zalu_raw]. rewrite (Ub n c Hn Rc), U_SLit.
  rewrite (zcanon_id k) by (unfold M64; clear - Rk; lia).
  replace (Z.land k 63) with k
    by (symmetry; change 63 with (Z.ones 6); rewrite Z.land_ones by lia; apply Z.mod_small;
        clear - Rk; split; [lia | cbn; lia]).
  rewrite Z.shiftl_mul_pow2 by (clear - Rk; lia). apply zcanon_id. unfold M64.
  assert (2 ^ k <= 2 ^ 32) by (apply Z.pow_le_mono_r; clear - Rk; lia).
  assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; clear - Rk; lia). clear - Rc H. nia. }
assert (Esw : U E (SAluw ALU_SLL (SExt false 8 (SOff n3 0)) (SLit 24))
              = c3 * 2 ^ 24 + (if c3 <? 128 then 0 else 2 ^ 64 - 2 ^ 32)).
{ rewrite U_of_S, S_SAluw. cbn [zalu_raw]. rewrite (Ub n3 c3 H3 R3), U_SLit.
  rewrite (zcanon_id 24) by (unfold M64; clear; lia).
  rewrite (Z.mod_small c3 (2 ^ 32)) by (clear - R3; lia).
  rewrite (Z.mod_small 24 (2 ^ 32)) by (clear; lia).
  replace (Z.land 24 31) with 24 by reflexivity.
  rewrite Z.shiftl_mul_pow2 by lia.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with 4294967296. change (2 ^ Z.of_N 64) with 18446744073709551616.
  change (2 ^ 24) with 16777216. change (4294967296 / 2) with 2147483648.
  change (2 ^ 64 - 2 ^ 32) with 18446744069414584320.
  destruct (Z.ltb_spec c3 128) as [Hlt|Hge].
  - rewrite (Z.mod_small (c3 * 16777216 + 2147483648) 4294967296) by (clear - R3 Hlt; lia).
    replace (c3 * 16777216 + 2147483648 - 2147483648) with (c3 * 16777216) by (clear; lia).
    rewrite (Z.mod_small (c3 * 16777216) 18446744073709551616) by (clear - R3; lia). clear; lia.
  - assert (Hq : (c3 * 16777216 + 2147483648) mod 4294967296 = c3 * 16777216 - 2147483648)
      by (symmetry; apply Z.mod_unique_pos with (q := 1); clear - R3 Hge; lia).
    rewrite Hq.
    replace (c3 * 16777216 - 2147483648 - 2147483648) with (c3 * 16777216 - 4294967296) by (clear; lia).
    assert (Hw : (c3 * 16777216 - 4294967296) mod 18446744073709551616
                 = c3 * 16777216 - 4294967296 + 18446744073709551616)
      by (symmetry; apply Z.mod_unique_pos with (q := -1); clear - R3 Hge; lia).
    rewrite Hw. clear; lia. }
set (s := if c3 <? 128 then 0 else 2 ^ 64 - 2 ^ 32).
assert (Hs : s = 0 \/ s = 2 ^ 64 - 2 ^ 32) by (unfold s; destruct (Z.ltb_spec c3 128); [left|right]; reflexivity).
rewrite !(U_SAlu E ALU_OR). cbn [zalu_raw].
rewrite (Esl n1 c1 8 H1 R1 ltac:(clear; lia)), (Ub n0 c0 H0 R0),
        (Esl n2 c2 16 H2 R2 ltac:(clear; lia)), Esw.
fold s.
assert (E1 : zcanon (Z.lor (c1 * 2 ^ 8) c0) = c0 + 256 * c1).
{ rewrite (opb_lor_disj c1 c0 8 ltac:(clear; lia) ltac:(clear - R1; lia) ltac:(clear - R0; cbn; lia)).
  rewrite zcanon_id by (unfold M64; clear - R0 R1; cbn; lia). cbn. clear; lia. }
assert (E2 : zcanon (Z.lor (c2 * 2 ^ 16) (c3 * 2 ^ 24 + s)) = 65536 * c2 + 16777216 * c3 + s).
{ replace (c3 * 2 ^ 24 + s) with ((c3 + (if c3 <? 128 then 0 else 2 ^ 40 - 2 ^ 8)) * 2 ^ 24)
    by (unfold s; destruct (Z.ltb_spec c3 128); clear; cbn; lia).
  rewrite Z.lor_comm.
  rewrite (opb_lor_disj (c3 + (if c3 <? 128 then 0 else 2 ^ 40 - 2 ^ 8)) (c2 * 2 ^ 16) 24
    ltac:(clear; lia) ltac:(destruct (Z.ltb_spec c3 128); clear - R3; cbn; lia)
    ltac:(clear - R2; cbn; lia)).
  rewrite zcanon_id; [unfold s; destruct (Z.ltb_spec c3 128); clear - R2 R3; cbn; lia|].
  unfold M64. destruct (Z.ltb_spec c3 128); clear - R2 R3; cbn; lia. }
rewrite E1, E2.
assert (E3 : Z.lor (c0 + 256 * c1) (65536 * c2 + 16777216 * c3 + s)
             = c0 + 256 * c1 + (65536 * c2 + 16777216 * c3 + s)).
{ replace (65536 * c2 + 16777216 * c3 + s)
    with ((c2 + 256 * c3 + (if c3 <? 128 then 0 else 2 ^ 48 - 2 ^ 16)) * 2 ^ 16)
    by (unfold s; destruct (Z.ltb_spec c3 128); clear; cbn; lia).
  rewrite Z.lor_comm.
  rewrite (opb_lor_disj (c2 + 256 * c3 + (if c3 <? 128 then 0 else 2 ^ 48 - 2 ^ 16)) (c0 + 256 * c1) 16
    ltac:(clear; lia) ltac:(destruct (Z.ltb_spec c3 128); clear - R2 R3; cbn; lia)
    ltac:(clear - R0 R1; cbn; lia)).
  clear; lia. }
rewrite E3. rewrite zcanon_id; [clear; lia|].
unfold M64. destruct Hs as [Hs0 | Hs0]; rewrite Hs0; clear - R0 R1 R2 R3; cbn; lia.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg pcap_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ pcap_listing PI).
#[local] Abbreviation VAL := (@pa_val _ pcap_listing PI).
#[local] Abbreviation SIGMA := (@pa_sigma _ pcap_listing PI).
#[local] Abbreviation BASE := (@pa_val _ pcap_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Section e.
Variable B : asyms.
Variable K : asource_syms.
Variable MT : ameter_ops.
Variable FM_RA : Z.
Variable CTX : list (list Z).
Variable roimg : (word -> option byte) -> Prop.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis MLAW : ameter_laws MT.
Hypothesis MLAWF : ameter_fs_laws MT.
Hypothesis FM : asrc_file_meter SK SEGS B MT.
Hypothesis ASIL : asource_img_laws SK SEGS B K.
Variable ra_fc1 ra_fc2 : Z.
Hypothesis AFCLOSE : afclose_source_spec SK SEGS B K (SIGMA PS___interceptor_trampoline_fclose) ra_fc1 ra_fc2
  pa_relro_lo pa_relro_hi.
Hypothesis HUfc1 : In [pc_free_ra0 (as_code B); ra_fc1] (as_universe B).
Hypothesis HUfc2 : In [pc_free_ra0 (as_code B); ra_fc2] (as_universe B).
Let RUN := paj_run (SK := SK) B LAWS.
Let RUNTO := paj_run_to (SK := SK) B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_pcap) (PI := PI).
Let RUNF := aj_flag_store_pi (SK := SK) B LAWS ML ASF FFL.

(* The bytes the epilogue writes: the frame, its shadow and its flag byte. *)
Definition opb_wr (cx : ocx) (fpos a : Z) : Prop :=
  (oF cx fpos <= a < oF cx fpos + 128) \/ (oSH cx fpos <= a < oSH cx fpos + 16) \/ a = oFL cx fpos.

(* What the epilogue leaves. *)
Definition opb_epi_post (cx : ocx) (fpos : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) (kev a0out : Z) : world SEGS -> config -> Prop :=
  fun W2 c2 => exists S2 regs2 mem2 md2,
  W2 = W3 /\
  c2 = mkCfg (mkst regs2 (getr (o_regs cx) 1) mem2 (seg_rom SEGS)) md2 /\
  ajournal SEGS B (o_STK cx) (o_sp0 cx) (o_FP cx) (o_ly cx) (o_S cx) (o_W0 cx) (o_mem0 cx) (o_md0 cx)
    (o_own cx) ly3 S2 W2 mem2 md2 kev /\
  aregs_preserved (o_regs cx) regs2 /\ getr regs2 10 = w64 a0out /\
  frames S2 = frames (o_Sc cx) /\ ablocks B ly3 S2 = ablocks B ly3 S3 /\
  (exists fs, S2 = set_fs fs S3) /\
  m_fds md2 = m_fds md3 /\ m_fs md2 = m_fs md3 /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ opb_wr cx fpos a ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a) /\
  (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W2) mem2 a).

(* The extra atoms: the eleven words the prologue saved (ra, s0, s1, s2..s9), ps->f, and the frame's flag
   address.  The read walk appends the four header bytes. *)
Definition opb_extra (cx : ocx) (fpos f : Z) : list word :=
  [getr (o_regs cx) 1; getr (o_regs cx) 8; getr (o_regs cx) 9;
   getr (o_regs cx) 18; getr (o_regs cx) 19; getr (o_regs cx) 20; getr (o_regs cx) 21;
   getr (o_regs cx) 22; getr (o_regs cx) 23; getr (o_regs cx) 24; getr (o_regs cx) 25;
   w64 f; w64 (oFL cx fpos)].

Definition opb_ps_ro : YP09.region := YP09.mkRegion (Some 19%nat) 0 24 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 43 0))].
Definition opb_rs_ro : smem := [opb_stack; opb_ps_ro].
Definition opb_rs_hdr : smem := [opb_stack; opb_ps_ro; opb_hdr].
Definition opb_rs_lo : smem := [opb_stack; opb_ps_lo].
Definition opb_rs_hi : smem := [opb_stack; opb_ps_hi].
Definition opb_extra_hdr (cx : ocx) (fpos f : Z) : list word :=
  opb_extra cx fpos f ++
  [w64 (nth 0 (o_C cx) 0); w64 (nth 1 (o_C cx) 0); w64 (nth 2 (o_C cx) 0); w64 (nth 3 (o_C cx) 0)].

Definition opb_facts_epi : facts := mkFacts [(22%nat, mkAF 4096 140737479966720 6)] [] [].
Definition opb_rs_epi : smem := [opb_stack; opb_F; opb_FS; opb_FL].

(* The stream environment lies in the image (asil_env). *)
Lemma opb_src_env_img : forall a, asrc_env_addr K a -> 0x10000 <= a < pcap_img_end.
Proof. intros a Ha. exact (pa_img_range a (proj1 (asil_env _ _ _ _ ASIL a Ha))). Qed.

Lemma opb_asource_none_frame : forall (m m' : word -> option byte),
  (forall a, asrc_env_addr K a -> mbyte SEGS m' a = mbyte SEGS m a) ->
  asource_none SEGS K m -> asource_none SEGS K m'.
Proof.
intros m m' Hfr ((Hth & Hnl & Hlk & Hmode & Hms & (cv & Hcv & Hc)) & Hhead).
unfold asource_none, asrc_stdio_env, as_ofl_head in *.
split; [split; [|split; [|split; [|split; [|split]]]]|].
- eapply opb_vm_frame; [|exact Hth]. intros x Hx. apply Hfr. unfold asrc_env_addr. cbn in Hx. clear - Hx. lia.
- eapply opb_vm_frame; [|exact Hnl]. intros x Hx. apply Hfr. unfold asrc_env_addr. cbn in Hx. clear - Hx. lia.
- eapply opb_vm_frame; [|exact Hlk]. intros x Hx. apply Hfr. unfold asrc_env_addr. cbn in Hx. clear - Hx. lia.
- apply (garr8_frame SEGS m m' _ _ Hmode). intros x Hx. apply Hfr. unfold asrc_env_addr.
  cbn [length src_mode_Z app] in Hx. cbn in Hx. clear - Hx. lia.
- apply (garr8_frame SEGS m m' _ _ Hms). intros x Hx. apply Hfr. unfold asrc_env_addr.
  cbn [length src_modeset_Z app] in Hx. cbn in Hx. clear - Hx. lia.
- exists cv. split; [exact Hcv|]. eapply opb_vm_frame; [|exact Hc]. intros x Hx. apply Hfr.
  unfold asrc_env_addr. cbn in Hx. clear - Hx. lia.
- eapply opb_vm_frame; [|exact Hhead]. intros x Hx. apply Hfr. unfold asrc_env_addr, as_ofl_head.
  cbn in Hx. clear - Hx. lia.
Qed.

(* Two 64-aligned frames that are apart have shadow ranges that are apart. *)
Lemma opb_shadow_disj : forall f1 n1 f2 n2,
  f1 mod 64 = 0 -> n1 mod 64 = 0 -> f2 mod 64 = 0 -> n2 mod 64 = 0 ->
  0 <= f1 -> 0 <= f2 -> 0 <= n1 -> 0 <= n2 -> (f1 + n1 <= f2 \/ f2 + n2 <= f1) ->
  shadow_addr f1 + n1 / 8 <= shadow_addr f2 \/ shadow_addr f2 + n2 / 8 <= shadow_addr f1.
Proof.
intros f1 n1 f2 n2 A1 A2 A3 A4 P1 P2 P3 P4 Hd.
destruct (opb_div8_mul64 _ A1) as (D1 & Q1). destruct (opb_div8_mul64 _ A2) as (D2 & Q2).
destruct (opb_div8_mul64 _ A3) as (D3 & Q3). destruct (opb_div8_mul64 _ A4) as (D4 & Q4).
unfold shadow_addr. rewrite D1, D2, D3, D4. clear - Q1 Q2 Q3 Q4 Hd. lia.
Qed.

(* The epilogue's writes keep everything the post must keep. *)
Lemma opb_kept_step : forall (cx : ocx) (fpos : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
    (mem3 mem2 : word -> option byte) (md3 : Model) (kev slo shi : Z) (Ek : Z -> Prop),
  ajournal SEGS B (o_STK cx) (o_sp0 cx) (o_FP cx) (o_ly cx) (o_S cx) (o_W0 cx) (o_mem0 cx) (o_md0 cx)
    ((OP_CID, fpos) :: o_own cx) ly3 S3 W3 mem3 md3 kev ->
  frames S3 = (OP_CID, fpos) :: frames (o_Sc cx) ->
  ~ In (OP_CID, fpos) (frames (o_Sc cx)) ->
  (forall c p, frame_addr (o_lyc cx) c p = frame_addr ly3 c p) ->
  (forall b m, In (b, m) (ablocks B (o_lyc cx) (o_Sc cx)) -> In (b, m) (ablocks B ly3 S3)) ->
  topen_kept SK SEGS B (o_lyc cx) (o_Sc cx) (o_W cx) (o_memc cx) W3 mem3 slo shi Ek ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ opb_wr cx fpos a ->
     aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) mem3 a) ->
  (forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) mem2 a) ->
  topen_kept SK SEGS B (o_lyc cx) (o_Sc cx) (o_W cx) (o_memc cx) W3 mem2 slo shi Ek.
Proof.
intros cx fpos ly3 S3 W3 mem3 mem2 md3 kev slo shi Ek HJ3 Hfrs3 Hnin Elay Hincl HK HW HP.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ3 as (HAR3 & _).
assert (HinF : In (OP_CID, fpos) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 OP_CID fpos HAR3 HinF) as (HF4096 & HFceil & HFapp).
pose proof (frame_al64 SEGS B ly3 S3 W3 mem3 md3 OP_CID fpos HAR3 HinF) as (HFal & HFbal & HFb64).
pose proof (frm_off_imgP B ly3 S3 W3 mem3 md3 OP_CID fpos HAR3 HinF) as HFimg.
destruct (al_frames _ _ LAWS ly3 S3 W3 mem3 md3 OP_CID fpos HAR3 HinF) as (_ & _ & HFpres & HFSpres).
destruct (FFL ly3 S3 W3 mem3 md3 OP_CID fpos HAR3 HinF) as (_ & HFLown & (_ & HFLimg) & (HFLb1 & HFLz & HFLb2)).
assert (EF : oF cx fpos = frame_addr ly3 OP_CID fpos) by (unfold oF; apply Elay).
assert (EFL : oFL cx fpos = flag_addr ly3 OP_CID fpos).
{ unfold oFL, flag_addr, frame_addr in *. pose proof (Elay OP_CID fpos) as Ee. unfold frame_addr in Ee.
  clear - Ee. lia. }
rewrite <- EF in HF4096, HFceil, HFapp, HFal, HFimg, HFpres, HFSpres.
rewrite <- EFL in HFLown, HFLimg, HFLb1, HFLz, HFLb2.
change (fs_frame_bytes OP_CID) with 128 in HF4096, HFceil, HFapp, HFimg, HFpres, HFSpres, HFbal, HFb64.
assert (HSHeq : oSH cx fpos = shadow_addr (oF cx fpos)) by (unfold oSH, shadow_addr; reflexivity).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP, pcap_img_end in HFimg.
unfold zone2, off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in HFLz.
(* the flag byte is the runtime's, the frame's bytes and its shadow are not *)
assert (HFLnF : ~ (oF cx fpos <= oFL cx fpos < oF cx fpos + 128)).
{ intros Hc. apply (proj2 (HFpres _ Hc)). exact HFLown. }
assert (HFLnS : ~ (oSH cx fpos <= oFL cx fpos < oSH cx fpos + 16)).
{ intros Hc. rewrite HSHeq in Hc.
  apply (proj2 (HFSpres (oFL cx fpos - shadow_addr (oF cx fpos))
    ltac:(change (128 / 8) with 16; clear - Hc; lia))).
  replace (shadow_addr (oF cx fpos) + (oFL cx fpos - shadow_addr (oF cx fpos))) with (oFL cx fpos)
    by (clear; lia). exact HFLown. }
assert (HSHb : 2147450880 <= oSH cx fpos /\ oSH cx fpos + 16 <= 17594333495296).
{ assert (Hd0 : 0 <= oF cx fpos / 8) by (apply Z.div_pos; clear - HF4096; lia).
  assert (Hd1 : oF cx fpos / 8 < 2 ^ 44 - 16) by (apply Z.div_lt_upper_bound; clear - HFceil C1; lia).
  unfold oSH, SHADOW_OFF. clear - Hd0 Hd1. lia. }
destruct HK as (T1 & T2 & T3 & T4 & T5 & T6).
split; [|split; [|split; [|split; [|split]]]].
- intros a Ha Hn.
  assert (Hab : 0 <= a < 2 ^ 64) by (clear - Ha C1; lia).
  assert (Hnw : ~ opb_wr cx fpos a)
    by (unfold opb_wr; clear - Ha HFceil HSHb HFLb2 C1; lia).
  rewrite (HW a Hab Hnw). exact (T1 a Ha Hn).
- intros b0 m0 i Hb Hi HnE.
  assert (Hb3 : In (b0, m0) (ablocks B ly3 S3)) by (apply Hincl; exact Hb).
  destruct (al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 b0 m0 HAR3 Hb3) as (_ & Hb4096 & Hbceil & Hbapp & Hbnown & _).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp.
  pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 mem3 md3 b0 m0 OP_CID fpos HAR3 Hb3 HinF) as Dbf.
  unfold zdisjoint in Dbf. cbn [fst snd] in Dbf. rewrite <- EF in Dbf.
  change (fs_frame_bytes OP_CID) with 128 in Dbf.
  assert (Hab : 0 <= b0 + i < 2 ^ 64) by (clear - Hb4096 Hbceil Hi C1; lia).
  assert (Hnw : ~ opb_wr cx fpos (b0 + i)).
  { unfold opb_wr. intros [Hq | [Hq | Hq]].
    - clear - Dbf Hq Hi. lia.
    - clear - Hq Hbapp HSHb Hi. lia.
    - apply (proj2 (Hbnown (b0 + i) ltac:(clear - Hi; lia))). rewrite Hq. exact HFLown. }
  rewrite (HW (b0 + i) Hab Hnw). exact (T2 b0 m0 i Hb Hi HnE).
- intros a Hi Ho He Hof.
  pose proof (pa_img_range a Hi) as Hr. pose proof (pa_segs_low a Hi) as Hr2.
  unfold pcap_img_end, YImgTop.IMG_TOP in Hr. unfold kLowMemEnd in Hr2.
  assert (Hab : 0 <= a < 2 ^ 64) by (clear - Hr; lia).
  assert (Hnw : ~ opb_wr cx fpos a).
  { unfold opb_wr. intros [Hq | [Hq | Hq]].
    - clear - Hq HFimg Hr. lia.
    - clear - Hq HSHb Hr. lia.
    - apply HFLimg. rewrite <- Hq. exact Hi. }
  rewrite (HW a Hab Hnw). exact (T3 a Hi Ho He Hof).
- intros cid' pos' a Hin' Hrng HnE.
  assert (Hin3 : In (cid', pos') (frames S3)) by (rewrite Hfrs3; right; exact Hin').
  destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 cid' pos' HAR3 Hin3) as (Hg4096 & Hgceil & Hgapp).
  pose proof (frame_al64 SEGS B ly3 S3 W3 mem3 md3 cid' pos' HAR3 Hin3) as (Hgal & Hgbal & Hgb64).
  destruct (al_frames _ _ LAWS ly3 S3 W3 mem3 md3 cid' pos' HAR3 Hin3) as (_ & _ & Hgpres & HgSpres).
  pose proof (fs_frame_bytes_nonneg cid') as Hgnn.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hgapp.
  assert (Hne : (OP_CID, fpos) <> (cid', pos')) by (intros Hq; injection Hq as <- <-; exact (Hnin Hin')).
  apply in_split in Hin' as (l1 & l2 & El).
  pose proof (sep_frames_pos SEGS B LAWS ly3 S3 W3 mem3 md3 (OP_CID, fpos) (cid', pos') [] l1 l2 HAR3
    ltac:(rewrite Hfrs3, El; reflexivity)) as Dfg.
  unfold zdisjoint, frame_rng in Dfg. cbn [fst snd] in Dfg. rewrite <- EF in Dfg.
  change (fs_frame_bytes OP_CID) with 128 in Dfg.
  pose proof (opb_shadow_disj (oF cx fpos) 128 (frame_addr ly3 cid' pos') (fs_frame_bytes cid')
    HFal ltac:(reflexivity) Hgal Hgbal ltac:(clear - HF4096; lia) ltac:(clear - Hg4096; lia)
    ltac:(clear; lia) Hgnn ltac:(clear - Dfg; lia)) as Dsh.
  rewrite <- HSHeq in Dsh. change (128 / 8) with 16 in Dsh.
  unfold in_zr, frame_rng in Hrng. cbn [fst snd] in Hrng. rewrite (Elay cid' pos') in Hrng.
  assert (Hs1 : kLowMemEnd <= shadow_addr (frame_addr ly3 cid' pos') < kHighShadowEnd)
    by (apply shadow_addr_bounds; clear - Hg4096 Hgceil Hgnn C1 C4; lia).
  assert (Hs2 : shadow_addr (frame_addr ly3 cid' pos') + fs_frame_bytes cid' / 8
                <= shadow_addr (frame_addr ly3 cid' pos' + fs_frame_bytes cid'))
    by (apply shadow_range_end; exact Hgnn).
  assert (Hs3 : kLowMemEnd <= shadow_addr (frame_addr ly3 cid' pos' + fs_frame_bytes cid') < kHighShadowEnd)
    by (apply shadow_addr_bounds; clear - Hg4096 Hgceil Hgnn C1 C4; lia).
  assert (Habnd : 0 <= a < 2 ^ 64).
  { destruct Hrng as [Hq|Hq].
    - clear - Hq Hg4096 Hgceil C1. lia.
    - clear - Hq Hs1 Hs2 Hs3 C2 C5. lia. }
  assert (Hnw : ~ opb_wr cx fpos a).
  { unfold opb_wr. intros [Hq | [Hq | Hq]].
    - destruct Hrng as [Hr'|Hr'].
      + clear - Hq Hr' Dfg. lia.
      + clear - Hq Hr' Hs1 Hs2 Hs3 C2 C5 HFapp HFceil C1. lia.
    - destruct Hrng as [Hr'|Hr'].
      + clear - Hq Hr' Hgapp HSHb. lia.
      + clear - Hq Hr' Dsh Hgnn. lia.
    - destruct Hrng as [Hr'|Hr'].
      + apply (proj2 (Hgpres a ltac:(clear - Hr'; lia))). rewrite Hq. exact HFLown.
      + apply (proj2 (HgSpres (a - shadow_addr (frame_addr ly3 cid' pos')) ltac:(clear - Hr'; lia))).
        replace (shadow_addr (frame_addr ly3 cid' pos') + (a - shadow_addr (frame_addr ly3 cid' pos')))
          with a by (clear; lia). rewrite Hq. exact HFLown. }
  rewrite (HW a Habnd Hnw).
  exact (T4 cid' pos' a ltac:(rewrite El; apply in_or_app; right; left; reflexivity)
     ltac:(unfold in_zr, frame_rng; cbn [fst snd]; rewrite (Elay cid' pos'); exact Hrng) HnE).
- intros a Ha Hn Hpr. apply HP. exact (T5 a Ha Hn Hpr).
- intros a Ha. apply HP. exact (T6 a Ha).
Qed.

(* A write inside ps[0..12) keeps every clause of the post's kept set. *)
Lemma opb_kept_ps : forall (cx : ocx) (ly4 : alayout) (S4 : astate) (W4 : world SEGS)
    (mem4 mem5 : word -> option byte) (md4 : Model) (slo shi : Z),
  AR SEGS B ly4 S4 W4 mem4 md4 ->
  In (o_cid cx, o_pos cx) (frames S4) ->
  (forall c p, In (c, p) (frames (o_Sc cx)) -> In (c, p) (frames S4)) ->
  (forall c p, frame_addr (o_lyc cx) c p = frame_addr ly4 c p) ->
  (forall b m, In (b, m) (ablocks B (o_lyc cx) (o_Sc cx)) -> In (b, m) (ablocks B ly4 S4)) ->
  frame_addr (o_lyc cx) (o_cid cx) (o_pos cx) <= o_ps cx ->
  o_ps cx + 24 <= frame_addr (o_lyc cx) (o_cid cx) (o_pos cx) + fs_frame_bytes (o_cid cx) ->
  topen_kept SK SEGS B (o_lyc cx) (o_Sc cx) (o_W cx) (o_memc cx) W4 mem4 slo shi
    (fun a => o_ps cx <= a < o_ps cx + 22) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (o_ps cx <= a < o_ps cx + 12) ->
     aview SEGS (w_H W4) mem5 a = aview SEGS (w_H W4) mem4 a) ->
  (forall a, apresent (w_H W4) mem4 a -> apresent (w_H W4) mem5 a) ->
  topen_kept SK SEGS B (o_lyc cx) (o_Sc cx) (o_W cx) (o_memc cx) W4 mem5 slo shi
    (fun a => o_ps cx <= a < o_ps cx + 22).
Proof.
intros cx ly4 S4 W4 mem4 mem5 md4 slo shi HAR4 Hin4 Hinfr Elay Hincl Hfa1 Hfa2 HK HW HP.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (frames_bounds SEGS B LAWS ly4 S4 W4 mem4 md4 (o_cid cx) (o_pos cx) HAR4 Hin4)
  as (Hg4096 & Hgceil & Hgapp).
pose proof (frm_off_imgP B ly4 S4 W4 mem4 md4 (o_cid cx) (o_pos cx) HAR4 Hin4) as Hgimg.
rewrite (Elay (o_cid cx) (o_pos cx)) in Hfa1, Hfa2.
unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in Hgimg.
pose proof (fs_frame_bytes_nonneg (o_cid cx)) as Hgnn.
destruct HK as (T1 & T2 & T3 & T4 & T5 & T6).
split; [|split; [|split; [|split; [|split]]]].
- intros a Ha Hn.
  rewrite (HW a ltac:(clear - Ha C1; lia) ltac:(clear - Ha Hfa1 Hfa2 Hgceil Hgnn C1; lia)).
  exact (T1 a Ha Hn).
- intros b0 m0 i Hb Hi HnE.
  assert (Hb4 : In (b0, m0) (ablocks B ly4 S4)) by (apply Hincl; exact Hb).
  destruct (al_blocks _ _ LAWS ly4 S4 W4 mem4 md4 b0 m0 HAR4 Hb4) as (_ & Hb4096 & Hbceil & Hbapp & _ & _).
  pose proof (sep_block_frame SEGS B LAWS ly4 S4 W4 mem4 md4 b0 m0 (o_cid cx) (o_pos cx) HAR4 Hb4 Hin4) as Dbf.
  unfold zdisjoint in Dbf. cbn [fst snd] in Dbf.
  rewrite (HW (b0 + i) ltac:(clear - Hb4096 Hbceil Hi C1; lia)
    ltac:(clear - Dbf Hi Hfa1 Hfa2; lia)).
  exact (T2 b0 m0 i Hb Hi HnE).
- intros a Hi Ho He Hof.
  pose proof (pa_img_range a Hi) as Hr. unfold pcap_img_end, YImgTop.IMG_TOP in Hr.
  rewrite (HW a ltac:(clear - Hr; lia) ltac:(clear - Hr Hgimg Hfa1 Hfa2 Hgnn; lia)).
  exact (T3 a Hi Ho He Hof).
- intros cid' pos' a Hin' Hrng HnE.
  assert (Hab : 0 <= a < 2 ^ 64).
  { assert (Hin4' : In (cid', pos') (frames S4)) by (exact (Hinfr cid' pos' Hin')).
    destruct (frames_bounds SEGS B LAWS ly4 S4 W4 mem4 md4 cid' pos' HAR4 Hin4') as (Hh4096 & Hhceil & _).
    pose proof (fs_frame_bytes_nonneg cid') as Hhnn.
    assert (Hs1 : kLowMemEnd <= shadow_addr (frame_addr ly4 cid' pos') < kHighShadowEnd)
      by (apply shadow_addr_bounds; clear - Hh4096 Hhceil Hhnn C1 C4; lia).
    assert (Hs2 : shadow_addr (frame_addr ly4 cid' pos') + fs_frame_bytes cid' / 8
                  <= shadow_addr (frame_addr ly4 cid' pos' + fs_frame_bytes cid'))
      by (apply shadow_range_end; exact Hhnn).
    assert (Hs3 : kLowMemEnd <= shadow_addr (frame_addr ly4 cid' pos' + fs_frame_bytes cid') < kHighShadowEnd)
      by (apply shadow_addr_bounds; clear - Hh4096 Hhceil Hhnn C1 C4; lia).
    unfold in_zr, frame_rng in Hrng. cbn [fst snd] in Hrng. rewrite (Elay cid' pos') in Hrng.
    destruct Hrng as [Hq|Hq]; [clear - Hq Hh4096 Hhceil C1; lia | clear - Hq Hs1 Hs2 Hs3 C2 C5; lia]. }
  rewrite (HW a Hab ltac:(clear - HnE; lia)). exact (T4 cid' pos' a Hin' Hrng HnE).
- intros a Ha Hn Hpr. apply HP. exact (T5 a Ha Hn Hpr).
- intros a Ha. apply HP. exact (T6 a Ha).
Qed.

(* ps's bytes and the image are outside the epilogue's write set. *)
Lemma opb_nwr : forall (cx : ocx) (fpos : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
    (mem3 : word -> option byte) (md3 : Model) (kev : Z),
  ajournal SEGS B (o_STK cx) (o_sp0 cx) (o_FP cx) (o_ly cx) (o_S cx) (o_W0 cx) (o_mem0 cx) (o_md0 cx)
    ((OP_CID, fpos) :: o_own cx) ly3 S3 W3 mem3 md3 kev ->
  frames S3 = (OP_CID, fpos) :: frames (o_Sc cx) ->
  ~ In (OP_CID, fpos) (frames (o_Sc cx)) ->
  (forall c p, frame_addr (o_lyc cx) c p = frame_addr ly3 c p) ->
  In (o_cid cx, o_pos cx) (frames (o_Sc cx)) ->
  frame_addr (o_lyc cx) (o_cid cx) (o_pos cx) <= o_ps cx ->
  o_ps cx + 24 <= frame_addr (o_lyc cx) (o_cid cx) (o_pos cx) + fs_frame_bytes (o_cid cx) ->
  (forall a, o_ps cx <= a < o_ps cx + 24 -> ~ opb_wr cx fpos a) /\
  (forall a, 0x10000 <= a < pcap_img_end -> ~ opb_wr cx fpos a) /\
  (forall a, o_ps cx <= a < o_ps cx + 24 -> 0 <= a < 2 ^ 64) /\
  (forall a, 0x10000 <= a < pcap_img_end -> 0 <= a < 2 ^ 64).
Proof.
intros cx fpos ly3 S3 W3 mem3 md3 kev HJ3 Hfrs3 Hnin Elay Hin Hfa1 Hfa2.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ3 as (HAR3 & _).
assert (HinF : In (OP_CID, fpos) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
assert (Hin3 : In (o_cid cx, o_pos cx) (frames S3)) by (rewrite Hfrs3; right; exact Hin).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 OP_CID fpos HAR3 HinF) as (HF4096 & HFceil & HFapp).
pose proof (frm_off_imgP B ly3 S3 W3 mem3 md3 OP_CID fpos HAR3 HinF) as HFimg.
destruct (al_frames _ _ LAWS ly3 S3 W3 mem3 md3 OP_CID fpos HAR3 HinF) as (_ & _ & HFpres & HFSpres).
destruct (FFL ly3 S3 W3 mem3 md3 OP_CID fpos HAR3 HinF) as (_ & HFLown & (_ & HFLimg) & (HFLb1 & HFLz & HFLb2)).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 (o_cid cx) (o_pos cx) HAR3 Hin3)
  as (Hg4096 & Hgceil & Hgapp).
destruct (al_frames _ _ LAWS ly3 S3 W3 mem3 md3 (o_cid cx) (o_pos cx) HAR3 Hin3) as (_ & _ & Hgpres & _).
pose proof (fs_frame_bytes_nonneg (o_cid cx)) as Hgnn.
assert (EF : oF cx fpos = frame_addr ly3 OP_CID fpos) by (unfold oF; apply Elay).
assert (EFL : oFL cx fpos = flag_addr ly3 OP_CID fpos).
{ unfold oFL, flag_addr. pose proof (Elay OP_CID fpos) as Ee. unfold frame_addr in Ee. clear - Ee. lia. }
rewrite <- EF in HF4096, HFceil, HFapp, HFimg, HFpres, HFSpres.
rewrite <- EFL in HFLown, HFLimg, HFLb1, HFLz, HFLb2.
rewrite (Elay (o_cid cx) (o_pos cx)) in Hfa1, Hfa2.
change (fs_frame_bytes OP_CID) with 128 in HF4096, HFceil, HFapp, HFimg, HFpres, HFSpres.
assert (HSHeq : oSH cx fpos = shadow_addr (oF cx fpos)) by (unfold oSH, shadow_addr; reflexivity).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp, Hgapp.
unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in HFimg.
unfold zone2, off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in HFLz.
pose proof (frame_al64 SEGS B ly3 S3 W3 mem3 md3 OP_CID fpos HAR3 HinF) as (HFal & _ & _).
rewrite <- EF in HFal.
assert (HSHb : 2147450880 <= oSH cx fpos /\ oSH cx fpos + 16 <= 17594333495296).
{ assert (Hd0 : 0 <= oF cx fpos / 8) by (apply Z.div_pos; clear - HF4096; lia).
  assert (Hd1 : oF cx fpos / 8 < 2 ^ 44 - 16) by (apply Z.div_lt_upper_bound; clear - HFceil C1; lia).
  unfold oSH, SHADOW_OFF. clear - Hd0 Hd1. lia. }
apply in_split in Hin as (l1 & l2 & El).
pose proof (sep_frames_pos SEGS B LAWS ly3 S3 W3 mem3 md3 (OP_CID, fpos) (o_cid cx, o_pos cx) [] l1 l2 HAR3
  ltac:(rewrite Hfrs3, El; reflexivity)) as Dfg.
unfold zdisjoint, frame_rng in Dfg. cbn [fst snd] in Dfg. rewrite <- EF in Dfg.
change (fs_frame_bytes OP_CID) with 128 in Dfg.
split; [|split; [|split]].
- intros a Ha. unfold opb_wr. intros [Hq | [Hq | Hq]].
  + clear - Hq Ha Hfa1 Hfa2 Dfg. lia.
  + clear - Hq Ha Hfa1 Hfa2 Hgapp HSHb Hgnn. lia.
  + apply (proj2 (Hgpres a ltac:(clear - Ha Hfa1 Hfa2; lia))). rewrite Hq. exact HFLown.
- intros a Ha. unfold pcap_img_end, YImgTop.IMG_TOP in Ha. unfold opb_wr. intros [Hq | [Hq | Hq]].
  + clear - Hq Ha HFimg. lia.
  + clear - Hq Ha HSHb. lia.
  + clear - Hq Ha HFLz. lia.
- intros a Ha. clear - Ha Hfa1 Hfa2 Hgceil C1 Hgnn Hg4096. lia.
- intros a Ha. unfold pcap_img_end, YImgTop.IMG_TOP in Ha. clear - Ha. lia.
Qed.

Lemma opb_epi : forall (cx : ocx) (fpos : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
    (ms3 : machine_state) (md3 : Model) (kev a0in a0out pc : Z),
  op_pre SK B K MT FM_RA CTX roimg cx ->
  (pc = OP_CUT_NULL /\ a0out = -1) \/ ((pc = OPB_EPI_A \/ pc = OPB_EPI_B) /\ a0out = a0in) ->
  ms_pc_val ms3 = w64 (BASE + pc) -> ms_resv ms3 = None -> ms_svc_pending ms3 = None ->
  ms_rom ms3 = seg_rom SEGS -> ms_fregs ms3 = fp_regs -> ms_fcsr ms3 = fp_csr ->
  ajournal SEGS B (o_STK cx) (o_sp0 cx) (o_FP cx) (o_ly cx) (o_S cx) (o_W0 cx) (o_mem0 cx) (o_md0 cx)
    ((OP_CID, fpos) :: o_own cx) ly3 S3 W3 (ms_mem ms3) md3 kev ->
  frames S3 = (OP_CID, fpos) :: frames (o_Sc cx) ->
  getr (ms_regs ms3) 8 = w64 (spZ (o_regs cx)) ->
  getr (ms_regs ms3) 10 = w64 a0in ->
  getr (ms_regs ms3) 18 = w64 (oF cx fpos) -> getr (ms_regs ms3) 21 = w64 (oSH cx fpos) ->
  getr (ms_regs ms3) 22 = w64 (oF cx fpos) ->
  getr (ms_regs ms3) 3 = getr (o_regs cx) 3 -> getr (ms_regs ms3) 4 = getr (o_regs cx) 4 ->
  getr (ms_regs ms3) 26 = getr (o_regs cx) 26 -> getr (ms_regs ms3) 27 = getr (o_regs cx) 27 ->
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (spZ (o_regs cx) - 8) = Some (raZ (o_regs cx)) ->
  (forall j, 0 <= j < 10 -> rdword (aview SEGS (w_H W3) (ms_mem ms3)) (spZ (o_regs cx) - 16 - 8 * j) =
     Some (bv_unsigned (getr (o_regs cx) (Z_to_bv 5 (if j <? 2 then 8 + j else 16 + j))))) ->
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (oF cx fpos + OP_FLAGPTR) = Some (oFL cx fpos) ->
  SRr SEGS W3 (mkCfg ms3 md3) (opb_epi_post cx fpos ly3 S3 W3 ms3 md3 kev a0out).
Proof.
intros cx fpos ly3 S3 W3 ms3 md3 kev a0in a0out pc HPRE Hpc0 Hpc Hresv Hsvc Hrom Hfrg Hfcsr HJ3 Hfrs3
  R8 R10 R18 R21 R22 R3 R4 R26 R27 Hra8 Hsav Hflag.
unfold op_pre in HPRE. cbv zeta in HPRE.
destruct HPRE as (HJ & HROD & Hraw & Hra4 & Hgp & Htp & H10 & H11 & Hch & Hctx & Hal16 & Hwlo & Hwhi & Htop32
  & Hnfr & Hown & Hfa1 & Hfa2 & Hps0 & Hps8 & Hshp & HFP0 & HRO & HPra & HPhull & HVn & HVb & Hb64 & HNONE
  & Hnn & HnC & Hinput & HMETA & Hev & Hlive & MOK & HU0 & HUC).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof (pa_base_lo (PL := PL_pcap) (PI := PI)) as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : TPCAP_SOURCE_OPEN_STK = 18736) by reflexivity.
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof HJ3 as (HAR3 & Hly3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & _).
assert (Hin : In (o_cid cx, o_pos cx) (frames (o_Sc cx)))
  by (rewrite Hfrs; apply in_or_app; left; exact Hown).
assert (HinF : In (OP_CID, fpos) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
assert (EF : frame_addr ly3 OP_CID fpos = oF cx fpos).
{ unfold oF, frame_addr. rewrite (opb_lay_F _ _ _ Hly3), (opb_lay_F _ _ _ Hly). reflexivity. }
assert (EFL : flag_addr ly3 OP_CID fpos = oFL cx fpos).
{ unfold oFL, flag_addr. rewrite (opb_lay_F _ _ _ Hly3), (opb_lay_F _ _ _ Hly). reflexivity. }
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 OP_CID fpos HAR3 HinF) as (HF4096 & HFceil & HFapp).
rewrite EF in HF4096, HFceil, HFapp. change (fs_frame_bytes OP_CID) with 128 in HF4096, HFceil, HFapp.
pose proof (frame_al64 SEGS B ly3 S3 W3 (ms_mem ms3) md3 OP_CID fpos HAR3 HinF) as (HFal & _ & _).
rewrite EF in HFal.
destruct (al_frames _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 OP_CID fpos HAR3 HinF) as (_ & _ & HFpres & HFSpres).
rewrite EF in HFpres, HFSpres. change (fs_frame_bytes OP_CID) with 128 in HFpres, HFSpres.
destruct (FFL ly3 S3 W3 (ms_mem ms3) md3 OP_CID fpos HAR3 HinF) as (HFLpres & HFLown & (HFLapp & HFLimg) & (HFLb1 & HFLz & HFLb2)).
rewrite EFL in HFLpres, HFLown, HFLapp, HFLimg, HFLb1, HFLz, HFLb2.
assert (HSHeq : oSH cx fpos = shadow_addr (oF cx fpos)) by (unfold oSH, shadow_addr; reflexivity).
destruct (opb_div8_mul64 _ HFal) as (HF8 & HF64).
(* the flag is owned by the runtime, the frame's bytes and its shadow are not *)
assert (HFLnF : forall a, oF cx fpos <= a < oF cx fpos + 128 -> a <> oFL cx fpos).
{ intros a Ha Heq. apply (proj2 (HFpres a Ha)). rewrite Heq. exact HFLown. }
assert (HFLnS : forall a, oSH cx fpos <= a < oSH cx fpos + 16 -> a <> oFL cx fpos).
{ intros a Ha Heq. rewrite HSHeq in Ha.
  apply (proj2 (HFSpres (a - shadow_addr (oF cx fpos)) ltac:(change (128 / 8) with 16; clear - Ha; lia))).
  replace (shadow_addr (oF cx fpos) + (a - shadow_addr (oF cx fpos))) with a by (clear; lia).
  rewrite Heq. exact HFLown. }
assert (HSHb : OPB_SB <= oSH cx fpos /\ oSH cx fpos + 16 <= OPB_SB + 2 ^ 44).
{ assert (Hd0 : 0 <= oF cx fpos / 8) by (apply Z.div_pos; clear - HF4096; lia).
  assert (Hd1 : oF cx fpos / 8 < 2 ^ 44 - 16) by (apply Z.div_lt_upper_bound; clear - HFceil C1; lia).
  unfold oSH, OPB_SB, SHADOW_OFF. clear - Hd0 Hd1. lia. }
assert (HFlt : 0 <= oF cx fpos < 2 ^ 64) by (clear - HF4096 HFceil C1; lia).
assert (HFLlt : 0 <= oFL cx fpos < 2 ^ 64) by (clear - HFLb1 HFLb2 C1; lia).
assert (HSHlt : 0 <= oSH cx fpos < 2 ^ 64) by (unfold OPB_SB in HSHb; clear - HSHb; lia).
assert (Hspr : 0 <= spZ (o_regs cx) < 2 ^ 64) by (unfold spZ; clear; apply u64_range).
(* the environment *)
set (E := Eimg (Ereg (ms_regs ms3) (opb_extra cx fpos 0))).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms3) (opb_extra cx fpos 0)) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (EREG : forall n (r : Prelude.reg), Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r).
{ intros n r Hr. rewrite EL; [exact (ew_Ereg_nat _ _ n r Hr)|].
  pose proof (u5_range r) as Hu. unfold A_TEXT. clear - Hr Hu. lia. }
assert (EX : forall j, (j < 13)%nat -> ew E (32 + j) = nth j (opb_extra cx fpos 0) (w64 0))
  by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ j)).
assert (E22 : ew E 22 = w64 (oF cx fpos)) by (rewrite (EREG 22%nat 22%bv eq_refl); exact R22).
assert (E21 : ew E 21 = w64 (oSH cx fpos)) by (rewrite (EREG 21%nat 21%bv eq_refl); exact R21).
assert (E8 : ew E 8 = w64 (spZ (o_regs cx))) by (rewrite (EREG 8%nat 8%bv eq_refl); exact R8).
assert (E44 : ew E 44 = w64 (oFL cx fpos)) by (exact (EX 12%nat ltac:(lia))).
assert (U22 : bv_unsigned (ew E 22) = oF cx fpos) by (rewrite E22; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E 21) = oSH cx fpos) by (rewrite E21; apply unsigned_lit_small; lia).
assert (U8 : bv_unsigned (ew E 8) = spZ (o_regs cx)) by (rewrite E8; apply unsigned_lit_small; lia).
assert (U44 : bv_unsigned (ew E 44) = oFL cx fpos) by (rewrite E44; apply unsigned_lit_small; lia).
assert (HAE : env_agree 32 (Ereg (ms_regs ms3) (opb_extra cx fpos 0)) E)
  by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
(* the saved words, as the stack region's chunks *)
assert (HSAV : forall j, (j < 11)%nat ->
  val_mem SEGS (rdW W3 (ms_mem ms3)) (spZ (o_regs cx) + (-8 - 8 * Z.of_nat j)) 8
    (bv_unsigned (nth j (opb_extra cx fpos 0) (w64 0)))).
{ intros j Hj. apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)).
  destruct j as [|j'];
  [ replace (spZ (o_regs cx) + (-8 - 8 * Z.of_nat 0)) with (spZ (o_regs cx) - 8) by (clear; lia);
    cbn [nth opb_extra]; exact Hra8 |].
  replace (spZ (o_regs cx) + (-8 - 8 * Z.of_nat (S j'))) with (spZ (o_regs cx) - 16 - 8 * Z.of_nat j')
    by (clear; lia).
  rewrite (Hsav (Z.of_nat j') ltac:(clear - Hj; lia)). f_equal.
  do 10 (destruct j' as [|j']; [cbn [nth opb_extra Z.ltb Z.compare]; reflexivity|]).
  cbn [length] in Hj. clear - Hj. lia. }
(* ---- the symbolic state at the entry of the epilogue ---- *)
assert (HCH : forall j, (j < 11)%nat -> YP09.chunk_ok SEGS E (rdW W3 (ms_mem ms3)) (spZ (o_regs cx))
   (YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (32 + j) 0)))).
{ intros j Hj.
  apply (chunk_ok_val SEGS E _ (spZ (o_regs cx)) (-8 - 8 * Z.of_nat j) 8 (SOff (32 + j) 0)
    (bv_unsigned (nth j (opb_extra cx fpos 0) (w64 0))));
  [ cbn [sv_denot]; rewrite (EX j ltac:(clear - Hj; lia)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | pose proof (u64_range (nth j (opb_extra cx fpos 0) (w64 0))) as Hu;
    change (8 * Z.of_N 8) with 64; clear - Hu; lia
  | zside
  | exact (HSAV j Hj) ]. }
assert (Hsplo : alloc_ceiling + TPCAP_SOURCE_OPEN_STK <= spZ (o_regs cx))
  by (clear - Hceil Hslo Hwlo Hwhi; lia).
assert (HdFL1 : oFL cx fpos + 1 <= oF cx fpos \/ oF cx fpos + 128 <= oFL cx fpos).
{ destruct (Z_lt_le_dec (oFL cx fpos) (oF cx fpos)) as [Hl|Hl]; [left; clear - Hl; lia|].
  destruct (Z_le_gt_dec (oF cx fpos + 128) (oFL cx fpos)) as [Hg|Hg]; [right; clear - Hg; lia|].
  exfalso. exact (HFLnF (oFL cx fpos) ltac:(clear - Hl Hg; lia) eq_refl). }
assert (HdFL2 : oFL cx fpos + 1 <= oSH cx fpos \/ oSH cx fpos + 16 <= oFL cx fpos).
{ destruct (Z_lt_le_dec (oFL cx fpos) (oSH cx fpos)) as [Hl|Hl]; [left; clear - Hl; lia|].
  destruct (Z_le_gt_dec (oSH cx fpos + 16) (oFL cx fpos)) as [Hg|Hg]; [right; clear - Hg; lia|].
  exfalso. exact (HFLnS (oFL cx fpos) ltac:(clear - Hl Hg; lia) eq_refl). }
assert (HSs : forall o, 0 <= o < 16 -> apresent (w_H W3) (ms_mem ms3) (oSH cx fpos + o)).
{ intros o Ho. rewrite HSHeq. apply (proj1 (HFSpres o ltac:(change (128 / 8) with 16; clear - Ho; lia))). }
assert (HSgeo : in_app (oF cx fpos) 128) by exact HFapp.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HSgeo.
unfold zone2, off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in HFLz.
assert (HS : st_ok_pi SEGS VAL E (opb_ss pc opb_sr_epi opb_rs_epi opb_facts_epi) (restrict (w_H W3) ms3)).
{ assert (HS0 : st_ok_pi SEGS VAL E (opb_ss pc sr_atoms opb_rs_epi opb_facts_epi) (restrict (w_H W3) ms3)).
  { rewrite (opb_ms_eta ms3 Hfrg Hsvc Hresv Hfcsr), Hpc, Hrom, restrict_mkst_fx.
    unfold opb_ss, opb_rs_epi, opb_facts_epi. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]];
      unfold region_ok, opb_stack, opb_F, opb_FS, opb_FL;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      + rewrite U8. split; [clear - Hsplo C1 HTS; lia|]. split; [clear - Hspr; lia|].
        split; [intros o Ho; clear - Ho; lia|].
        unfold opb_stack_chunks. apply Forall_map, Forall_forall. intros j Hj.
        apply in_seq in Hj. apply HCH. clear - Hj. lia.
      + rewrite U22. split; [clear - HF4096; lia|]. split; [clear - HFceil C1; lia|].
        split; [intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (oF cx fpos + o) ltac:(clear - Ho; lia)))|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS E _ (oF cx fpos) 120 8 (SOff 44 0) (oFL cx fpos));
        [ cbn [sv_denot]; rewrite E44, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (8 * Z.of_N 8) with 64; clear - HFLlt; lia | zside
        | exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ Hflag) ].
      + rewrite U21. unfold OPB_SB in HSHb. split; [clear - HSHb; lia|].
        split; [clear - HSHb; lia|].
        split; [intros o Ho; apply (apresent_writable SEGS); apply (HSs o ltac:(clear - Ho; lia))|].
        apply Forall_nil.
      + rewrite U44. split; [clear - HFLb1; lia|]. split; [clear - HFLb2 C1; lia|].
        split; [intros o Ho; replace (oFL cx fpos + o) with (oFL cx fpos) by (clear - Ho; lia);
                apply (apresent_writable SEGS); exact HFLpres|].
        apply Forall_nil.
    - apply pairwise_disjoint_of_extents.
      unfold opb_rs_epi, opb_stack, opb_F, opb_FS, opb_FL, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U8, U22, U21, U44.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      unfold OPB_SB in HSHb.
      clear - Hsplo C1 HTS HF4096 HFceil HSHb HSgeo HdFL1 HdFL2 HFLb1 HFLb2 HSHeq.
      unfold shadow_addr, SHADOW_OFF in HSHeq. repeat split; lia.
    - split; [|split; [exact I | exact I]].
      cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      repeat split; rewrite ?U22; try exact I; try (change (2 ^ 6) with 64; exact HFal);
      try (clear - HF4096 HFceil C1 HFal; lia). }
  exact (ast_ok_pi_set_reg_fp E _ _ (18%bv : bv 5) (SOff 22 0) HS0 ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite U22, Z.add_0_r; exact (eq_sym R18))). }
clearbody E.
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 5%nat ltac:(lia)) as E37.
pose proof (EX 6%nat ltac:(lia)) as E38. pose proof (EX 7%nat ltac:(lia)) as E39.
pose proof (EX 8%nat ltac:(lia)) as E40. pose proof (EX 9%nat ltac:(lia)) as E41.
pose proof (EX 10%nat ltac:(lia)) as E42.
cbn [Nat.add nth opb_extra] in E32, E33, E34, E35, E36, E37, E38, E39, E40, E41, E42.
pose proof HJ3 as (_ & _ & _ & _ & _ & Hfrs3j & _).
unfold opb_epi_post.
destruct Hpc0 as [[-> ->] | [[-> | ->] ->]].
all: paj_run_flag_sh RUNF HS HJ3.
all: lazymatch goal with
| |- 0 <= _ => unfold OP_CID; clear; lia
| |- forall a, in_wrange _ _ a -> _ =>
    let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Ha := fresh "Ha" in
    intros a (r & Hr & Ha);
    cbn [opb_ss ss_mem opb_rs_epi In] in Hr;
    destruct Hr as [<- | [<- | [<- | [<- | []]]]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val opb_stack opb_F opb_FS opb_FL] in Ha;
    [ exfalso; clear - Ha; lia
    | left; right; right; right; exists OP_CID, fpos; split; [left; reflexivity|]; left;
      unfold in_zr, frame_rng; cbn [fst snd]; rewrite EF; change (fs_frame_bytes OP_CID) with 128;
      rewrite U22 in Ha; clear - Ha; lia
    | left; right; right; right; exists OP_CID, fpos; split; [left; reflexivity|]; right;
      unfold in_zr; cbn [fst snd]; rewrite EF, <- HSHeq; change (fs_frame_bytes OP_CID / 8) with 16;
      rewrite U21 in Ha; clear - Ha; lia
    | right; rewrite EFL; rewrite U44 in Ha; clear - Ha; lia ]
| |- forall msr, st_ok_pi _ _ _ _ msr -> _ =>
    let msr := fresh "msr" in let HSr := fresh "HSr" in
    intros msr HSr;
    lazymatch type of HSr with st_ok_pi _ _ _ ?ssx _ =>
      let r3 := eval vm_compute in (nth 3 (ss_mem ssx) opb_FL) in
      let HR3 := fresh "HR3" in
      pose proof (st_ok_pi_region_nth E ssx msr 3 r3 HSr ltac:(vm_compute; reflexivity)) as HR3;
      let Vfl := fresh "Vfl" in
      pose proof (field_of_region E (ms_mem msr) 44 (oFL cx fpos) _ 0 1 0 1 0 1%N (SLit 0) 0 HR3 U44
        ltac:(cbn; tauto) ltac:(reflexivity) ltac:(clear; lia) ltac:(clear; lia)) as Vfl;
      change (N.to_nat 1) with 1%nat in Vfl; specialize (Vfl 0%nat ltac:(clear; lia));
      replace (oFL cx fpos + 0 + Z.of_nat 0) with (oFL cx fpos) in Vfl by (clear; lia);
      rewrite EFL, Vfl; reflexivity
    end
| |- _ => idtac
end.
(* the three continuations: the registers restored, `ret`, the post *)
all: (prreg HS (1%bv : bv 5) Q1; prreg HS (2%bv : bv 5) Q2; prreg HS (3%bv : bv 5) Q3;
  prreg HS (4%bv : bv 5) Q4; prreg HS (8%bv : bv 5) Q8; prreg HS (9%bv : bv 5) Q9;
  prreg HS (10%bv : bv 5) Q10; prreg HS (18%bv : bv 5) Q18; prreg HS (19%bv : bv 5) Q19;
  prreg HS (20%bv : bv 5) Q20; prreg HS (21%bv : bv 5) Q21; prreg HS (22%bv : bv 5) Q22;
  prreg HS (23%bv : bv 5) Q23; prreg HS (24%bv : bv 5) Q24; prreg HS (25%bv : bv 5) Q25;
  prreg HS (26%bv : bv 5) Q26; prreg HS (27%bv : bv 5) Q27;
  pose proof HJ3 as (_ & _ & _ & _ & _ & Hfrs4 & _);
  eapply (RET W3 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
  let mat2 := fresh "mat" in intros mat2;
  exists (stack_free_state OP_CID fpos S3), (ms_regs ms), (ms_mem ms); eexists;
  split; [reflexivity|];
  split; [rewrite Q1, E32, Hraw; reflexivity|];
  split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ3|];
  split;
  [ apply aregs_preserved_eqs;
    [ rewrite Q2, E8; unfold w64, spZ; apply Z_to_bv_bv_unsigned
    | rewrite Q3, (EREG 3%nat 3%bv eq_refl); exact R3
    | rewrite Q4, (EREG 4%nat 4%bv eq_refl); exact R4
    | rewrite Q8, E33; reflexivity | rewrite Q9, E34; reflexivity
    | rewrite Q18, E35; reflexivity | rewrite Q19, E36; reflexivity
    | rewrite Q20, E37; reflexivity | rewrite Q21, E38; reflexivity
    | rewrite Q22, E39; reflexivity | rewrite Q23, E40; reflexivity
    | rewrite Q24, E41; reflexivity | rewrite Q25, E42; reflexivity
    | rewrite Q26, (EREG 26%nat 26%bv eq_refl); exact R26
    | rewrite Q27, (EREG 27%nat 27%bv eq_refl); exact R27 ] |];
  split; [rewrite Q10; first [ rewrite (EREG 10%nat 10%bv eq_refl); exact R10
                             | unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; vm_compute; reflexivity ] |];
  split; [rewrite Hfrs4, Hfrs; reflexivity|];
  split; [unfold ablocks; rewrite blocks_stack_free_state; reflexivity|];
  split; [unfold stack_free_state; eexists; reflexivity|];
  split; [repeat rewrite (proj1 (opb_wvb_fds_fs _ _ _)); reflexivity|];
  split; [repeat rewrite (proj2 (opb_wvb_fds_fs _ _ _)); reflexivity|];
  split;
  [ let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
    intros a Ha Hn;
    apply (kept_of_frame (segs := SEGS) E _ (w_H W3) (ms_mem ms3) (ms_mem ms) (opb_wr cx fpos) HFr);
    [ let bW := fresh "bW" in let wloW := fresh "wloW" in let whiW := fresh "whiW" in let aW := fresh "aW" in
      let HinW := fresh "HinW" in let HrrW := fresh "HrrW" in let HqW := fresh "HqW" in
      intros bW wloW whiW aW HinW HrrW; vm_compute in HinW;
      repeat (destruct HinW as [HqW | HinW];
              [injection HqW as <- <- <-; cbn [base_val] in HrrW; rewrite ?U8, ?U22, ?U21, ?U44 in HrrW;
               unfold opb_wr; clear - HrrW; lia|]);
      destruct HinW
    | exact Ha | exact Hn ]
  | let a := fresh "a" in let Ha := fresh "Ha" in
    intros a Ha; exact (apresent_grows (w_H W3) (ms_mem ms3) (ms_mem ms) a HG Ha) ]).
Qed.

(* A live block is outside the epilogue's write set and outside ps. *)
Lemma opb_blk_out : forall (cx : ocx) (fpos : Z) (ly4 : alayout) (S4 : astate) (W4 : world SEGS)
    (mem4 : word -> option byte) (md4 : Model) (kev bb mm : Z),
  ajournal SEGS B (o_STK cx) (o_sp0 cx) (o_FP cx) (o_ly cx) (o_S cx) (o_W0 cx) (o_mem0 cx) (o_md0 cx)
    ((OP_CID, fpos) :: o_own cx) ly4 S4 W4 mem4 md4 kev ->
  frames S4 = (OP_CID, fpos) :: frames (o_Sc cx) ->
  (forall c p, frame_addr (o_lyc cx) c p = frame_addr ly4 c p) ->
  In (o_cid cx, o_pos cx) (frames (o_Sc cx)) ->
  frame_addr (o_lyc cx) (o_cid cx) (o_pos cx) <= o_ps cx ->
  o_ps cx + 24 <= frame_addr (o_lyc cx) (o_cid cx) (o_pos cx) + fs_frame_bytes (o_cid cx) ->
  In (bb, mm) (ablocks B ly4 S4) ->
  forall a, bb <= a < bb + req_size mm ->
    ~ opb_wr cx fpos a /\ ~ (o_ps cx <= a < o_ps cx + 24) /\ 0 <= a < 2 ^ 64.
Proof.
intros cx fpos ly4 S4 W4 mem4 md4 kev bb mm HJ4 Hfrs4 Elay Hin Hfa1 Hfa2 Hblk a Ha.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ4 as (HAR4 & _).
assert (HinF : In (OP_CID, fpos) (frames S4)) by (rewrite Hfrs4; left; reflexivity).
assert (Hin4 : In (o_cid cx, o_pos cx) (frames S4)) by (rewrite Hfrs4; right; exact Hin).
destruct (al_blocks _ _ LAWS ly4 S4 W4 mem4 md4 bb mm HAR4 Hblk) as (_ & Hb4096 & Hbceil & Hbapp & Hbnown & _).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp.
destruct (frames_bounds SEGS B LAWS ly4 S4 W4 mem4 md4 OP_CID fpos HAR4 HinF) as (HF4096 & HFceil & HFapp).
assert (EF : frame_addr ly4 OP_CID fpos = oF cx fpos) by (unfold oF; symmetry; apply (Elay OP_CID fpos)).
rewrite EF in HF4096, HFceil, HFapp.
change (fs_frame_bytes OP_CID) with 128 in HF4096, HFceil, HFapp.
pose proof (frame_al64 SEGS B ly4 S4 W4 mem4 md4 OP_CID fpos HAR4 HinF) as (HFal & _ & _).
rewrite EF in HFal.
assert (HSHb : 2147450880 <= oSH cx fpos /\ oSH cx fpos + 16 <= 17594333495296).
{ assert (Hd0 : 0 <= oF cx fpos / 8) by (apply Z.div_pos; clear - HF4096; lia).
  assert (Hd1 : oF cx fpos / 8 < 2 ^ 44 - 16) by (apply Z.div_lt_upper_bound; clear - HFceil C1; lia).
  unfold oSH, SHADOW_OFF. clear - Hd0 Hd1. lia. }
destruct (FFL ly4 S4 W4 mem4 md4 OP_CID fpos HAR4 HinF) as (_ & HFLown & _ & _).
assert (EFL : oFL cx fpos = flag_addr ly4 OP_CID fpos).
{ unfold oFL, flag_addr. pose proof (Elay OP_CID fpos) as Ee. unfold frame_addr in Ee. clear - Ee. lia. }
rewrite <- EFL in HFLown.
pose proof (sep_block_frame SEGS B LAWS ly4 S4 W4 mem4 md4 bb mm OP_CID fpos HAR4 Hblk HinF) as DbF.
unfold zdisjoint in DbF. cbn [fst snd] in DbF. rewrite EF in DbF.
change (fs_frame_bytes OP_CID) with 128 in DbF.
pose proof (sep_block_frame SEGS B LAWS ly4 S4 W4 mem4 md4 bb mm (o_cid cx) (o_pos cx) HAR4 Hblk Hin4) as Dbg.
unfold zdisjoint in Dbg. cbn [fst snd] in Dbg. rewrite <- (Elay (o_cid cx) (o_pos cx)) in Dbg.
split; [|split].
- unfold opb_wr. intros [Hq | [Hq | Hq]].
  + clear - Hq Ha DbF. lia.
  + clear - Hq Ha Hbapp HSHb. lia.
  + apply (proj2 (Hbnown a Ha)). rewrite Hq. exact HFLown.
- clear - Ha Dbg Hfa1 Hfa2. lia.
- clear - Ha Hb4096 Hbceil C1. lia.
Qed.

Lemma opb_frame_nil : forall E rs (m m' : word -> option byte),
  (forall r, In r rs -> YP09.r_whi r <= YP09.r_wlo r) -> frame_of E rs m m' -> m' = m.
Proof.
intros E rs m m' Hro Hfr. apply functional_extensionality. intros x. apply Hfr.
intros (r & Hin & Hrng). pose proof (Hro r Hin) as Hq. clear - Hq Hrng. lia.
Qed.

(* The post's kept set across the fclose call. *)
Lemma opb_kept_call : forall (cx : ocx) (fpos : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
    (mem3 : word -> option byte) (md3 : Model) (ly5 : alayout) (S5 : astate) (W5 : world SEGS)
    (mem5 : word -> option byte) (md5 : Model) (fblk kev : Z),
  ajournal SEGS B (o_STK cx) (o_sp0 cx) (o_FP cx) (o_ly cx) (o_S cx) (o_W0 cx) (o_mem0 cx) (o_md0 cx)
    ((OP_CID, fpos) :: o_own cx) ly3 S3 W3 mem3 md3 kev ->
  ajournal SEGS B PFCLOSE_STK (osp1 cx) (asource_fp fblk) ly3 S3 W3 mem3 md3 [] ly5 S5 W5 mem5 md5 2 ->
  In (fblk, SRC_FILE_BLOCK) (ablocks B ly3 S3) ->
  ~ In (fblk, SRC_FILE_BLOCK) (ablocks B (o_lyc cx) (o_Sc cx)) ->
  (forall b m, In (b, m) (ablocks B (o_lyc cx) (o_Sc cx)) -> In (b, m) (ablocks B ly3 S3)) ->
  (forall b m, In (b, m) (ablocks B (o_lyc cx) (o_Sc cx)) -> In (b, m) (ablocks B ly5 S5)) ->
  frames S3 = (OP_CID, fpos) :: frames (o_Sc cx) ->
  (forall c p, frame_addr (o_lyc cx) c p = frame_addr ly3 c p) ->
  spZ (o_regs cx) - TPCAP_SOURCE_OPEN_STK <= osp1 cx - PFCLOSE_STK -> osp1 cx <= spZ (o_regs cx) ->
  alloc_ceiling + TPCAP_SOURCE_OPEN_STK <= spZ (o_regs cx) -> spZ (o_regs cx) <= 2 ^ 47 ->
  topen_kept SK SEGS B (o_lyc cx) (o_Sc cx) (o_W cx) (o_memc cx) W3 mem3
    (spZ (o_regs cx) - TPCAP_SOURCE_OPEN_STK) (spZ (o_regs cx)) (fun a => o_ps cx <= a < o_ps cx + 22) ->
  topen_kept SK SEGS B (o_lyc cx) (o_Sc cx) (o_W cx) (o_memc cx) W5 mem5
    (spZ (o_regs cx) - TPCAP_SOURCE_OPEN_STK) (spZ (o_regs cx)) (fun a => o_ps cx <= a < o_ps cx + 22).
Proof.
intros cx fpos ly3 S3 W3 mem3 md3 ly5 S5 W5 mem5 md5 fblk kev HJ3 HJc Hfin Hfresh Hincl3 Hincl5 Hfrs3 Elay Hw1 Hw2 Hslo Hshi HK.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ3 as (HAR3 & _).
pose proof HJc as (HAR5 & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & G4 & _ & Gpres & Gstk & _).
destruct (al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 fblk SRC_FILE_BLOCK HAR3 Hfin)
  as (_ & Hf4096 & Hfceil & Hfapp & _ & _).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hfapp.
change (req_size SRC_FILE_BLOCK) with 1304 in Hfceil, Hfapp.
destruct HK as (T1 & T2 & T3 & T4 & T5 & T6).
assert (HnFP : forall a, 4096 <= a -> ~ (fblk <= a < fblk + SRC_FILE_BLOCK) -> ~ inFP (asource_fp fblk) a).
{ intros a Ha Hn Hc. destruct (in_asource_fp fblk a Hc) as [Hq | Hq]; [exact (Hn Hq) | clear - Ha Hq; lia]. }
split; [|split; [|split; [|split; [|split]]]].
- intros a Ha Hn. rewrite (G1 a ltac:(clear - Ha; lia) ltac:(clear - Hn Hw1 Hw2; lia)). exact (T1 a Ha Hn).
- intros b0 m0 i Hb Hi HnE.
  assert (Hb3 : In (b0, m0) (ablocks B ly3 S3)) by (apply Hincl3; exact Hb).
  assert (Hb5 : In (b0, m0) (ablocks B ly5 S5)) by (apply Hincl5; exact Hb).
  destruct (al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 b0 m0 HAR3 Hb3) as (_ & Hb4096 & _ & _ & _ & _).
  rewrite (G2 b0 m0 i Hb3 Hb5 Hi).
  + exact (T2 b0 m0 i Hb Hi HnE).
  + apply HnFP; [clear - Hb4096 Hi; lia|].
    assert (Hne : (b0, m0) <> (fblk, SRC_FILE_BLOCK))
      by (intros Heq; rewrite Heq in Hb; exact (Hfresh Hb)).
    pose proof (sep_blocks SEGS B LAWS ly3 S3 W3 mem3 md3 b0 m0 fblk SRC_FILE_BLOCK HAR3 Hb3 Hfin Hne) as Db.
    unfold zdisjoint in Db. cbn [fst snd] in Db.
    change (req_size SRC_FILE_BLOCK) with 1304 in Db. unfold SRC_FILE_BLOCK.
    clear - Db Hi. lia.
- intros a Hi Ho He Hof.
  rewrite (G3 a Hi Ho He ltac:(apply fp_spares_off; exact Hof)). exact (T3 a Hi Ho He Hof).
- intros cid' pos' a Hin' Hrng HnE.
  assert (Hin3 : In (cid', pos') (frames S3)) by (rewrite Hfrs3; right; exact Hin').
  destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 cid' pos' HAR3 Hin3) as (Hg4096 & Hgceil & Hgapp).
  pose proof (fs_frame_bytes_nonneg cid') as Hgnn.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hgapp.
  pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 mem3 md3 fblk SRC_FILE_BLOCK cid' pos' HAR3 Hfin Hin3) as Dgf.
  unfold zdisjoint in Dgf. cbn [fst snd] in Dgf. change (req_size SRC_FILE_BLOCK) with 1304 in Dgf.
  assert (Hs1 : kLowMemEnd <= shadow_addr (frame_addr ly3 cid' pos') < kHighShadowEnd)
    by (apply shadow_addr_bounds; clear - Hg4096 Hgceil Hgnn C1 C4; lia).
  assert (Hs2 : shadow_addr (frame_addr ly3 cid' pos') + fs_frame_bytes cid' / 8
                <= shadow_addr (frame_addr ly3 cid' pos' + fs_frame_bytes cid'))
    by (apply shadow_range_end; exact Hgnn).
  assert (Hs3 : kLowMemEnd <= shadow_addr (frame_addr ly3 cid' pos' + fs_frame_bytes cid') < kHighShadowEnd)
    by (apply shadow_addr_bounds; clear - Hg4096 Hgceil Hgnn C1 C4; lia).
  unfold in_zr, frame_rng in Hrng. cbn [fst snd] in Hrng. rewrite (Elay cid' pos') in Hrng.
  rewrite (G4 cid' pos' a Hin3 ltac:(unfold in_zr, frame_rng; cbn [fst snd]; exact Hrng)).
  + exact (T4 cid' pos' a Hin' ltac:(unfold in_zr, frame_rng; cbn [fst snd];
             rewrite (Elay cid' pos'); exact Hrng) HnE).
  + apply HnFP; [destruct Hrng as [Hq|Hq]; [clear - Hq Hg4096; lia | clear - Hq Hs1 C5; lia]|].
    unfold SRC_FILE_BLOCK;
    destruct Hrng as [Hq|Hq]; [clear - Hq Dgf; lia | clear - Hq Hs1 Hs2 Hs3 C2 C5 Hfapp Hfceil C1; lia].
- intros a Ha Hn Hpr.
  eapply (apresent_transfer SEGS); [clear - Ha C1; lia
    | intros Him; pose proof (pa_segs_low a Him) as Hl; unfold kLowMemEnd in Hl; clear - Ha Hl C1; lia
    | apply G1; [clear - Ha; lia | clear - Hn Hw1 Hw2; lia]
    | exact (T5 a Ha Hn Hpr) ].
- intros a Ha.
  destruct (Z_lt_le_dec a (osp1 cx)) as [Hlo|Hlo].
  + destruct (Z_le_gt_dec (osp1 cx - PFCLOSE_STK) a) as [Hhi|Hhi].
    * apply Gpres. clear - Hlo Hhi. lia.
    * eapply (apresent_transfer SEGS); [clear - Ha Hw1 Hw2 Hslo Hshi C1; lia
        | intros Him; pose proof (pa_segs_low a Him) as Hl; unfold kLowMemEnd in Hl;
          clear - Ha Hw1 Hw2 Hslo Hshi Hl C1; lia
        | apply G1; [clear - Ha Hw1 Hw2 Hslo Hshi C1; lia | clear - Hhi; lia]
        | exact (T6 a Ha) ].
  + eapply (apresent_transfer SEGS); [clear - Ha Hw1 Hw2 Hslo Hshi C1; lia
      | intros Him; pose proof (pa_segs_low a Him) as Hl; unfold kLowMemEnd in Hl;
        clear - Ha Hw1 Hw2 Hslo Hshi Hl C1; lia
      | apply G1; [clear - Ha Hw1 Hw2 Hslo Hshi C1; lia | clear - Hlo; lia]
      | exact (T6 a Ha) ].
Qed.

(* ---- the refused tail: the fclose wrapper returned, ps->f = NULL, a0 = -1 -------------------------------- *)
Lemma opb_refuse_tail : forall (cx : ocx) (fpos : Z) (ly4 : alayout) (S4 : astate) (W4 : world SEGS)
    (ms4 : machine_state) (md4 : Model) (kev pc f : Z),
  op_pre SK B K MT FM_RA CTX roimg cx ->
  (pc = OPB_RET1 \/ pc = OPB_RET2) ->
  ms_pc_val ms4 = w64 (BASE + pc) -> ms_resv ms4 = None -> ms_svc_pending ms4 = None ->
  ms_rom ms4 = seg_rom SEGS -> ms_fregs ms4 = fp_regs -> ms_fcsr ms4 = fp_csr ->
  ajournal SEGS B (o_STK cx) (o_sp0 cx) (o_FP cx) (o_ly cx) (o_S cx) (o_W0 cx) (o_mem0 cx) (o_md0 cx)
    ((OP_CID, fpos) :: o_own cx) ly4 S4 W4 (ms_mem ms4) md4 kev ->
  kev <= o_k cx + EV_OPEN ->
  frames S4 = (OP_CID, fpos) :: frames (o_Sc cx) ->
  ~ In (OP_CID, fpos) (frames (o_Sc cx)) ->
  Permutation (ablocks B ly4 S4) (ablocks B (o_lyc cx) (o_Sc cx)) ->
  (forall b m, In (b, m) (ablocks B (o_lyc cx) (o_Sc cx)) -> In (b, m) (ablocks B ly4 S4)) ->
  mo_le MT (o_Sc cx) S4 (OPEN_METER MT) ->
  getr (ms_regs ms4) 2 = w64 (osp1 cx) -> getr (ms_regs ms4) 8 = w64 (spZ (o_regs cx)) ->
  getr (ms_regs ms4) 18 = w64 (oF cx fpos) -> getr (ms_regs ms4) 19 = w64 (o_ps cx) ->
  getr (ms_regs ms4) 21 = w64 (oSH cx fpos) -> getr (ms_regs ms4) 22 = w64 (oF cx fpos) ->
  getr (ms_regs ms4) 23 = w64 SHADOW_OFF -> getr (ms_regs ms4) 24 = w64 (SHADOW_OFF + o_ps cx / 8) ->
  getr (ms_regs ms4) 3 = getr (o_regs cx) 3 -> getr (ms_regs ms4) 4 = getr (o_regs cx) 4 ->
  getr (ms_regs ms4) 26 = getr (o_regs cx) 26 -> getr (ms_regs ms4) 27 = getr (o_regs cx) 27 ->
  rdword (aview SEGS (w_H W4) (ms_mem ms4)) (spZ (o_regs cx) - 8) = Some (raZ (o_regs cx)) ->
  (forall j, 0 <= j < 10 -> rdword (aview SEGS (w_H W4) (ms_mem ms4)) (spZ (o_regs cx) - 16 - 8 * j) =
     Some (bv_unsigned (getr (o_regs cx) (Z_to_bv 5 (if j <? 2 then 8 + j else 16 + j))))) ->
  rdword (aview SEGS (w_H W4) (ms_mem ms4)) (oF cx fpos + OP_FLAGPTR) = Some (oFL cx fpos) ->
  range_addressable (aview SEGS (w_H W4) (ms_mem ms4)) SHADOW_OFF (o_ps cx) 24 ->
  val_mem SEGS (rdW W4 (ms_mem ms4)) (o_ps cx) 8 f -> 0 <= f < 2 ^ 64 ->
  val_mem SEGS (rdW W4 (ms_mem ms4)) (o_ps cx + 12) 4 0 ->
  val_mem SEGS (rdW W4 (ms_mem ms4)) (o_ps cx + 16) 4 0 ->
  val_mem SEGS (rdW W4 (ms_mem ms4)) (o_ps cx + 20) 2 0 ->
  (forall i, 8 <= i < 12 -> aview SEGS (w_H W4) (ms_mem ms4) (o_ps cx + i)
     = aview SEGS (w_H (o_W cx)) (o_memc cx) (o_ps cx + i)) ->
  topen_kept SK SEGS B (o_lyc cx) (o_Sc cx) (o_W cx) (o_memc cx) W4 (ms_mem ms4)
    (spZ (o_regs cx) - TPCAP_SOURCE_OPEN_STK) (spZ (o_regs cx)) (fun a => o_ps cx <= a < o_ps cx + 22) ->
  m_fds md4 = m_fds (o_mdc cx) -> m_fs md4 = m_fs (o_mdc cx) ->
  asource_none SEGS K (rdW W4 (ms_mem ms4)) ->
  pcap_goodZ (o_C cx) = false ->
  SRr SEGS W4 (mkCfg ms4 md4) (op_post SK B K MT cx).
Proof.
intros cx fpos ly4 S4 W4 ms4 md4 kev pc f HPRE Hcase Hpc Hresv Hsvc Hrom Hfrg Hfcsr HJ4 Hkev Hfrs4 Hnin
  Hperm4 Hincl4 Hmo4 R2 R8 R18 R19 R21 R22 R23 R24 R3 R4 R26 R27 Hra8 Hsav Hflagp Hsh4 Hvf4 Hf64
  Hv12 Hv16 Hv20 Hkeep8 HKEPT4 Hfds4 Hfsm4 Hnone4 Hgood.
pose proof HPRE as HPRE'. unfold op_pre in HPRE'. cbv zeta in HPRE'.
destruct HPRE' as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hal16 & Hwlo & Hwhi & _ & _ & Hown & Hfa1 & Hfa2 &
  Hps0 & Hps8 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hnn & _).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : TPCAP_SOURCE_OPEN_STK = 18736) by reflexivity.
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof HJ4 as (HAR4 & Hly4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres4 & _).
assert (Elay : forall c p, frame_addr (o_lyc cx) c p = frame_addr ly4 c p)
  by (intros c p; unfold frame_addr; rewrite (opb_lay_F _ _ _ Hly4), (opb_lay_F _ _ _ Hly); reflexivity).
assert (Hin : In (o_cid cx, o_pos cx) (frames (o_Sc cx)))
  by (rewrite Hfrs; apply in_or_app; left; exact Hown).
assert (Hinfr : forall c p, In (c, p) (frames (o_Sc cx)) -> In (c, p) (frames S4))
  by (intros c p Hc; rewrite Hfrs4; right; exact Hc).
assert (Hin4 : In (o_cid cx, o_pos cx) (frames S4)) by (apply Hinfr; exact Hin).
assert (HinF : In (OP_CID, fpos) (frames S4)) by (rewrite Hfrs4; left; reflexivity).
destruct (opb_nwr cx fpos ly4 S4 W4 (ms_mem ms4) md4 kev HJ4 Hfrs4 Hnin Elay Hin Hfa1 Hfa2)
  as (NWps & NWimg & BDps & BDimg).
destruct (frames_bounds SEGS B LAWS ly4 S4 W4 (ms_mem ms4) md4 OP_CID fpos HAR4 HinF)
  as (HF4096 & HFceil & HFapp).
assert (EF : frame_addr ly4 OP_CID fpos = oF cx fpos) by (unfold oF; symmetry; apply (Elay OP_CID fpos)).
rewrite EF in HF4096, HFceil, HFapp.
change (fs_frame_bytes OP_CID) with 128 in HF4096, HFceil, HFapp.
destruct (frames_bounds SEGS B LAWS ly4 S4 W4 (ms_mem ms4) md4 (o_cid cx) (o_pos cx) HAR4 Hin4)
  as (Hg4096 & Hgceil & Hgapp).
rewrite <- (Elay (o_cid cx) (o_pos cx)) in Hg4096, Hgceil, Hgapp.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hgapp.
pose proof (fs_frame_bytes_nonneg (o_cid cx)) as Hgnn.
pose proof (frm_off_imgP B ly4 S4 W4 (ms_mem ms4) md4 (o_cid cx) (o_pos cx) HAR4 Hin4) as Hgimg.
rewrite <- (Elay (o_cid cx) (o_pos cx)) in Hgimg.
unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in Hgimg.
assert (Hpsb : 4096 <= o_ps cx /\ o_ps cx + 24 <= 140737479966720)
  by (clear - Hfa1 Hfa2 Hg4096 Hgceil C1; lia).
assert (Hsplo : alloc_ceiling + TPCAP_SOURCE_OPEN_STK <= spZ (o_regs cx))
  by (clear - Hceil Hslo Hwlo Hwhi; lia).
assert (Hspr : 0 <= spZ (o_regs cx) < 2 ^ 64) by (unfold spZ; clear; apply u64_range).
assert (HSHb : OPB_SB <= oSH cx fpos /\ oSH cx fpos + 16 <= OPB_SB + 2 ^ 44).
{ assert (Hd0 : 0 <= oF cx fpos / 8) by (apply Z.div_pos; clear - HF4096; lia).
  assert (Hd1 : oF cx fpos / 8 < 2 ^ 44 - 16) by (apply Z.div_lt_upper_bound; clear - HFceil C1; lia).
  unfold oSH, OPB_SB, SHADOW_OFF. clear - Hd0 Hd1. lia. }
assert (HFlt : 0 <= oF cx fpos < 2 ^ 64) by (clear - HF4096 HFceil C1; lia).
assert (HSHlt : 0 <= oSH cx fpos < 2 ^ 64) by (unfold OPB_SB in HSHb; clear - HSHb; lia).
pose proof (frame_al64 SEGS B ly4 S4 W4 (ms_mem ms4) md4 OP_CID fpos HAR4 HinF) as (HFal & _ & _).
rewrite EF in HFal.
assert (HSHm8 : oSH cx fpos mod 8 = 0).
{ destruct (opb_div8_mul64 _ HFal) as (HD & _). unfold oSH, SHADOW_OFF. rewrite HD.
  clear. replace (2147450880 + 8 * (oF cx fpos / 64)) with ((268431360 + oF cx fpos / 64) * 8) by lia.
  apply Z_mod_mult. }
destruct (opb_sp1_facts (spZ (o_regs cx)) ltac:(clear - Hspr; lia) Hal16) as (Hsp1r & Hsp1m32 & Hsp1m16).
assert (Hosp1 : osp1 cx = 32 * ((spZ (o_regs cx) - 96) / 32)) by (unfold osp1, OPEN_FRAME; reflexivity).
rewrite <- Hosp1 in Hsp1r, Hsp1m32, Hsp1m16.
(* the environment *)
set (E := Eimg (Ereg (ms_regs ms4) (opb_extra cx fpos f))).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms4) (opb_extra cx fpos f)) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (EREG : forall n (r : Prelude.reg), Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms4) r).
{ intros n r Hr. rewrite EL; [exact (ew_Ereg_nat _ _ n r Hr)|].
  pose proof (u5_range r) as Hu. unfold A_TEXT. clear - Hr Hu. lia. }
assert (EX : forall j, (j < 13)%nat -> ew E (32 + j) = nth j (opb_extra cx fpos f) (w64 0))
  by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ j)).
assert (E22 : ew E 22 = w64 (oF cx fpos)) by (rewrite (EREG 22%nat 22%bv eq_refl); exact R22).
assert (E21 : ew E 21 = w64 (oSH cx fpos)) by (rewrite (EREG 21%nat 21%bv eq_refl); exact R21).
assert (E19 : ew E 19 = w64 (o_ps cx)) by (rewrite (EREG 19%nat 19%bv eq_refl); exact R19).
assert (E23 : ew E 23 = w64 SHADOW_OFF) by (rewrite (EREG 23%nat 23%bv eq_refl); exact R23).
assert (E24 : ew E 24 = w64 (SHADOW_OFF + o_ps cx / 8)) by (rewrite (EREG 24%nat 24%bv eq_refl); exact R24).
assert (E8 : ew E 8 = w64 (spZ (o_regs cx))) by (rewrite (EREG 8%nat 8%bv eq_refl); exact R8).
assert (E2 : ew E 2 = w64 (osp1 cx)) by (rewrite (EREG 2%nat 2%bv eq_refl); exact R2).
assert (U2 : bv_unsigned (ew E 2) = osp1 cx)
  by (rewrite E2; apply unsigned_lit_small; clear - Hsp1r Hspr Hsplo C1 HTS; lia).
assert (E43 : ew E 43 = w64 f) by (exact (EX 11%nat ltac:(lia))).
assert (E44 : ew E 44 = w64 (oFL cx fpos)) by (exact (EX 12%nat ltac:(lia))).
assert (U22 : bv_unsigned (ew E 22) = oF cx fpos) by (rewrite E22; apply unsigned_lit_small; clear - HFlt; lia).
assert (U21 : bv_unsigned (ew E 21) = oSH cx fpos) by (rewrite E21; apply unsigned_lit_small; clear - HSHlt; lia).
assert (U19 : bv_unsigned (ew E 19) = o_ps cx) by (rewrite E19; apply unsigned_lit_small; clear - Hpsb; lia).
assert (U23 : bv_unsigned (ew E 23) = SHADOW_OFF)
  by (rewrite E23; apply unsigned_lit_small; unfold SHADOW_OFF; clear; lia).
assert (U8 : bv_unsigned (ew E 8) = spZ (o_regs cx)) by (rewrite E8; apply unsigned_lit_small; clear - Hspr; lia).
assert (U43 : bv_unsigned (ew E 43) = f) by (rewrite E43; apply unsigned_lit_small; clear - Hf64; lia).
assert (HSAV : forall j, (j < 11)%nat ->
  val_mem SEGS (rdW W4 (ms_mem ms4)) (spZ (o_regs cx) + (-8 - 8 * Z.of_nat j)) 8
    (bv_unsigned (nth j (opb_extra cx fpos f) (w64 0)))).
{ intros j Hj. apply (val_mem_of_rdword SEGS (w_H W4) (ms_mem ms4)).
  destruct j as [|j'];
  [ replace (spZ (o_regs cx) + (-8 - 8 * Z.of_nat 0)) with (spZ (o_regs cx) - 8) by (clear; lia);
    cbn [nth opb_extra]; exact Hra8 |].
  replace (spZ (o_regs cx) + (-8 - 8 * Z.of_nat (S j'))) with (spZ (o_regs cx) - 16 - 8 * Z.of_nat j')
    by (clear; lia).
  rewrite (Hsav (Z.of_nat j') ltac:(clear - Hj; lia)). f_equal.
  do 10 (destruct j' as [|j']; [cbn [nth opb_extra Z.ltb Z.compare]; reflexivity|]).
  cbn [length] in Hj. clear - Hj. lia. }
assert (HCH : forall j, (j < 11)%nat -> YP09.chunk_ok SEGS E (rdW W4 (ms_mem ms4)) (spZ (o_regs cx))
   (YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (32 + j) 0)))).
{ intros j Hj.
  apply (chunk_ok_val SEGS E _ (spZ (o_regs cx)) (-8 - 8 * Z.of_nat j) 8 (SOff (32 + j) 0)
    (bv_unsigned (nth j (opb_extra cx fpos f) (w64 0))));
  [ cbn [sv_denot]; rewrite (EX j ltac:(clear - Hj; lia)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | pose proof (u64_range (nth j (opb_extra cx fpos f) (w64 0))) as Hu;
    change (8 * Z.of_N 8) with 64; clear - Hu; lia
  | zside
  | exact (HSAV j Hj) ]. }
assert (HPSpres : forall o, 0 <= o < 24 -> apresent (w_H W4) (ms_mem ms4) (o_ps cx + o)).
{ intros o Ho. refine (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (o_ps cx + o) HJ4 _)).
  right. right. right. exists (o_cid cx), (o_pos cx). split; [right; exact Hown|]. left.
  unfold in_zr. cbn [fst snd]. rewrite <- (Elay (o_cid cx) (o_pos cx)).
  clear - Hfa1 Hfa2 Ho. lia. }
assert (HS : st_ok_pi SEGS VAL E (opb_ss pc opb_sr opb_rs_lo opb_facts) (restrict (w_H W4) ms4)).
{ assert (HS0 : st_ok_pi SEGS VAL E (opb_ss pc sr_atoms opb_rs_lo opb_facts) (restrict (w_H W4) ms4)).
  { rewrite (opb_ms_eta ms4 Hfrg Hsvc Hresv Hfcsr), Hpc, Hrom, restrict_mkst_fx.
    unfold opb_ss, opb_rs_lo, opb_facts. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
      unfold region_ok, opb_stack, opb_ps_lo;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      + rewrite U8. split; [clear - Hsplo C1 HTS; lia|]. split; [clear - Hspr; lia|].
        split; [intros o Ho; clear - Ho; lia|].
        unfold opb_stack_chunks. apply Forall_map, Forall_forall. intros j Hj.
        apply in_seq in Hj. apply HCH. clear - Hj. lia.
      + rewrite U19. split; [clear - Hpsb; lia|]. split; [clear - Hpsb; lia|].
        split; [intros o Ho; apply (apresent_writable SEGS); apply (HPSpres o ltac:(clear - Ho; lia))|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS E _ (o_ps cx) 0 8 (SOff 43 0) f);
        [ cbn [sv_denot]; rewrite E43, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (8 * Z.of_N 8) with 64; clear - Hf64; lia | zside | rewrite Z.add_0_r; exact Hvf4 ].
    - apply pairwise_disjoint_of_extents.
      unfold opb_rs_lo, opb_stack, opb_ps_lo, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U8, U19.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      clear - Hsplo C1 HTS Hpsb Hgceil Hfa2 Hfa1. repeat split; lia.
    - split; [|split; [exact I | exact I]].
      cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      repeat split; rewrite ?U2, ?U8, ?U19, ?U21, ?U22, ?U23;
      try exact I;
      try (change (2 ^ 6) with 64); try (change (2 ^ 5) with 32); try (change (2 ^ 4) with 16);
      try (change (2 ^ 3) with 8); try (change (2 ^ 0) with 1);
      first [ exact Hsp1m32 | exact Hal16 | exact Hps8 | exact HSHm8 | exact HFal | apply Z.mod_1_r
            | unfold OPB_SB, SHADOW_OFF; clear; lia
            | clear - Hsp1r Hsplo Hshi Hwhi H47 Htop Htop2 C1 HTS Hpsb HSHb HFlt HF4096 HFceil Hspr; lia ]. }
  unfold opb_sr, opb_sr_epi.
  refine (ast_ok_pi_set_reg_fp E _ _ (24%bv : bv 5) opb_sh8
    (ast_ok_pi_set_reg_fp E _ _ (18%bv : bv 5) (SOff 22 0) HS0 ltac:(vm_compute; reflexivity) _)
    ltac:(vm_compute; reflexivity) _).
  - cbn [ms_regs restrict mkst]. cbn [sv_denot]. rewrite U22, Z.add_0_r. exact (eq_sym R18).
  - cbn [ms_regs restrict mkst]. unfold opb_sh8.
    rewrite (shadow_decl_ok E 19%nat 23%nat 24%nat (o_ps cx) SHADOW_OFF E19 ltac:(clear - Hpsb; lia) E23 E24).
    cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E24. exact (eq_sym R24). }
assert (SHOK : sh_ok SEGS OPB_Bx OPB_SH E (rdW W4 (ms_mem ms4))).
{ unfold sh_ok, OPB_SH, OPB_Bx. apply Forall_cons; [|apply Forall_nil].
  unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
  rewrite (U_atom E 23%nat SHADOW_OFF E23 ltac:(unfold SHADOW_OFF; clear; lia)).
  rewrite (U_atom E 19%nat (o_ps cx) E19 ltac:(clear - Hpsb; lia)).
  split.
  - rewrite Z.add_0_r. rewrite <- (aview_rd_of SEGS). exact Hsh4.
  - intros a Ha. cbn [Z.min Z.max] in Ha. unfold SHADOW_OFF.
    clear - Ha Hgapp Hfa1 Hfa2 Hgnn. lia. }
destruct Hcase as [-> | ->].
all: paj_run_to_tok RUNTO HS HJ4 SHOK OPB_span OPB_EPI_A;
  [ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?ownx =>
      let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx ownx) end;
    apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; clear; lia|];
    eapply awr_ok_cons_gen;
    [ reflexivity | exact U19
    | cbn [YP09.r_wlo YP09.r_whi]; intros aW HaW;
      right; right; right; exists (o_cid cx), (o_pos cx); split; [right; exact Hown|]; left;
      unfold in_zr; cbn [fst snd]; rewrite <- (Elay (o_cid cx) (o_pos cx)); clear - Hfa1 Hfa2 HaW; lia
    | apply awr_ok_nil ] |].
all: (
  pose proof (kept_of_frame (segs := SEGS) E _ (w_H W4) (ms_mem ms4) (ms_mem ms)
    (fun a => o_ps cx <= a < o_ps cx + 8) HFr
    ltac:(intros bW wloW whiW aW HinW HrrW; vm_compute in HinW;
          repeat (destruct HinW as [HqW | HinW];
                  [injection HqW as <- <- <-; cbn [base_val] in HrrW; rewrite ?U8, ?U19 in HrrW;
                   clear - HrrW; lia|]);
          destruct HinW)) as UN1;
  assert (UNw : forall a, 0 <= a < 2 ^ 64 -> ~ (o_ps cx <= a < o_ps cx + 12) ->
            aview SEGS (w_H W4) (ms_mem ms) a = aview SEGS (w_H W4) (ms_mem ms4) a)
    by (intros a Ha Hn; apply UN1; [exact Ha | clear - Hn; lia]);
  assert (Hra8' : rdword (aview SEGS (w_H W4) (ms_mem ms)) (spZ (o_regs cx) - 8) = Some (raZ (o_regs cx)))
    by (rewrite (opb_rdword_ext (aview SEGS (w_H W4) (ms_mem ms4)) (aview SEGS (w_H W4) (ms_mem ms))
          (spZ (o_regs cx) - 8)
          ltac:(intros i Hi; apply UN1;
                [clear - Hspr Hsplo C1 HTS Hi; lia
                | clear - Hi Hfa1 Hfa2 Hgceil Hsplo C1 HTS Hpsb; lia])); exact Hra8);
  assert (Hsav' : forall j, 0 <= j < 10 ->
            rdword (aview SEGS (w_H W4) (ms_mem ms)) (spZ (o_regs cx) - 16 - 8 * j) =
            Some (bv_unsigned (getr (o_regs cx) (Z_to_bv 5 (if j <? 2 then 8 + j else 16 + j)))))
    by (intros j Hj;
        rewrite (opb_rdword_ext (aview SEGS (w_H W4) (ms_mem ms4)) (aview SEGS (w_H W4) (ms_mem ms))
          (spZ (o_regs cx) - 16 - 8 * j)
          ltac:(intros i Hi; apply UN1;
                [clear - Hspr Hsplo C1 HTS Hi Hj; lia
                | clear - Hi Hj Hfa1 Hfa2 Hgceil Hsplo C1 HTS Hpsb; lia]));
        exact (Hsav j Hj));
  assert (Hflagp' : rdword (aview SEGS (w_H W4) (ms_mem ms)) (oF cx fpos + OP_FLAGPTR) = Some (oFL cx fpos))
    by (rewrite (opb_rdword_ext (aview SEGS (w_H W4) (ms_mem ms4)) (aview SEGS (w_H W4) (ms_mem ms))
          (oF cx fpos + OP_FLAGPTR)
          ltac:(intros i Hi; apply UN1;
                [unfold OP_FLAGPTR; clear - HF4096 HFceil C1 Hi; lia
                | unfold OP_FLAGPTR; intros Hc;
                  apply (NWps (oF cx fpos + 120 + i) ltac:(clear - Hc; lia));
                  unfold opb_wr; left; clear - Hi; lia])); exact Hflagp);
  pose proof HS as (Mfrg & Mpc & Msvc & Mresv & Mfcsr & Mrom & _);
  cbn [restrict ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom] in Mfrg, Mpc, Msvc, Mresv, Mfcsr, Mrom;
  cbn [abs_ss setpc ss_pc ss_resv resv_denot opb_ss] in Mpc, Mresv;
  prreg HS (3%bv : bv 5) P3; prreg HS (4%bv : bv 5) P4;
  prreg HS (8%bv : bv 5) P8; prreg HS (10%bv : bv 5) P10; prreg HS (18%bv : bv 5) P18;
  prreg HS (21%bv : bv 5) P21; prreg HS (22%bv : bv 5) P22; prreg HS (26%bv : bv 5) P26;
  prreg HS (27%bv : bv 5) P27;
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
    let r1 := eval vm_compute in (nth 1 (ss_mem ssx) opb_ps_lo) in
    pose proof (st_ok_pi_region_nth E ssx (restrict (w_H W4) msx) 1 r1 HS ltac:(vm_compute; reflexivity)) as HR1
  end;
  cbn [ms_mem restrict mkst] in HR1;
  pose proof (field_of_region E (rdW W4 (ms_mem ms)) 19%nat (o_ps cx) _ 0 24 0 8 0 8%N (SLit 0) 0 HR1 U19
    ltac:(cbn; tauto) ltac:(reflexivity) ltac:(clear; lia) ltac:(clear; lia)) as Vps0;
  change (N.to_nat 8) with 8%nat in Vps0; rewrite Z.add_0_r in Vps0;
  eapply SRr_mono;
  [ exact (opb_epi cx fpos ly4 S4 W4 ms _ kev (-1) (-1) OPB_EPI_A HPRE
      (or_intror (conj (or_introl eq_refl) eq_refl))
      Mpc Mresv Msvc Mrom Mfrg Mfcsr HJ4 Hfrs4
      ltac:(rewrite P8, E8; reflexivity)
      ltac:(rewrite P10; unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; vm_compute; reflexivity)
      ltac:(rewrite P18, E22; reflexivity)
      ltac:(rewrite P21, E21; reflexivity)
      ltac:(rewrite P22, E22; reflexivity)
      ltac:(rewrite P3, (EREG 3%nat 3%bv eq_refl); exact R3)
      ltac:(rewrite P4, (EREG 4%nat 4%bv eq_refl); exact R4)
      ltac:(rewrite P26, (EREG 26%nat 26%bv eq_refl); exact R26)
      ltac:(rewrite P27, (EREG 27%nat 27%bv eq_refl); exact R27)
      Hra8' Hsav' Hflagp')
  | ]).
all: (cbv beta; intros W2 c2 _ (S2 & regs2 & mem2 & md2 & -> & -> & HJ2 & HP2 & Ha0 & Hfrs2 & Hab2 &
        (fs2 & Efs2) & Hfd2 & Hfs2 & HKEEP & HPRES)).
all: (
  assert (HPG : forall a, apresent (w_H W4) (ms_mem ms4) a -> apresent (w_H W4) (ms_mem ms) a)
    by (intros a Ha; exact (apresent_grows (w_H W4) (ms_mem ms4) (ms_mem ms) a HG Ha));
  assert (KPS2 : forall a n v, o_ps cx + 8 <= a -> a + Z.of_nat n <= o_ps cx + 24 ->
            val_mem SEGS (rdW W4 (ms_mem ms4)) a n v -> val_mem SEGS (rdW W4 mem2) a n v)
    by (intros a n v Ha1 Ha2 Hv; eapply opb_vm_frame; [|exact Hv]; intros x Hx;
        apply (mbyte_of_aview SEGS);
        rewrite (HKEEP x ltac:(apply BDps; clear - Ha1 Ha2 Hx; lia)
                          ltac:(apply NWps; clear - Ha1 Ha2 Hx; lia));
        apply UN1; [apply BDps; clear - Ha1 Ha2 Hx; lia | clear - Ha1 Ha2 Hx; lia]);
  unfold op_post; cbv zeta; unfold tpcap_source_open_post;
  exists ly4, S2, regs2, mem2, md2;
  split; [reflexivity|];
  split; [exact HP2|];
  split; [exact Hfrs2|];
  split; [rewrite Hfd2, (proj1 (opb_wvb_fds_fs _ _ _)); exact Hfds4|];
  split; [rewrite Hfs2, (proj2 (opb_wvb_fds_fs _ _ _)); exact Hfsm4|];
  split;
  [ exact (opb_kept_step cx fpos ly4 S4 W4 (ms_mem ms) mem2 _ kev _ _ _ HJ4 Hfrs4 Hnin Elay Hincl4
             (opb_kept_ps cx ly4 S4 W4 (ms_mem ms4) (ms_mem ms) md4 _ _ HAR4 Hin4 Hinfr Elay Hincl4
                Hfa1 Hfa2 HKEPT4 UNw HPG) HKEEP HPRES) |];
  split; [rewrite Efs2; apply (mo_le_set_fs_r MT MLAWF); exact Hmo4|];
  split; [exact (KPS2 (o_ps cx + 12) 4%nat 0 ltac:(clear; lia) ltac:(clear; cbn; lia) Hv12)|];
  split; [exact (KPS2 (o_ps cx + 16) 4%nat 0 ltac:(clear; lia) ltac:(clear; cbn; lia) Hv16)|];
  split; [exact (KPS2 (o_ps cx + 20) 2%nat 0 ltac:(clear; lia) ltac:(clear; cbn; lia) Hv20)|];
  right;
  split; [eapply ajournal_mono_k; [exact HJ2 | exact Hkev]|];
  split; [exact Ha0|];
  split; [exact Hgood|];
  split;
  [ eapply opb_vm_frame; [|exact Vps0]; intros x Hx; apply (mbyte_of_aview SEGS);
    apply HKEEP; [apply BDps; clear - Hx; cbn in Hx; lia | apply NWps; clear - Hx; cbn in Hx; lia] |];
  split;
  [ intros i Hi;
    rewrite (HKEEP (o_ps cx + i) ltac:(apply BDps; clear - Hi; lia) ltac:(apply NWps; clear - Hi; lia));
    rewrite (UN1 (o_ps cx + i) ltac:(apply BDps; clear - Hi; lia) ltac:(cbv beta; clear - Hi; lia));
    exact (Hkeep8 i Hi) |];
  split; [rewrite Hab2; exact Hperm4|];
  apply (opb_asource_none_frame (rdW W4 (ms_mem ms4)) (rdW W4 mem2)); [|exact Hnone4];
  intros a Ha; apply (mbyte_of_aview SEGS);
  pose proof (opb_src_env_img a Ha) as Hr;
  rewrite (HKEEP a ltac:(apply BDimg; exact Hr) ltac:(apply NWimg; exact Hr));
  apply UN1; [apply BDimg; exact Hr
             | cbv beta; unfold pcap_img_end, YImgTop.IMG_TOP in Hr;
               clear - Hr Hgimg Hfa1 Hfa2 Hgnn; lia]).
Qed.

(* ---- the accepted tail: a good magic, ps->swapped, a0 = 0 ------------------------------------------------ *)
Lemma opb_accept_tail : forall (cx : ocx) (fpos : Z) (ly4 : alayout) (S4 : astate) (W4 : world SEGS)
    (ms4 : machine_state) (md4 : Model) (kev pc f swv : Z),
  op_pre SK B K MT FM_RA CTX roimg cx ->
  (pc = OPB_SWAP /\ swv = 1) \/ (pc = OPB_NATIVE /\ swv = 0) ->
  ms_pc_val ms4 = w64 (BASE + pc) -> ms_resv ms4 = None -> ms_svc_pending ms4 = None ->
  ms_rom ms4 = seg_rom SEGS -> ms_fregs ms4 = fp_regs -> ms_fcsr ms4 = fp_csr ->
  ajournal SEGS B (o_STK cx) (o_sp0 cx) (o_FP cx) (o_ly cx) (o_S cx) (o_W0 cx) (o_mem0 cx) (o_md0 cx)
    ((OP_CID, fpos) :: o_own cx) ly4 S4 W4 (ms_mem ms4) md4 kev ->
  kev <= o_k cx + EV_FUZZ_FOPEN ->
  frames S4 = (OP_CID, fpos) :: frames (o_Sc cx) ->
  ~ In (OP_CID, fpos) (frames (o_Sc cx)) ->
  ablocks B ly4 S4 = ablocks B (o_lyc cx) (o_Sc cx) ++ [(f, SRC_FILE_BLOCK)] ->
  (forall b m, In (b, m) (ablocks B (o_lyc cx) (o_Sc cx)) -> In (b, m) (ablocks B ly4 S4)) ->
  mo_le MT (o_Sc cx) S4 (mo_malloc MT SRC_FILE_BLOCK) ->
  4096 <= f -> f mod 16 = 0 ->
  asource_at SEGS K (rdW W4 (ms_mem ms4)) f (o_b cx) (o_C cx) 24 ->
  In (o_b cx, Z.of_nat (length (o_C cx))) (ablocks B ly4 S4) ->
  getr (ms_regs ms4) 2 = w64 (osp1 cx) -> getr (ms_regs ms4) 8 = w64 (spZ (o_regs cx)) ->
  getr (ms_regs ms4) 18 = w64 (oF cx fpos) -> getr (ms_regs ms4) 19 = w64 (o_ps cx) ->
  getr (ms_regs ms4) 21 = w64 (oSH cx fpos) -> getr (ms_regs ms4) 22 = w64 (oF cx fpos) ->
  getr (ms_regs ms4) 23 = w64 SHADOW_OFF -> getr (ms_regs ms4) 24 = w64 (SHADOW_OFF + o_ps cx / 8) ->
  getr (ms_regs ms4) 3 = getr (o_regs cx) 3 -> getr (ms_regs ms4) 4 = getr (o_regs cx) 4 ->
  getr (ms_regs ms4) 26 = getr (o_regs cx) 26 -> getr (ms_regs ms4) 27 = getr (o_regs cx) 27 ->
  rdword (aview SEGS (w_H W4) (ms_mem ms4)) (spZ (o_regs cx) - 8) = Some (raZ (o_regs cx)) ->
  (forall j, 0 <= j < 10 -> rdword (aview SEGS (w_H W4) (ms_mem ms4)) (spZ (o_regs cx) - 16 - 8 * j) =
     Some (bv_unsigned (getr (o_regs cx) (Z_to_bv 5 (if j <? 2 then 8 + j else 16 + j))))) ->
  rdword (aview SEGS (w_H W4) (ms_mem ms4)) (oF cx fpos + OP_FLAGPTR) = Some (oFL cx fpos) ->
  range_addressable (aview SEGS (w_H W4) (ms_mem ms4)) SHADOW_OFF (o_ps cx) 24 ->
  val_mem SEGS (rdW W4 (ms_mem ms4)) (o_ps cx) 8 f -> 0 <= f < 2 ^ 64 ->
  val_mem SEGS (rdW W4 (ms_mem ms4)) (o_ps cx + 12) 4 0 ->
  val_mem SEGS (rdW W4 (ms_mem ms4)) (o_ps cx + 16) 4 0 ->
  val_mem SEGS (rdW W4 (ms_mem ms4)) (o_ps cx + 20) 2 0 ->
  (forall i, 8 <= i < 12 -> aview SEGS (w_H W4) (ms_mem ms4) (o_ps cx + i)
     = aview SEGS (w_H (o_W cx)) (o_memc cx) (o_ps cx + i)) ->
  topen_kept SK SEGS B (o_lyc cx) (o_Sc cx) (o_W cx) (o_memc cx) W4 (ms_mem ms4)
    (spZ (o_regs cx) - TPCAP_SOURCE_OPEN_STK) (spZ (o_regs cx)) (fun a => o_ps cx <= a < o_ps cx + 22) ->
  m_fds md4 = m_fds (o_mdc cx) -> m_fs md4 = m_fs (o_mdc cx) ->
  pcap_goodZ (o_C cx) = true -> swv = pcap_swZ (o_C cx) ->
  SRr SEGS W4 (mkCfg ms4 md4) (op_post SK B K MT cx).
Proof.
intros cx fpos ly4 S4 W4 ms4 md4 kev pc f swv HPRE Hcase Hpc Hresv Hsvc Hrom Hfrg Hfcsr HJ4 Hkev Hfrs4 Hnin
  Hperm4 Hincl4 Hmo4 Hf4096 Hf16 HSRC4 Hbblk R2 R8 R18 R19 R21 R22 R23 R24 R3 R4 R26 R27 Hra8 Hsav Hflagp
  Hsh4 Hvf4 Hf64 Hv12 Hv16 Hv20 Hkeep8 HKEPT4 Hfds4 Hfsm4 Hgood Hswv.
pose proof HPRE as HPRE'. unfold op_pre in HPRE'. cbv zeta in HPRE'.
destruct HPRE' as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hal16 & Hwlo & Hwhi & _ & _ & Hown & Hfa1 & Hfa2 &
  Hps0 & Hps8 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hnn & _).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : TPCAP_SOURCE_OPEN_STK = 18736) by reflexivity.
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof HJ4 as (HAR4 & Hly4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres4 & _).
assert (Elay : forall c p, frame_addr (o_lyc cx) c p = frame_addr ly4 c p)
  by (intros c p; unfold frame_addr; rewrite (opb_lay_F _ _ _ Hly4), (opb_lay_F _ _ _ Hly); reflexivity).
assert (Hin : In (o_cid cx, o_pos cx) (frames (o_Sc cx)))
  by (rewrite Hfrs; apply in_or_app; left; exact Hown).
assert (Hinfr : forall c p, In (c, p) (frames (o_Sc cx)) -> In (c, p) (frames S4))
  by (intros c p Hc; rewrite Hfrs4; right; exact Hc).
assert (Hin4 : In (o_cid cx, o_pos cx) (frames S4)) by (apply Hinfr; exact Hin).
assert (HinF : In (OP_CID, fpos) (frames S4)) by (rewrite Hfrs4; left; reflexivity).
destruct (opb_nwr cx fpos ly4 S4 W4 (ms_mem ms4) md4 kev HJ4 Hfrs4 Hnin Elay Hin Hfa1 Hfa2)
  as (NWps & NWimg & BDps & BDimg).
destruct (frames_bounds SEGS B LAWS ly4 S4 W4 (ms_mem ms4) md4 OP_CID fpos HAR4 HinF)
  as (HF4096 & HFceil & HFapp).
assert (EF : frame_addr ly4 OP_CID fpos = oF cx fpos) by (unfold oF; symmetry; apply (Elay OP_CID fpos)).
rewrite EF in HF4096, HFceil, HFapp.
change (fs_frame_bytes OP_CID) with 128 in HF4096, HFceil, HFapp.
destruct (frames_bounds SEGS B LAWS ly4 S4 W4 (ms_mem ms4) md4 (o_cid cx) (o_pos cx) HAR4 Hin4)
  as (Hg4096 & Hgceil & Hgapp).
rewrite <- (Elay (o_cid cx) (o_pos cx)) in Hg4096, Hgceil, Hgapp.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hgapp.
pose proof (fs_frame_bytes_nonneg (o_cid cx)) as Hgnn.
pose proof (frm_off_imgP B ly4 S4 W4 (ms_mem ms4) md4 (o_cid cx) (o_pos cx) HAR4 Hin4) as Hgimg.
rewrite <- (Elay (o_cid cx) (o_pos cx)) in Hgimg.
unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in Hgimg.
assert (Hpsb : 4096 <= o_ps cx /\ o_ps cx + 24 <= 140737479966720)
  by (clear - Hfa1 Hfa2 Hg4096 Hgceil C1; lia).
assert (Hsplo : alloc_ceiling + TPCAP_SOURCE_OPEN_STK <= spZ (o_regs cx))
  by (clear - Hceil Hslo Hwlo Hwhi; lia).
assert (Hspr : 0 <= spZ (o_regs cx) < 2 ^ 64) by (unfold spZ; clear; apply u64_range).
assert (HSHb : OPB_SB <= oSH cx fpos /\ oSH cx fpos + 16 <= OPB_SB + 2 ^ 44).
{ assert (Hd0 : 0 <= oF cx fpos / 8) by (apply Z.div_pos; clear - HF4096; lia).
  assert (Hd1 : oF cx fpos / 8 < 2 ^ 44 - 16) by (apply Z.div_lt_upper_bound; clear - HFceil C1; lia).
  unfold oSH, OPB_SB, SHADOW_OFF. clear - Hd0 Hd1. lia. }
assert (HFlt : 0 <= oF cx fpos < 2 ^ 64) by (clear - HF4096 HFceil C1; lia).
assert (HSHlt : 0 <= oSH cx fpos < 2 ^ 64) by (unfold OPB_SB in HSHb; clear - HSHb; lia).
pose proof (frame_al64 SEGS B ly4 S4 W4 (ms_mem ms4) md4 OP_CID fpos HAR4 HinF) as (HFal & _ & _).
rewrite EF in HFal.
assert (HSHm8 : oSH cx fpos mod 8 = 0).
{ destruct (opb_div8_mul64 _ HFal) as (HD & _). unfold oSH, SHADOW_OFF. rewrite HD.
  clear. replace (2147450880 + 8 * (oF cx fpos / 64)) with ((268431360 + oF cx fpos / 64) * 8) by lia.
  apply Z_mod_mult. }
destruct (opb_sp1_facts (spZ (o_regs cx)) ltac:(clear - Hspr; lia) Hal16) as (Hsp1r & Hsp1m32 & Hsp1m16).
assert (Hosp1 : osp1 cx = 32 * ((spZ (o_regs cx) - 96) / 32)) by (unfold osp1, OPEN_FRAME; reflexivity).
rewrite <- Hosp1 in Hsp1r, Hsp1m32, Hsp1m16.
(* the environment *)
set (E := Eimg (Ereg (ms_regs ms4) (opb_extra cx fpos f))).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms4) (opb_extra cx fpos f)) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (EREG : forall n (r : Prelude.reg), Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms4) r).
{ intros n r Hr. rewrite EL; [exact (ew_Ereg_nat _ _ n r Hr)|].
  pose proof (u5_range r) as Hu. unfold A_TEXT. clear - Hr Hu. lia. }
assert (EX : forall j, (j < 13)%nat -> ew E (32 + j) = nth j (opb_extra cx fpos f) (w64 0))
  by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ j)).
assert (E22 : ew E 22 = w64 (oF cx fpos)) by (rewrite (EREG 22%nat 22%bv eq_refl); exact R22).
assert (E21 : ew E 21 = w64 (oSH cx fpos)) by (rewrite (EREG 21%nat 21%bv eq_refl); exact R21).
assert (E19 : ew E 19 = w64 (o_ps cx)) by (rewrite (EREG 19%nat 19%bv eq_refl); exact R19).
assert (E23 : ew E 23 = w64 SHADOW_OFF) by (rewrite (EREG 23%nat 23%bv eq_refl); exact R23).
assert (E24 : ew E 24 = w64 (SHADOW_OFF + o_ps cx / 8)) by (rewrite (EREG 24%nat 24%bv eq_refl); exact R24).
assert (E8 : ew E 8 = w64 (spZ (o_regs cx))) by (rewrite (EREG 8%nat 8%bv eq_refl); exact R8).
assert (E2 : ew E 2 = w64 (osp1 cx)) by (rewrite (EREG 2%nat 2%bv eq_refl); exact R2).
assert (U2 : bv_unsigned (ew E 2) = osp1 cx)
  by (rewrite E2; apply unsigned_lit_small; clear - Hsp1r Hspr Hsplo C1 HTS; lia).
assert (E43 : ew E 43 = w64 f) by (exact (EX 11%nat ltac:(lia))).
assert (E44 : ew E 44 = w64 (oFL cx fpos)) by (exact (EX 12%nat ltac:(lia))).
assert (U22 : bv_unsigned (ew E 22) = oF cx fpos) by (rewrite E22; apply unsigned_lit_small; clear - HFlt; lia).
assert (U21 : bv_unsigned (ew E 21) = oSH cx fpos) by (rewrite E21; apply unsigned_lit_small; clear - HSHlt; lia).
assert (U19 : bv_unsigned (ew E 19) = o_ps cx) by (rewrite E19; apply unsigned_lit_small; clear - Hpsb; lia).
assert (U23 : bv_unsigned (ew E 23) = SHADOW_OFF)
  by (rewrite E23; apply unsigned_lit_small; unfold SHADOW_OFF; clear; lia).
assert (U8 : bv_unsigned (ew E 8) = spZ (o_regs cx)) by (rewrite E8; apply unsigned_lit_small; clear - Hspr; lia).
assert (U43 : bv_unsigned (ew E 43) = f) by (rewrite E43; apply unsigned_lit_small; clear - Hf64; lia).
assert (HSAV : forall j, (j < 11)%nat ->
  val_mem SEGS (rdW W4 (ms_mem ms4)) (spZ (o_regs cx) + (-8 - 8 * Z.of_nat j)) 8
    (bv_unsigned (nth j (opb_extra cx fpos f) (w64 0)))).
{ intros j Hj. apply (val_mem_of_rdword SEGS (w_H W4) (ms_mem ms4)).
  destruct j as [|j'];
  [ replace (spZ (o_regs cx) + (-8 - 8 * Z.of_nat 0)) with (spZ (o_regs cx) - 8) by (clear; lia);
    cbn [nth opb_extra]; exact Hra8 |].
  replace (spZ (o_regs cx) + (-8 - 8 * Z.of_nat (S j'))) with (spZ (o_regs cx) - 16 - 8 * Z.of_nat j')
    by (clear; lia).
  rewrite (Hsav (Z.of_nat j') ltac:(clear - Hj; lia)). f_equal.
  do 10 (destruct j' as [|j']; [cbn [nth opb_extra Z.ltb Z.compare]; reflexivity|]).
  cbn [length] in Hj. clear - Hj. lia. }
assert (HCH : forall j, (j < 11)%nat -> YP09.chunk_ok SEGS E (rdW W4 (ms_mem ms4)) (spZ (o_regs cx))
   (YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (32 + j) 0)))).
{ intros j Hj.
  apply (chunk_ok_val SEGS E _ (spZ (o_regs cx)) (-8 - 8 * Z.of_nat j) 8 (SOff (32 + j) 0)
    (bv_unsigned (nth j (opb_extra cx fpos f) (w64 0))));
  [ cbn [sv_denot]; rewrite (EX j ltac:(clear - Hj; lia)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | pose proof (u64_range (nth j (opb_extra cx fpos f) (w64 0))) as Hu;
    change (8 * Z.of_N 8) with 64; clear - Hu; lia
  | zside
  | exact (HSAV j Hj) ]. }
assert (HPSpres : forall o, 0 <= o < 24 -> apresent (w_H W4) (ms_mem ms4) (o_ps cx + o)).
{ intros o Ho. refine (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (o_ps cx + o) HJ4 _)).
  right. right. right. exists (o_cid cx), (o_pos cx). split; [right; exact Hown|]. left.
  unfold in_zr. cbn [fst snd]. rewrite <- (Elay (o_cid cx) (o_pos cx)).
  clear - Hfa1 Hfa2 Ho. lia. }
assert (HS : st_ok_pi SEGS VAL E (opb_ss pc opb_sr opb_rs_hi opb_facts) (restrict (w_H W4) ms4)).
{ assert (HS0 : st_ok_pi SEGS VAL E (opb_ss pc sr_atoms opb_rs_hi opb_facts) (restrict (w_H W4) ms4)).
  { rewrite (opb_ms_eta ms4 Hfrg Hsvc Hresv Hfcsr), Hpc, Hrom, restrict_mkst_fx.
    unfold opb_ss, opb_rs_hi, opb_facts. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
      unfold region_ok, opb_stack, opb_ps_hi;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      + rewrite U8. split; [clear - Hsplo C1 HTS; lia|]. split; [clear - Hspr; lia|].
        split; [intros o Ho; clear - Ho; lia|].
        unfold opb_stack_chunks. apply Forall_map, Forall_forall. intros j Hj.
        apply in_seq in Hj. apply HCH. clear - Hj. lia.
      + rewrite U19. split; [clear - Hpsb; lia|]. split; [clear - Hpsb; lia|].
        split; [intros o Ho; apply (apresent_writable SEGS); apply (HPSpres o ltac:(clear - Ho; lia))|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS E _ (o_ps cx) 0 8 (SOff 43 0) f);
        [ cbn [sv_denot]; rewrite E43, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (8 * Z.of_N 8) with 64; clear - Hf64; lia | zside | rewrite Z.add_0_r; exact Hvf4 ].
    - apply pairwise_disjoint_of_extents.
      unfold opb_rs_hi, opb_stack, opb_ps_hi, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U8, U19.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      clear - Hsplo C1 HTS Hpsb Hgceil Hfa2 Hfa1. repeat split; lia.
    - split; [|split; [exact I | exact I]].
      cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      repeat split; rewrite ?U2, ?U8, ?U19, ?U21, ?U22, ?U23;
      try exact I;
      try (change (2 ^ 6) with 64); try (change (2 ^ 5) with 32); try (change (2 ^ 4) with 16);
      try (change (2 ^ 3) with 8); try (change (2 ^ 0) with 1);
      first [ exact Hsp1m32 | exact Hal16 | exact Hps8 | exact HSHm8 | exact HFal | apply Z.mod_1_r
            | unfold OPB_SB, SHADOW_OFF; clear; lia
            | clear - Hsp1r Hsplo Hshi Hwhi H47 Htop Htop2 C1 HTS Hpsb HSHb HFlt HF4096 HFceil Hspr; lia ]. }
  unfold opb_sr, opb_sr_epi.
  refine (ast_ok_pi_set_reg_fp E _ _ (24%bv : bv 5) opb_sh8
    (ast_ok_pi_set_reg_fp E _ _ (18%bv : bv 5) (SOff 22 0) HS0 ltac:(vm_compute; reflexivity) _)
    ltac:(vm_compute; reflexivity) _).
  - cbn [ms_regs restrict mkst]. cbn [sv_denot]. rewrite U22, Z.add_0_r. exact (eq_sym R18).
  - cbn [ms_regs restrict mkst]. unfold opb_sh8.
    rewrite (shadow_decl_ok E 19%nat 23%nat 24%nat (o_ps cx) SHADOW_OFF E19 ltac:(clear - Hpsb; lia) E23 E24).
    cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E24. exact (eq_sym R24). }
assert (SHOK : sh_ok SEGS OPB_Bx OPB_SH E (rdW W4 (ms_mem ms4))).
{ unfold sh_ok, OPB_SH, OPB_Bx. apply Forall_cons; [|apply Forall_nil].
  unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
  rewrite (U_atom E 23%nat SHADOW_OFF E23 ltac:(unfold SHADOW_OFF; clear; lia)).
  rewrite (U_atom E 19%nat (o_ps cx) E19 ltac:(clear - Hpsb; lia)).
  split.
  - rewrite Z.add_0_r. rewrite <- (aview_rd_of SEGS). exact Hsh4.
  - intros a Ha. cbn [Z.min Z.max] in Ha. unfold SHADOW_OFF.
    clear - Ha Hgapp Hfa1 Hfa2 Hgnn. lia. }
pose proof HJ4 as HJ4a.
destruct Hcase as [[-> ->] | [-> ->]].
all: paj_run_to_tok RUNTO HS HJ4 SHOK OPB_span OPB_EPI_A;
  [ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?ownx =>
      let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx ownx) end;
    apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; clear; lia|];
    eapply awr_ok_cons_gen;
    [ reflexivity | exact U19
    | cbn [YP09.r_wlo YP09.r_whi]; intros aW HaW;
      right; right; right; exists (o_cid cx), (o_pos cx); split; [right; exact Hown|]; left;
      unfold in_zr; cbn [fst snd]; rewrite <- (Elay (o_cid cx) (o_pos cx)); clear - Hfa1 Hfa2 HaW; lia
    | apply awr_ok_nil ] |].
all: (
  pose proof (kept_of_frame (segs := SEGS) E _ (w_H W4) (ms_mem ms4) (ms_mem ms)
    (fun a => o_ps cx + 8 <= a < o_ps cx + 12) HFr
    ltac:(intros bW wloW whiW aW HinW HrrW; vm_compute in HinW;
          repeat (destruct HinW as [HqW | HinW];
                  [injection HqW as <- <- <-; cbn [base_val] in HrrW; rewrite ?U8, ?U19 in HrrW;
                   clear - HrrW; lia|]);
          destruct HinW)) as UN1;
  assert (UNw : forall a, 0 <= a < 2 ^ 64 -> ~ (o_ps cx <= a < o_ps cx + 12) ->
            aview SEGS (w_H W4) (ms_mem ms) a = aview SEGS (w_H W4) (ms_mem ms4) a)
    by (intros a Ha Hn; apply UN1; [exact Ha | cbv beta; clear - Hn; lia]);
  assert (Hra8' : rdword (aview SEGS (w_H W4) (ms_mem ms)) (spZ (o_regs cx) - 8) = Some (raZ (o_regs cx)))
    by (rewrite (opb_rdword_ext (aview SEGS (w_H W4) (ms_mem ms4)) (aview SEGS (w_H W4) (ms_mem ms))
          (spZ (o_regs cx) - 8)
          ltac:(intros i Hi; apply UN1;
                [clear - Hspr Hsplo C1 HTS Hi; lia
                | cbv beta; clear - Hi Hfa1 Hfa2 Hgceil Hsplo C1 HTS Hpsb; lia])); exact Hra8);
  assert (Hsav' : forall j, 0 <= j < 10 ->
            rdword (aview SEGS (w_H W4) (ms_mem ms)) (spZ (o_regs cx) - 16 - 8 * j) =
            Some (bv_unsigned (getr (o_regs cx) (Z_to_bv 5 (if j <? 2 then 8 + j else 16 + j)))))
    by (intros j Hj;
        rewrite (opb_rdword_ext (aview SEGS (w_H W4) (ms_mem ms4)) (aview SEGS (w_H W4) (ms_mem ms))
          (spZ (o_regs cx) - 16 - 8 * j)
          ltac:(intros i Hi; apply UN1;
                [clear - Hspr Hsplo C1 HTS Hi Hj; lia
                | cbv beta; clear - Hi Hj Hfa1 Hfa2 Hgceil Hsplo C1 HTS Hpsb; lia]));
        exact (Hsav j Hj));
  assert (Hflagp' : rdword (aview SEGS (w_H W4) (ms_mem ms)) (oF cx fpos + OP_FLAGPTR) = Some (oFL cx fpos))
    by (rewrite (opb_rdword_ext (aview SEGS (w_H W4) (ms_mem ms4)) (aview SEGS (w_H W4) (ms_mem ms))
          (oF cx fpos + OP_FLAGPTR)
          ltac:(intros i Hi; apply UN1;
                [unfold OP_FLAGPTR; clear - HF4096 HFceil C1 Hi; lia
                | unfold OP_FLAGPTR; cbv beta; intros Hc;
                  apply (NWps (oF cx fpos + 120 + i) ltac:(clear - Hc; lia));
                  unfold opb_wr; left; clear - Hi; lia])); exact Hflagp);
  pose proof HS as (Mfrg & Mpc & Msvc & Mresv & Mfcsr & Mrom & _);
  cbn [restrict ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom] in Mfrg, Mpc, Msvc, Mresv, Mfcsr, Mrom;
  cbn [abs_ss setpc ss_pc ss_resv resv_denot opb_ss] in Mpc, Mresv;
  prreg HS (3%bv : bv 5) P3; prreg HS (4%bv : bv 5) P4;
  prreg HS (8%bv : bv 5) P8; prreg HS (10%bv : bv 5) P10; prreg HS (18%bv : bv 5) P18;
  prreg HS (21%bv : bv 5) P21; prreg HS (22%bv : bv 5) P22; prreg HS (26%bv : bv 5) P26;
  prreg HS (27%bv : bv 5) P27;
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
    let r1 := eval vm_compute in (nth 1 (ss_mem ssx) opb_ps_hi) in
    pose proof (st_ok_pi_region_nth E ssx (restrict (w_H W4) msx) 1 r1 HS ltac:(vm_compute; reflexivity)) as HR1
  end;
  cbn [ms_mem restrict mkst] in HR1;
  first
  [ pose proof (field_of_region E (rdW W4 (ms_mem ms)) 19%nat (o_ps cx) _ 0 24 8 12 8 4%N (SLit 1) 1 HR1 U19
      ltac:(cbn; tauto) ltac:(reflexivity) ltac:(clear; cbv; split; [discriminate | reflexivity])
      ltac:(clear; lia)) as Vsw
  | pose proof (field_of_region E (rdW W4 (ms_mem ms)) 19%nat (o_ps cx) _ 0 24 8 12 8 4%N (SLit 0) 0 HR1 U19
      ltac:(cbn; tauto) ltac:(reflexivity) ltac:(clear; cbv; split; [discriminate | reflexivity])
      ltac:(clear; lia)) as Vsw ];
  change (N.to_nat 4) with 4%nat in Vsw;
  pose proof (field_of_region E (rdW W4 (ms_mem ms)) 19%nat (o_ps cx) _ 0 24 8 12 0 8%N (SOff 43 0) f HR1 U19
    ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite E43, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
    ltac:(change (8 * Z.of_N 8) with 64; clear - Hf64; lia) ltac:(clear; lia)) as Vps0;
  change (N.to_nat 8) with 8%nat in Vps0; rewrite Z.add_0_r in Vps0;
  eapply SRr_mono;
  [ exact (opb_epi cx fpos ly4 S4 W4 ms _ kev 0 0 OPB_EPI_A HPRE
      (or_intror (conj (or_introl eq_refl) eq_refl))
      Mpc Mresv Msvc Mrom Mfrg Mfcsr HJ4 Hfrs4
      ltac:(rewrite P8, E8; reflexivity)
      ltac:(rewrite P10; reflexivity)
      ltac:(rewrite P18, E22; reflexivity)
      ltac:(rewrite P21, E21; reflexivity)
      ltac:(rewrite P22, E22; reflexivity)
      ltac:(rewrite P3, (EREG 3%nat 3%bv eq_refl); exact R3)
      ltac:(rewrite P4, (EREG 4%nat 4%bv eq_refl); exact R4)
      ltac:(rewrite P26, (EREG 26%nat 26%bv eq_refl); exact R26)
      ltac:(rewrite P27, (EREG 27%nat 27%bv eq_refl); exact R27)
      Hra8' Hsav' Hflagp')
  | ]).
all: (cbv beta; intros W2 c2 _ (S2 & regs2 & mem2 & md2 & -> & -> & HJ2 & HP2 & Ha0 & Hfrs2 & Hab2 &
        (fs2 & Efs2) & Hfd2 & Hfs2 & HKEEP & HPRES)).
all: (
  assert (HPG : forall a, apresent (w_H W4) (ms_mem ms4) a -> apresent (w_H W4) (ms_mem ms) a)
    by (intros a Ha; exact (apresent_grows (w_H W4) (ms_mem ms4) (ms_mem ms) a HG Ha));
  assert (KPS2 : forall a n v, o_ps cx + 12 <= a -> a + Z.of_nat n <= o_ps cx + 24 ->
            val_mem SEGS (rdW W4 (ms_mem ms4)) a n v -> val_mem SEGS (rdW W4 mem2) a n v)
    by (intros a n v Ha1 Ha2 Hv; eapply opb_vm_frame; [|exact Hv]; intros x Hx;
        apply (mbyte_of_aview SEGS);
        rewrite (HKEEP x ltac:(apply BDps; clear - Ha1 Ha2 Hx; lia)
                          ltac:(apply NWps; clear - Ha1 Ha2 Hx; lia));
        apply UN1; [apply BDps; clear - Ha1 Ha2 Hx; lia | cbv beta; clear - Ha1 Ha2 Hx; lia]);
  unfold op_post; cbv zeta; unfold tpcap_source_open_post;
  exists ly4, S2, regs2, mem2, md2;
  split; [reflexivity|];
  split; [exact HP2|];
  split; [exact Hfrs2|];
  split; [rewrite Hfd2, (proj1 (opb_wvb_fds_fs _ _ _)); exact Hfds4|];
  split; [rewrite Hfs2, (proj2 (opb_wvb_fds_fs _ _ _)); exact Hfsm4|];
  split;
  [ exact (opb_kept_step cx fpos ly4 S4 W4 (ms_mem ms) mem2 _ kev _ _ _ HJ4 Hfrs4 Hnin Elay Hincl4
             (opb_kept_ps cx ly4 S4 W4 (ms_mem ms4) (ms_mem ms) md4 _ _ HAR4 Hin4 Hinfr Elay Hincl4
                Hfa1 Hfa2 HKEPT4 UNw HPG) HKEEP HPRES) |];
  split; [rewrite Efs2; eapply mle_weaken;
          [exact MLAW | apply (mo_le_set_fs_r MT MLAWF); exact Hmo4
          | unfold OPEN_METER; pose proof (mo_free_nonneg MT MLAW) as Hf0; clear - Hf0; lia]|];
  split; [exact (KPS2 (o_ps cx + 12) 4%nat 0 ltac:(clear; lia) ltac:(clear; cbn; lia) Hv12)|];
  split; [exact (KPS2 (o_ps cx + 16) 4%nat 0 ltac:(clear; lia) ltac:(clear; cbn; lia) Hv16)|];
  split; [exact (KPS2 (o_ps cx + 20) 2%nat 0 ltac:(clear; lia) ltac:(clear; cbn; lia) Hv20)|];
  left;
  split; [eapply ajournal_mono_k; [exact HJ2 | exact Hkev]|];
  split; [exact Ha0|];
  split; [exact Hgood|];
  exists f;
  split; [exact Hf4096|];
  split; [exact Hf16|];
  split; [rewrite Hab2; exact Hperm4|];
  split;
  [ eapply opb_vm_frame; [|exact Vps0]; intros x Hx; apply (mbyte_of_aview SEGS);
    apply HKEEP; [apply BDps; clear - Hx; cbn in Hx; lia | apply NWps; clear - Hx; cbn in Hx; lia] |];
  split;
  [ rewrite <- Hswv; eapply opb_vm_frame; [|exact Vsw]; intros x Hx; apply (mbyte_of_aview SEGS);
    apply HKEEP; [apply BDps; clear - Hx; cbn in Hx; lia | apply NWps; clear - Hx; cbn in Hx; lia] |];
  split;
  [ apply (asource_at_frame K (rdW W4 (ms_mem ms4)) (rdW W4 mem2) f (o_b cx) (o_C cx) 24); [|exact HSRC4];
    intros a Ha; apply (mbyte_of_aview SEGS);
    destruct Ha as [Ha | [Ha | Ha]];
    [ destruct (opb_blk_out cx fpos ly4 S4 W4 (ms_mem ms4) md4 kev f SRC_FILE_BLOCK HJ4a Hfrs4 Elay Hin Hfa1 Hfa2
        ltac:(rewrite Hperm4; apply in_or_app; right; left; reflexivity) a
        ltac:(change (req_size SRC_FILE_BLOCK) with 1304; clear - Ha; unfold SRC_FILE_BLOCK in Ha; lia))
        as (Hw1 & Hw2 & Hw3);
      rewrite (HKEEP a Hw3 Hw1); apply UN1; [exact Hw3 | cbv beta; clear - Hw2; lia]
    | destruct (opb_blk_out cx fpos ly4 S4 W4 (ms_mem ms4) md4 kev (o_b cx) (Z.of_nat (length (o_C cx)))
        HJ4a Hfrs4 Elay Hin Hfa1 Hfa2 Hbblk a
        ltac:(pose proof (req_size_pos (Z.of_nat (length (o_C cx))) ltac:(clear; lia)) as (_ & Hrq);
              clear - Ha Hrq; lia)) as (Hw1 & Hw2 & Hw3);
      rewrite (HKEEP a Hw3 Hw1); apply UN1; [exact Hw3 | cbv beta; clear - Hw2; lia]
    | pose proof (opb_src_env_img a Ha) as Hr;
      rewrite (HKEEP a ltac:(apply BDimg; exact Hr) ltac:(apply NWimg; exact Hr));
      apply UN1; [apply BDimg; exact Hr
                 | cbv beta; unfold pcap_img_end, YImgTop.IMG_TOP in Hr;
                   clear - Hr Hgimg Hfa1 Hfa2 Hgnn; lia] ] |];
  rewrite Efs2; apply (mo_le_set_fs_r MT MLAWF); exact Hmo4).
Qed.
(* ---- the empty input: f = NULL at 0x81660 ------------------------------------------------------------------ *)
Theorem op_from_null : op_from SK B K MT FM_RA CTX roimg (op_gi_null SK B K MT).
Proof.
intros cx fpos ly3 S3 W3 ms3 md3 HPRE HG.
unfold op_gi_null in HG. cbv zeta in HG.
destruct HG as (Hpc & HM & Hn0 & Hab & Hnone & Hmo).
unfold op_mid in HM. cbv zeta in HM.
destruct HM as (Hresv & Hsvc & Hrom & Hfrg & Hfcsr & HJ3 & Hkk & Hnev3 & Hfrs3 & Hnin & Hfs3 & M2 & M8 & M9 &
  M18 & M19 & M20 & M21 & M22 & M23 & M24 & M25 & M3 & M4 & M26 & M27 & Hra8 & Hsav & Hhdr0 & Hhdr8 & Hhdr16 &
  Hflagp & Hshlen & Hshb & Hvf & Hv12 & Hv16 & Hv20 & Hkeep8 & HKEPT & Hfds & Hfsm & HMETA3 & HROD3 & Hchain3).
pose proof HPRE as HPRE'. unfold op_pre in HPRE'. cbv zeta in HPRE'.
destruct HPRE' as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hown & Hfa1 & Hfa2 & _ & _ & _ &
  _ & _ & _ & _ & _ & _ & _ & _ & Hnn & _).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _).
pose proof HJ3 as (HAR3 & Hly3 & _).
assert (Elay : forall c p, frame_addr (o_lyc cx) c p = frame_addr ly3 c p)
  by (intros c p; unfold frame_addr; rewrite (opb_lay_F _ _ _ Hly3), (opb_lay_F _ _ _ Hly); reflexivity).
assert (Hincl : forall b m, In (b, m) (ablocks B (o_lyc cx) (o_Sc cx)) -> In (b, m) (ablocks B ly3 S3))
  by (intros b m Hb; rewrite Hab; exact Hb).
assert (Hin : In (o_cid cx, o_pos cx) (frames (o_Sc cx)))
  by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (opb_nwr cx fpos ly3 S3 W3 (ms_mem ms3) md3 (o_k cx + 1) HJ3 Hfrs3 Hnin Elay Hin Hfa1 Hfa2)
  as (NWps & NWimg & BDps & BDimg).
eapply SRr_mono.
{ exact (opb_epi cx fpos ly3 S3 W3 ms3 md3 (o_k cx + 1) (bv_unsigned (getr (ms_regs ms3) 10)) (-1) OP_CUT_NULL
    HPRE (or_introl (conj eq_refl eq_refl)) Hpc Hresv Hsvc Hrom Hfrg Hfcsr HJ3 Hfrs3 M8
    ltac:(symmetry; apply Z_to_bv_bv_unsigned) M18 M21 M22 M3 M4 M26 M27 Hra8 Hsav Hflagp). }
cbv beta. intros W2 c2 _ (S2 & regs2 & mem2 & md2 & -> & -> & HJ2 & HP2 & Ha0 & Hfrs2 & Hab2 & (fs2 & Efs2) &
  Hfd2 & Hfs2 & HKEEP & HPRES).
unfold op_post. cbv zeta. unfold tpcap_source_open_post.
exists ly3, S2, regs2, mem2, md2.
split; [reflexivity|].
split; [exact HP2|].
split; [exact Hfrs2|].
split; [rewrite Hfd2; exact Hfds|].
split; [rewrite Hfs2; exact Hfsm|].
split; [exact (opb_kept_step cx fpos ly3 S3 W3 (ms_mem ms3) mem2 md3 (o_k cx + 1) _ _ _
                 HJ3 Hfrs3 Hnin Elay Hincl HKEPT HKEEP HPRES)|].
split; [rewrite Efs2; eapply mle_weaken;
        [exact MLAW | apply (mo_le_set_fs_r MT MLAWF); exact Hmo
        | unfold OPEN_METER; pose proof (mo_malloc_nonneg MT MLAW SRC_FILE_BLOCK ltac:(clear; cbv; discriminate))
            as Hm0; pose proof (mo_free_nonneg MT MLAW) as Hf0; clear - Hm0 Hf0; lia]|].
assert (KPS : forall a n v, o_ps cx <= a -> a + Z.of_nat n <= o_ps cx + 24 ->
  val_mem SEGS (rdW W3 (ms_mem ms3)) a n v -> val_mem SEGS (rdW W3 mem2) a n v).
{ intros a n v Ha1 Ha2 Hv. eapply opb_vm_frame; [|exact Hv]. intros x Hx. apply (mbyte_of_aview SEGS).
  apply HKEEP; [apply BDps; clear - Ha1 Ha2 Hx; lia | apply NWps; clear - Ha1 Ha2 Hx; lia]. }
split; [exact (KPS (o_ps cx + 12) 4%nat 0 ltac:(clear; lia) ltac:(clear; cbn; lia) Hv12)|].
split; [exact (KPS (o_ps cx + 16) 4%nat 0 ltac:(clear; lia) ltac:(clear; cbn; lia) Hv16)|].
split; [exact (KPS (o_ps cx + 20) 2%nat 0 ltac:(clear; lia) ltac:(clear; cbn; lia) Hv20)|].
right.
split; [eapply ajournal_mono_k; [exact HJ2 | unfold EV_OPEN, EV_FUZZ_FOPEN; clear; lia]|].
split; [exact Ha0|].
split.
{ unfold pcap_goodZ. assert (Hl : length (o_C cx) = 0%nat) by (clear - Hnn Hn0; lia).
  rewrite Hl. reflexivity. }
split; [exact (KPS (o_ps cx) 8%nat 0 ltac:(clear; lia) ltac:(clear; cbn; lia) Hvf)|].
split.
{ intros i Hi. rewrite (HKEEP (o_ps cx + i) ltac:(apply BDps; clear - Hi; lia)
    ltac:(apply NWps; clear - Hi; lia)). exact (Hkeep8 i Hi). }
split; [rewrite Hab2, Hab; apply Permutation_refl|].
apply (opb_asource_none_frame (rdW W3 (ms_mem ms3)) (rdW W3 mem2)); [|exact Hnone].
intros a Ha. apply (mbyte_of_aview SEGS).
pose proof (opb_src_env_img a Ha) as Hr.
apply HKEEP; [apply BDimg; exact Hr | apply NWimg; exact Hr].
Qed.

(* ---- the cut after fread: 0x815fc ------------------------------------------------------------------------- *)
Theorem op_from_read : op_from SK B K MT FM_RA CTX roimg (op_gi_read SK B K MT).
Proof.
intros cx fpos ly3 S3 W3 ms3 md3 HPRE HG.
unfold op_gi_read in HG. cbv zeta in HG.
destruct HG as (f & kr & Hpc & HM & Hn1 & Hf4096 & Hf16 & Hab & M10 & Hkr & Hgarr & HSRC & HFPinc & Hmo).
unfold op_mid in HM. cbv zeta in HM.
destruct HM as (Hresv & Hsvc & Hrom & Hfrg & Hfcsr & HJ3 & Hkk & Hnev3 & Hfrs3 & Hnin & Hfs3 & M2 & M8 & M9 &
  M18 & M19 & M20 & M21 & M22 & M23 & M24 & M25 & M3 & M4 & M26 & M27 & Hra8 & Hsav & Hhdr0 & Hhdr8 & Hhdr16 &
  Hflagp & Hshlen & Hshb & Hvf & Hv12 & Hv16 & Hv20 & Hkeep8 & HKEPT & Hfds & Hfsm & HMETA3 & HROD3 & Hchain3).
pose proof HPRE as HPRE'. unfold op_pre in HPRE'. cbv zeta in HPRE'.
destruct HPRE' as (HJ & HROD & Hraw & Hra4 & Hgp & Htp & _ & _ & Hch & Hctx & Hal16 & Hwlo & Hwhi & Htop32 &
  Hnfr & Hown & Hfa1 & Hfa2 & Hps0 & Hps8 & Hshp & HFP0 & HRO & _ & _ & HVn & HVb & Hb64 & HNONE & Hnn & HnC &
  Hinput & HMETA & Hev & Hlive & MOK & HU0 & HUC).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : TPCAP_SOURCE_OPEN_STK = 18736) by reflexivity.
assert (HFS : PFCLOSE_STK = 16528) by reflexivity.
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof HJ3 as (HAR3 & Hly3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & _).
assert (Elay : forall c p, frame_addr (o_lyc cx) c p = frame_addr ly3 c p)
  by (intros c p; unfold frame_addr; rewrite (opb_lay_F _ _ _ Hly3), (opb_lay_F _ _ _ Hly); reflexivity).
assert (Hin : In (o_cid cx, o_pos cx) (frames (o_Sc cx)))
  by (rewrite Hfrs; apply in_or_app; left; exact Hown).
assert (Hinfr : forall c p, In (c, p) (frames (o_Sc cx)) -> In (c, p) (frames S3))
  by (intros c p Hc; rewrite Hfrs3; right; exact Hc).
assert (Hin3 : In (o_cid cx, o_pos cx) (frames S3)) by (apply Hinfr; exact Hin).
assert (HinF : In (OP_CID, fpos) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
assert (Hincl : forall b m, In (b, m) (ablocks B (o_lyc cx) (o_Sc cx)) -> In (b, m) (ablocks B ly3 S3))
  by (intros b m Hb; rewrite Hab; apply in_or_app; left; exact Hb).
assert (Hfin : In (f, SRC_FILE_BLOCK) (ablocks B ly3 S3))
  by (rewrite Hab; apply in_or_app; right; left; reflexivity).
assert (Hfresh : ~ In (f, SRC_FILE_BLOCK) (ablocks B (o_lyc cx) (o_Sc cx))).
{ intros Hc. apply in_split in Hc as (l1 & l2 & El).
  pose proof (sep_blocks_pos SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 (f, SRC_FILE_BLOCK) (f, SRC_FILE_BLOCK)
    l1 l2 [] HAR3 ltac:(rewrite Hab, El, <- app_assoc; reflexivity)) as Hd.
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd.
  change (req_size SRC_FILE_BLOCK) with 1304 in Hd. clear - Hd. lia. }
destruct (opb_nwr cx fpos ly3 S3 W3 (ms_mem ms3) md3 (o_k cx + 1) HJ3 Hfrs3 Hnin Elay Hin Hfa1 Hfa2)
  as (NWps & NWimg & BDps & BDimg).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 OP_CID fpos HAR3 HinF)
  as (HF4096 & HFceil & HFapp).
assert (EF : frame_addr ly3 OP_CID fpos = oF cx fpos) by (unfold oF; symmetry; apply (Elay OP_CID fpos)).
rewrite EF in HF4096, HFceil, HFapp.
change (fs_frame_bytes OP_CID) with 128 in HF4096, HFceil, HFapp.
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 (o_cid cx) (o_pos cx) HAR3 Hin3)
  as (Hg4096 & Hgceil & Hgapp).
rewrite <- (Elay (o_cid cx) (o_pos cx)) in Hg4096, Hgceil, Hgapp.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hgapp.
pose proof (fs_frame_bytes_nonneg (o_cid cx)) as Hgnn.
assert (Hpsb : 4096 <= o_ps cx /\ o_ps cx + 24 <= 140737479966720)
  by (clear - Hfa1 Hfa2 Hg4096 Hgceil C1; lia).
assert (Hsplo : alloc_ceiling + TPCAP_SOURCE_OPEN_STK <= spZ (o_regs cx))
  by (clear - Hceil Hslo Hwlo Hwhi; lia).
assert (Hspr : 0 <= spZ (o_regs cx) < 2 ^ 64) by (unfold spZ; clear; apply u64_range).
assert (Hsphi : spZ (o_regs cx) <= 2 ^ 47) by (clear - Hwhi Hshi H47; lia).
pose proof (frame_al64 SEGS B ly3 S3 W3 (ms_mem ms3) md3 OP_CID fpos HAR3 HinF) as (HFal & _ & _).
rewrite EF in HFal.
assert (HSHm8 : oSH cx fpos mod 8 = 0).
{ destruct (opb_div8_mul64 _ HFal) as (HD & _). unfold oSH, SHADOW_OFF. rewrite HD.
  clear. replace (2147450880 + 8 * (oF cx fpos / 64)) with ((268431360 + oF cx fpos / 64) * 8) by lia.
  apply Z_mod_mult. }
destruct (opb_sp1_facts (spZ (o_regs cx)) ltac:(clear - Hspr; lia) Hal16) as (Hsp1r & Hsp1m32 & Hsp1m16).
assert (Hosp1 : osp1 cx = 32 * ((spZ (o_regs cx) - 96) / 32)) by (unfold osp1, OPEN_FRAME; reflexivity).
rewrite <- Hosp1 in Hsp1r, Hsp1m32, Hsp1m16.
assert (HSHb : OPB_SB <= oSH cx fpos /\ oSH cx fpos + 16 <= OPB_SB + 2 ^ 44).
{ assert (Hd0 : 0 <= oF cx fpos / 8) by (apply Z.div_pos; clear - HF4096; lia).
  assert (Hd1 : oF cx fpos / 8 < 2 ^ 44 - 16) by (apply Z.div_lt_upper_bound; clear - HFceil C1; lia).
  unfold oSH, OPB_SB, SHADOW_OFF. clear - Hd0 Hd1. lia. }
assert (HFlt : 0 <= oF cx fpos < 2 ^ 64) by (clear - HF4096 HFceil C1; lia).
assert (HSHlt : 0 <= oSH cx fpos < 2 ^ 64) by (unfold OPB_SB in HSHb; clear - HSHb; lia).
assert (Hf64 : 0 <= f < 2 ^ 64).
{ destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 f SRC_FILE_BLOCK HAR3 Hfin)
    as (_ & Hq1 & Hq2 & _ & _ & _). change (req_size SRC_FILE_BLOCK) with 1304 in Hq2.
  clear - Hq1 Hq2 C1. lia. }
(* the shadow of ps at the cut *)
assert (Hsh3 : range_addressable (aview SEGS (w_H W3) (ms_mem ms3)) SHADOW_OFF (o_ps cx) 24).
{ apply (ra_frame (aview SEGS (w_H (o_W cx)) (o_memc cx))); [exact Hshp|].
  intros x Hx. unfold shadow_of_addr.
  destruct HKEPT as (_ & _ & _ & T4 & _).
  pose proof (frame_al64 SEGS B (o_lyc cx) (o_Sc cx) (o_W cx) (o_memc cx) (o_mdc cx) (o_cid cx) (o_pos cx)
    HAR Hin) as (Hga & Hgb & _).
  destruct (opb_div8_mul64 _ Hga) as (Hd1 & He1). destruct (opb_div8_mul64 _ Hgb) as (Hd2 & He2).
  assert (Hlo : frame_addr (o_lyc cx) (o_cid cx) (o_pos cx) / 8 <= x / 8)
    by (apply Z.div_le_mono; [clear; lia | clear - Hx Hfa1; lia]).
  assert (Hhi : x / 8 < frame_addr (o_lyc cx) (o_cid cx) (o_pos cx) / 8 + fs_frame_bytes (o_cid cx) / 8)
    by (apply Z.div_lt_upper_bound; [clear; lia | rewrite Hd1, Hd2; clear - Hx Hfa2 He1 He2; lia]).
  assert (Hx44 : x / 8 < 2 ^ 44)
    by (apply Z.div_lt_upper_bound; [clear; lia | clear - Hx Hfa2 Hgceil C1; lia]).
  assert (Hx0 : 0 <= x / 8) by (apply Z.div_pos; [clear - Hx Hpsb; lia | clear; lia]).
  apply (T4 (o_cid cx) (o_pos cx) (SHADOW_OFF + x / 8) Hin).
  - right. unfold in_zr, shadow_addr. cbn [fst snd]. unfold SHADOW_OFF. clear - Hlo Hhi. lia.
  - cbn beta. unfold SHADOW_OFF. clear - Hx44 Hx0 Hpsb Hgapp Hfa1 Hfa2 Hgnn. lia. }
(* the environment and the symbolic state at the cut *)
set (E := Eimg (Ereg (ms_regs ms3) (opb_extra cx fpos f))).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms3) (opb_extra cx fpos f)) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (EREG : forall n (r : Prelude.reg), Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r).
{ intros n r Hr. rewrite EL; [exact (ew_Ereg_nat _ _ n r Hr)|].
  pose proof (u5_range r) as Hu. unfold A_TEXT. clear - Hr Hu. lia. }
assert (EX : forall j, (j < 13)%nat -> ew E (32 + j) = nth j (opb_extra cx fpos f) (w64 0))
  by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ j)).
assert (E22 : ew E 22 = w64 (oF cx fpos)) by (rewrite (EREG 22%nat 22%bv eq_refl); exact M22).
assert (E21 : ew E 21 = w64 (oSH cx fpos)) by (rewrite (EREG 21%nat 21%bv eq_refl); exact M21).
assert (E19 : ew E 19 = w64 (o_ps cx)) by (rewrite (EREG 19%nat 19%bv eq_refl); exact M19).
assert (E23 : ew E 23 = w64 SHADOW_OFF) by (rewrite (EREG 23%nat 23%bv eq_refl); exact M23).
assert (E24 : ew E 24 = w64 (SHADOW_OFF + o_ps cx / 8)) by (rewrite (EREG 24%nat 24%bv eq_refl); exact M24).
assert (E8 : ew E 8 = w64 (spZ (o_regs cx))) by (rewrite (EREG 8%nat 8%bv eq_refl); exact M8).
assert (E2 : ew E 2 = w64 (osp1 cx)) by (rewrite (EREG 2%nat 2%bv eq_refl); exact M2).
assert (E10 : ew E 10 = w64 kr) by (rewrite (EREG 10%nat 10%bv eq_refl); exact M10).
assert (E43 : ew E 43 = w64 f) by (exact (EX 11%nat ltac:(lia))).
assert (E44 : ew E 44 = w64 (oFL cx fpos)) by (exact (EX 12%nat ltac:(lia))).
assert (U22 : bv_unsigned (ew E 22) = oF cx fpos) by (rewrite E22; apply unsigned_lit_small; clear - HFlt; lia).
assert (U21 : bv_unsigned (ew E 21) = oSH cx fpos) by (rewrite E21; apply unsigned_lit_small; clear - HSHlt; lia).
assert (U19 : bv_unsigned (ew E 19) = o_ps cx) by (rewrite E19; apply unsigned_lit_small; clear - Hpsb; lia).
assert (U23 : bv_unsigned (ew E 23) = SHADOW_OFF)
  by (rewrite E23; apply unsigned_lit_small; unfold SHADOW_OFF; clear; lia).
assert (U8 : bv_unsigned (ew E 8) = spZ (o_regs cx)) by (rewrite E8; apply unsigned_lit_small; clear - Hspr; lia).
assert (U2 : bv_unsigned (ew E 2) = osp1 cx)
  by (rewrite E2; apply unsigned_lit_small; clear - Hsp1r Hspr Hsplo C1 HTS; lia).
assert (U10 : bv_unsigned (ew E 10) = kr)
  by (rewrite E10; apply unsigned_lit_small; rewrite Hkr; clear - Hnn HnC; lia).
assert (U43 : bv_unsigned (ew E 43) = f) by (rewrite E43; apply unsigned_lit_small; clear - Hf64; lia).
assert (HSAV : forall j, (j < 11)%nat ->
  val_mem SEGS (rdW W3 (ms_mem ms3)) (spZ (o_regs cx) + (-8 - 8 * Z.of_nat j)) 8
    (bv_unsigned (nth j (opb_extra cx fpos f) (w64 0)))).
{ intros j Hj. apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)).
  destruct j as [|j'];
  [ replace (spZ (o_regs cx) + (-8 - 8 * Z.of_nat 0)) with (spZ (o_regs cx) - 8) by (clear; lia);
    cbn [nth opb_extra]; exact Hra8 |].
  replace (spZ (o_regs cx) + (-8 - 8 * Z.of_nat (S j'))) with (spZ (o_regs cx) - 16 - 8 * Z.of_nat j')
    by (clear; lia).
  rewrite (Hsav (Z.of_nat j') ltac:(clear - Hj; lia)). f_equal.
  do 10 (destruct j' as [|j']; [cbn [nth opb_extra Z.ltb Z.compare]; reflexivity|]).
  cbn [length] in Hj. clear - Hj. lia. }
assert (HCH : forall j, (j < 11)%nat -> YP09.chunk_ok SEGS E (rdW W3 (ms_mem ms3)) (spZ (o_regs cx))
   (YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (32 + j) 0)))).
{ intros j Hj.
  apply (chunk_ok_val SEGS E _ (spZ (o_regs cx)) (-8 - 8 * Z.of_nat j) 8 (SOff (32 + j) 0)
    (bv_unsigned (nth j (opb_extra cx fpos f) (w64 0))));
  [ cbn [sv_denot]; rewrite (EX j ltac:(clear - Hj; lia)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | pose proof (u64_range (nth j (opb_extra cx fpos f) (w64 0))) as Hu;
    change (8 * Z.of_N 8) with 64; clear - Hu; lia
  | zside
  | exact (HSAV j Hj) ]. }
assert (HPSpres : forall o, 0 <= o < 24 -> apresent (w_H W3) (ms_mem ms3) (o_ps cx + o)).
{ intros o Ho. refine (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (o_ps cx + o) HJ3 _)).
  right. right. right. exists (o_cid cx), (o_pos cx). split; [right; exact Hown|]. left.
  unfold in_zr. cbn [fst snd]. rewrite <- (Elay (o_cid cx) (o_pos cx)).
  clear - Hfa1 Hfa2 Ho. lia. }
assert (HS : st_ok_pi SEGS VAL E (opb_ss OP_CUT_READ opb_sr_read opb_rs_ro opb_facts) (restrict (w_H W3) ms3)).
{ assert (HS0 : st_ok_pi SEGS VAL E (opb_ss OP_CUT_READ sr_atoms opb_rs_ro opb_facts) (restrict (w_H W3) ms3)).
  { rewrite (opb_ms_eta ms3 Hfrg Hsvc Hresv Hfcsr), Hpc, Hrom, restrict_mkst_fx.
    unfold opb_ss, opb_rs_ro, opb_facts. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
      unfold region_ok, opb_stack, opb_ps_ro;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      + rewrite U8. split; [clear - Hsplo C1 HTS; lia|]. split; [clear - Hspr; lia|].
        split; [intros o Ho; clear - Ho; lia|].
        unfold opb_stack_chunks. apply Forall_map, Forall_forall. intros j Hj.
        apply in_seq in Hj. apply HCH. clear - Hj. lia.
      + rewrite U19. split; [clear - Hpsb; lia|]. split; [clear - Hpsb; lia|].
        split; [intros o Ho; clear - Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS E _ (o_ps cx) 0 8 (SOff 43 0) f);
        [ cbn [sv_denot]; rewrite E43, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (8 * Z.of_N 8) with 64; clear - Hf64; lia | zside | rewrite Z.add_0_r; exact Hvf ].
    - apply pairwise_disjoint_of_extents.
      unfold opb_rs_ro, opb_stack, opb_ps_ro, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U8, U19.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      clear - Hsplo C1 HTS Hpsb Hgceil Hfa2 Hfa1. repeat split; lia.
    - split; [|split; [exact I | exact I]].
      cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      repeat split; rewrite ?U2, ?U8, ?U19, ?U21, ?U22, ?U23;
      try exact I;
      try (change (2 ^ 6) with 64); try (change (2 ^ 5) with 32); try (change (2 ^ 4) with 16);
      try (change (2 ^ 3) with 8); try (change (2 ^ 0) with 1);
      first [ exact Hsp1m32 | exact Hal16 | exact Hps8 | exact HSHm8 | exact HFal | apply Z.mod_1_r
            | unfold OPB_SB, SHADOW_OFF; clear; lia
            | clear - Hsp1r Hsplo Hshi Hwhi H47 Htop Htop2 C1 HTS Hpsb HSHb HFlt HF4096 HFceil Hspr; lia ]. }
  unfold opb_sr_read, opb_sr, opb_sr_epi.
  refine (ast_ok_pi_set_reg_fp E _ _ (25%bv : bv 5) (SLit 24)
    (ast_ok_pi_set_reg_fp E _ _ (20%bv : bv 5) (SOff 22 32)
      (ast_ok_pi_set_reg_fp E _ _ (24%bv : bv 5) opb_sh8
        (ast_ok_pi_set_reg_fp E _ _ (18%bv : bv 5) (SOff 22 0) HS0 ltac:(vm_compute; reflexivity) _)
        ltac:(vm_compute; reflexivity) _)
      ltac:(vm_compute; reflexivity) _)
    ltac:(vm_compute; reflexivity) _).
  - cbn [ms_regs restrict mkst]. cbn [sv_denot]. rewrite U22, Z.add_0_r. exact (eq_sym M18).
  - cbn [ms_regs restrict mkst]. unfold opb_sh8.
    rewrite (shadow_decl_ok E 19%nat 23%nat 24%nat (o_ps cx) SHADOW_OFF E19 ltac:(clear - Hpsb; lia) E23 E24).
    cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E24. exact (eq_sym M24).
  - cbn [ms_regs restrict mkst]. cbn [sv_denot]. rewrite U22. exact (eq_sym M20).
  - cbn [ms_regs restrict mkst]. cbn [sv_denot]. exact (eq_sym M25). }
assert (SHOK : sh_ok SEGS OPB_Bx OPB_SH E (rdW W3 (ms_mem ms3))).
{ unfold sh_ok, OPB_SH, OPB_Bx. apply Forall_cons; [|apply Forall_nil].
  unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
  rewrite (U_atom E 23%nat SHADOW_OFF E23 ltac:(unfold SHADOW_OFF; clear; lia)).
  rewrite (U_atom E 19%nat (o_ps cx) E19 ltac:(clear - Hpsb; lia)).
  split.
  - rewrite Z.add_0_r. rewrite <- (aview_rd_of SEGS). exact Hsh3.
  - intros a Ha. cbn [Z.min Z.max] in Ha. unfold SHADOW_OFF.
    clear - Ha Hgapp Hfa1 Hfa2 Hgnn. lia. }
assert (Hbinblk : In (o_b cx, Z.of_nat (length (o_C cx))) (ablocks B ly3 S3)).
{ apply Hincl. rewrite <- Hnn. exact (proj1 (Hinput ltac:(clear - Hn1; lia))). }
assert (HPf : Permutation (ablocks B ly3 S3) ((f, SRC_FILE_BLOCK) :: ablocks B (o_lyc cx) (o_Sc cx)))
  by (rewrite Hab; apply Permutation_sym; apply Permutation_cons_append).
assert (HEVf : st_nev S3 + 2 <= EV_MAX) by (unfold EV_OPEN, EV_FUZZ_FOPEN in Hev; clear - Hnev3 Hev; lia).
(* 0x815fc `bne a0,s9`: the short read *)
psrr_branch_tok RUN BR HS SHOK OPB_span.
- (* kr <> 24: the short read closes the stream *)
  rewrite branch_ne_U, (U_atom E 10%nat kr E10 ltac:(rewrite Hkr; clear - Hnn HnC; lia)),
    (U_lit E 24 ltac:(clear; lia)) in Hc.
  apply Bool.negb_true_iff, Z.eqb_neq in Hc.
  assert (Hgood : pcap_goodZ (o_C cx) = false).
  { unfold pcap_goodZ. assert (Hlt : Z.of_nat (length (o_C cx)) < 24)
      by (rewrite Hkr in Hc; clear - Hc Hnn; lia).
    destruct (Z.leb_spec 24 (Z.of_nat (length (o_C cx)))) as [Hq|Hq];
    [exfalso; clear - Hlt Hq; lia | reflexivity]. }
  (* 0x81668..0x81674: the shadow check of ps, ps->f reloaded, the fclose wrapper *)
  paj_run_tok RUN HS HJ3 SHOK OPB_span;
    [ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?ownx =>
        let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx ownx) end;
      apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; clear; lia|];
      apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; clear; lia|];
      apply awr_ok_nil |].
  assert (Hmm : ms_mem ms = ms_mem ms3).
  { apply (opb_frame_nil E (ss_mem (opb_ss OP_CUT_READ opb_sr_read opb_rs_ro opb_facts)));
    [ intros r Hr0; cbn [opb_ss ss_mem opb_rs_ro In] in Hr0;
      destruct Hr0 as [<- | [<- | []]]; cbn; clear; lia
    | exact HF ]. }
  assert (Hvf' : val_mem SEGS (rdW W3 (ms_mem ms)) (o_ps cx) 8 f) by (rewrite Hmm; exact Hvf).
  assert (Hv12' : val_mem SEGS (rdW W3 (ms_mem ms)) (o_ps cx + 12) 4 0) by (rewrite Hmm; exact Hv12).
  assert (Hv16' : val_mem SEGS (rdW W3 (ms_mem ms)) (o_ps cx + 16) 4 0) by (rewrite Hmm; exact Hv16).
  assert (Hv20' : val_mem SEGS (rdW W3 (ms_mem ms)) (o_ps cx + 20) 2 0) by (rewrite Hmm; exact Hv20).
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
  prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
  prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (21%bv : bv 5) Q21.
  prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
  prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
  assert (Q24s : getr (ms_regs ms) 24 = w64 (SHADOW_OFF + o_ps cx / 8)).
  { pose proof (st_ok_restrict_reg SEGS (w_H W3) E _ ms (24%bv : bv 5) HS) as Q24r.
    cbn [ms_regs restrict mkst] in Q24r.
    lazymatch type of Q24r with getr _ _ = sv_denot _ ?e =>
      let e' := eval vm_compute in e in change e with e' in Q24r end.
    rewrite (shadow_decl_ok E 19%nat 23%nat 24%nat (o_ps cx) SHADOW_OFF E19 ltac:(clear - Hpsb; lia) E23 E24)
      in Q24r.
    cbn [sv_denot] in Q24r. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E24 in Q24r. exact Q24r. }
  assert (Hspc : spZ (ms_regs ms) = o_sp0 cx + (osp1 cx - o_sp0 cx)).
  { unfold spZ. rewrite Q2, E2. unfold w64.
    rewrite unsigned_lit_small by (clear - Hsp1r Hspr Hsplo C1 HTS; lia). clear; lia. }
  eapply SRr_bind.
  { eapply (cl_callS B LAWS W3 (ms_regs ms) (ms_mem ms) _ (o_STK cx) (o_sp0 cx) (o_FP cx) (o_ly cx) (o_S cx)
      (o_W0 cx) (o_mem0 cx) (o_md0 cx) ((OP_CID, fpos) :: o_own cx) ly3 S3 _ (o_k cx + 1)
      PFCLOSE_STK (asource_fp f) 2 (osp1 cx - o_sp0 cx) (Z_to_bv 64 (BASE + OPB_RET1))
      ((spZ (o_regs cx), raZ (o_regs cx), s0Z (o_regs cx)) :: o_ch cx)
      (fun ly5 S5 W5 regs5 mem5 md5 =>
         getr regs5 10 = Z_to_bv 64 0 /\ Permutation (ablocks B ly5 S5) (ablocks B (o_lyc cx) (o_Sc cx)) /\
         frames S5 = frames S3 /\ asource_none SEGS K (rdW W5 mem5) /\
         m_fds md5 = m_fds md3 /\ m_fs md5 = m_fs md3) HJ3 Hspc).
    - rewrite Zminus_mod, Hsp1m16, Hsp0al. reflexivity.
    - clear - Hsp1r Hwhi. lia.
    - unfold PFCLOSE_STK. clear; lia.
    - rewrite HFS. clear - Hsp1r Hwlo Hwhi HTS. lia.
    - rewrite Q3, (EREG 3%nat 3%bv eq_refl), M3. exact Hgp.
    - rewrite Q4, (EREG 4%nat 4%bv eq_refl), M4. exact Htp.
    - exact Q1.
    - apply ret_ok_codeptr_v; [unfold OPB_RET1; clear; lia | reflexivity].
    - rewrite unsigned_lit_small by (pose proof (pa_base_lo (PL := PL_pcap) (PI := PI));
        pose proof pa_B_ok as (HB0 & HB1 & _); unfold OPB_RET1; clear - HB0 HB1; lia).
      pose proof (pa_base_lo (PL := PL_pcap) (PI := PI)). unfold OPB_RET1. clear - H. lia.
    - replace (o_sp0 cx + (osp1 cx - o_sp0 cx)) with (osp1 cx) by (clear; lia).
      unfold s0Z. rewrite Q8, E8. unfold w64. rewrite unsigned_lit_small by (clear - Hspr; lia).
      rewrite Hmm. exact Hchain3.
    - intros HPRE1. eapply SRr_mono.
      + eapply (AFCLOSE W3 ly3 S3 (ms_regs ms) (ms_mem ms) _ _ f (o_b cx) (o_M cx) (o_C cx) kr
          (ablocks B (o_lyc cx) (o_Sc cx)) HPRE1).
        * rewrite Q10, E43. reflexivity.
        * exact HPf.
        * rewrite Hmm. exact HSRC.
        * exact Hbinblk.
        * rewrite Hmm. exact HMETA3.
        * rewrite Hmm. intros a Ha Ho He. exact (HROD3 a Ha Ho He).
        * exact HEVf.
        * exact HUfc1.
        * exact HUfc2.
      + cbv beta. intros W5 c5 _ (ly5 & S5 & regs5 & mem5 & md5 & -> & HJc5 & HP5 & Ha05 & HPm5 & Hfrs5 &
          HSN5 & HGB5 & HFD5 & HFS5).
        exists ly5, S5, regs5, mem5, md5. split; [rewrite Q1; reflexivity|].
        split; [exact HJc5|]. split; [exact HP5|].
        split; [exact Ha05|]. split; [exact HPm5|]. split; [exact Hfrs5|]. split; [exact HSN5|].
        split; [rewrite HFD5; repeat rewrite (proj1 (opb_wvb_fds_fs _ _ _)); reflexivity
               | rewrite HFS5; repeat rewrite (proj2 (opb_wvb_fds_fs _ _ _)); reflexivity].
    - exact HFPinc. }
  cbv beta. intros W5 c5 _ (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ5 & HJc5 & HP5 & Ha05 & HPm5 & Hfrs5 &
    HSN5 & HFD5 & HFS5).
  replace (o_sp0 cx + (osp1 cx - o_sp0 cx)) with (osp1 cx) in HJc5 by (clear; lia).
  pose proof HJc5 as (HAR5 & _ & _ & _ & _ & _ & _ & _ & G1 & _ & _ & G4 & _).
  assert (Hfdisj : forall a, o_ps cx <= a < o_ps cx + 24 -> ~ inFP (asource_fp f) a).
  { intros a Ha Hcf.
    pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 f SRC_FILE_BLOCK
      (o_cid cx) (o_pos cx) HAR3 Hfin Hin3) as Dfg.
    unfold zdisjoint in Dfg. cbn [fst snd] in Dfg. change (req_size SRC_FILE_BLOCK) with 1304 in Dfg.
    rewrite <- (Elay (o_cid cx) (o_pos cx)) in Dfg.
    destruct (in_asource_fp f a Hcf) as [Hq | Hq]; unfold SRC_FILE_BLOCK in Hq;
    [clear - Hq Ha Dfg Hfa1 Hfa2 | clear - Hq Ha Hpsb]; lia. }
  assert (KPS5 : forall a, o_ps cx <= a < o_ps cx + 24 ->
            aview SEGS (w_H W5) mem5 a = aview SEGS (w_H W3) (ms_mem ms) a).
  { intros a Ha. apply (G4 (o_cid cx) (o_pos cx) a Hin3); [|exact (Hfdisj a Ha)].
    left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite <- (Elay (o_cid cx) (o_pos cx)).
    clear - Ha Hfa1 Hfa2. lia. }
  assert (KST5 : forall a, spZ (o_regs cx) - 96 <= a < spZ (o_regs cx) ->
            aview SEGS (w_H W5) mem5 a = aview SEGS (w_H W3) (ms_mem ms) a)
    by (intros a Ha; apply G1; [clear - Ha Hsplo C1 HTS Hspr; lia | clear - Ha Hsp1r HFS; lia]).
  assert (KFL5 : forall a, oF cx fpos <= a < oF cx fpos + 128 ->
            aview SEGS (w_H W5) mem5 a = aview SEGS (w_H W3) (ms_mem ms) a).
  { intros a Ha. apply (G4 OP_CID fpos a HinF).
    - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF.
      change (fs_frame_bytes OP_CID) with 128. clear - Ha. lia.
    - intros Hcf.
      pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 f SRC_FILE_BLOCK OP_CID fpos
        HAR3 Hfin HinF) as DfF.
      unfold zdisjoint in DfF. cbn [fst snd] in DfF. change (req_size SRC_FILE_BLOCK) with 1304 in DfF.
      rewrite EF in DfF. change (fs_frame_bytes OP_CID) with 128 in DfF.
      destruct (in_asource_fp f a Hcf) as [Hq | Hq]; unfold SRC_FILE_BLOCK in Hq;
      [clear - Hq Ha DfF | clear - Hq Ha HF4096]; lia. }
  assert (HR5 : forall (r : Prelude.reg), acallee_saved (bv_unsigned r) ->
            getr regs5 r = getr (ms_regs ms) r)
    by (intros r Hr; pose proof (HP5 (bv_unsigned r) Hr) as Hq; rewrite !Z_to_bv_bv_unsigned in Hq;
        exact Hq).
  eapply (opb_refuse_tail cx fpos ly5 S5 W5
    (mkst regs5 (Z_to_bv 64 (BASE + OPB_RET1)) mem5 (seg_rom SEGS)) md5 (o_k cx + 1 + 2) OPB_RET1 f
    HPRE (or_introl eq_refl) eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl).
  + exact HJ5.
  + unfold EV_OPEN, EV_FUZZ_FOPEN. clear; lia.
  + rewrite Hfrs5. exact Hfrs3.
  + exact Hnin.
  + exact HPm5.
  + intros b0 m0 Hb0. apply (Permutation_in _ (Permutation_sym HPm5)). exact Hb0.
  + unfold OPEN_METER.
    exact (mle_station MT _ _ _ _ _ MLAW Hmo (asfm_close SK SEGS B MT FM _ _ _ _ _ _ _ _ _ _ _ _ _ _
             f (ablocks B (o_lyc cx) (o_Sc cx)) HJc5 HPf HPm5)).
  + cbn [ms_regs mkst]. rewrite (HR5 2%bv ltac:(clear; unfold acallee_saved; change (bv_unsigned 2%bv) with 2; lia)), Q2, E2. reflexivity.
  + cbn [ms_regs mkst]. rewrite (HR5 8%bv ltac:(clear; unfold acallee_saved; change (bv_unsigned 8%bv) with 8; lia)), Q8, E8. reflexivity.
  + cbn [ms_regs mkst]. rewrite (HR5 18%bv ltac:(clear; unfold acallee_saved; change (bv_unsigned 18%bv) with 18; lia)), Q18, E22. reflexivity.
  + cbn [ms_regs mkst]. rewrite (HR5 19%bv ltac:(clear; unfold acallee_saved; change (bv_unsigned 19%bv) with 19; lia)), Q19, E19. reflexivity.
  + cbn [ms_regs mkst]. rewrite (HR5 21%bv ltac:(clear; unfold acallee_saved; change (bv_unsigned 21%bv) with 21; lia)), Q21, E21. reflexivity.
  + cbn [ms_regs mkst]. rewrite (HR5 22%bv ltac:(clear; unfold acallee_saved; change (bv_unsigned 22%bv) with 22; lia)), Q22, E22. reflexivity.
  + cbn [ms_regs mkst]. rewrite (HR5 23%bv ltac:(clear; unfold acallee_saved; change (bv_unsigned 23%bv) with 23; lia)), Q23, E23. reflexivity.
  + cbn [ms_regs mkst].
    rewrite (HR5 24%bv ltac:(clear; unfold acallee_saved; change (bv_unsigned 24%bv) with 24; lia)).
    exact Q24s.
  + cbn [ms_regs mkst]. rewrite (HR5 3%bv ltac:(clear; unfold acallee_saved; change (bv_unsigned 3%bv) with 3; lia)), Q3,
      (EREG 3%nat 3%bv eq_refl). exact M3.
  + cbn [ms_regs mkst]. rewrite (HR5 4%bv ltac:(clear; unfold acallee_saved; change (bv_unsigned 4%bv) with 4; lia)), Q4,
      (EREG 4%nat 4%bv eq_refl). exact M4.
  + cbn [ms_regs mkst]. rewrite (HR5 26%bv ltac:(clear; unfold acallee_saved; change (bv_unsigned 26%bv) with 26; lia)), Q26,
      (EREG 26%nat 26%bv eq_refl). exact M26.
  + cbn [ms_regs mkst]. rewrite (HR5 27%bv ltac:(clear; unfold acallee_saved; change (bv_unsigned 27%bv) with 27; lia)), Q27,
      (EREG 27%nat 27%bv eq_refl). exact M27.
  + cbn [ms_mem mkst]. rewrite (opb_rdword_ext (aview SEGS (w_H W3) (ms_mem ms))
      (aview SEGS (w_H W5) mem5) (spZ (o_regs cx) - 8)
      ltac:(intros i Hi; apply KST5; clear - Hi; lia)), Hmm. exact Hra8.
  + cbn [ms_mem mkst]. intros j Hj.
    rewrite (opb_rdword_ext (aview SEGS (w_H W3) (ms_mem ms)) (aview SEGS (w_H W5) mem5)
      (spZ (o_regs cx) - 16 - 8 * j) ltac:(intros i Hi; apply KST5; clear - Hi Hj; lia)), Hmm.
    exact (Hsav j Hj).
  + cbn [ms_mem mkst]. rewrite (opb_rdword_ext (aview SEGS (w_H W3) (ms_mem ms))
      (aview SEGS (w_H W5) mem5) (oF cx fpos + OP_FLAGPTR)
      ltac:(intros i Hi; apply KFL5; unfold OP_FLAGPTR; clear - Hi; lia)), Hmm. exact Hflagp.
  + cbn [ms_mem mkst]. apply (ra_frame (aview SEGS (w_H W3) (ms_mem ms3))); [exact Hsh3|].
    intros x Hx. unfold shadow_of_addr. rewrite <- Hmm.
    apply (G4 (o_cid cx) (o_pos cx) (SHADOW_OFF + x / 8) Hin3).
    * right. unfold in_zr. cbn [fst snd]. rewrite <- (Elay (o_cid cx) (o_pos cx)).
      pose proof (frame_al64 SEGS B (o_lyc cx) (o_Sc cx) (o_W cx) (o_memc cx) (o_mdc cx) (o_cid cx) (o_pos cx)
        HAR Hin) as (Hga & Hgb & _).
      destruct (opb_div8_mul64 _ Hga) as (Hd1 & He1). destruct (opb_div8_mul64 _ Hgb) as (Hd2 & He2).
      assert (Hlo : frame_addr (o_lyc cx) (o_cid cx) (o_pos cx) / 8 <= x / 8)
        by (apply Z.div_le_mono; [clear; lia | clear - Hx Hfa1; lia]).
      assert (Hhi : x / 8 < frame_addr (o_lyc cx) (o_cid cx) (o_pos cx) / 8 + fs_frame_bytes (o_cid cx) / 8)
        by (apply Z.div_lt_upper_bound; [clear; lia | rewrite Hd1, Hd2; clear - Hx Hfa2 He1 He2; lia]).
      unfold shadow_addr, SHADOW_OFF. clear - Hlo Hhi. lia.
    * intros Hcf.
      assert (Hx44 : x / 8 < 2 ^ 44)
        by (apply Z.div_lt_upper_bound; [clear; lia | clear - Hx Hfa2 Hgceil C1; lia]).
      assert (Hx0 : 0 <= x / 8) by (apply Z.div_pos; [clear - Hx Hpsb; lia | clear; lia]).
      destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 f SRC_FILE_BLOCK HAR3 Hfin)
        as (_ & Hq1 & Hq2 & Hq3 & _ & _).
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hq3.
      change (req_size SRC_FILE_BLOCK) with 1304 in Hq2, Hq3.
      destruct (in_asource_fp f (SHADOW_OFF + x / 8) Hcf) as [Hq | Hq]; unfold SRC_FILE_BLOCK in Hq;
      unfold SHADOW_OFF in Hq; clear - Hq Hx44 Hx0 Hq1 Hq2 Hq3; lia.
  + cbn [ms_mem mkst]. eapply opb_vm_frame; [|exact Hvf'].
    intros x Hx. apply (mbyte_of_aview SEGS). apply KPS5. clear - Hx. cbn in Hx. lia.
  + exact Hf64.
  + cbn [ms_mem mkst]. eapply opb_vm_frame; [|exact Hv12'].
    intros x Hx. apply (mbyte_of_aview SEGS). apply KPS5. clear - Hx. cbn in Hx. lia.
  + cbn [ms_mem mkst]. eapply opb_vm_frame; [|exact Hv16'].
    intros x Hx. apply (mbyte_of_aview SEGS). apply KPS5. clear - Hx. cbn in Hx. lia.
  + cbn [ms_mem mkst]. eapply opb_vm_frame; [|exact Hv20'].
    intros x Hx. apply (mbyte_of_aview SEGS). apply KPS5. clear - Hx. cbn in Hx. lia.
  + cbn [ms_mem mkst]. intros i Hi. rewrite (KPS5 (o_ps cx + i) ltac:(clear - Hi; lia)), Hmm.
    exact (Hkeep8 i Hi).
  + cbn [ms_mem mkst].
    exact (opb_kept_call cx fpos ly3 S3 W3 (ms_mem ms) _ ly5 S5 W5 mem5 md5 f (o_k cx + 1)
             HJ3 HJc5 Hfin Hfresh Hincl
             ltac:(intros b0 m0 Hb0; apply (Permutation_in _ (Permutation_sym HPm5)); exact Hb0)
             Hfrs3 Elay ltac:(clear - Hsp1r HFS HTS; lia) ltac:(clear - Hsp1r; lia) Hsplo Hsphi
             ltac:(rewrite Hmm; exact HKEPT)).
  + cbn [ms_mem mkst]. rewrite HFD5. exact Hfds.
  + cbn [ms_mem mkst]. rewrite HFS5. exact Hfsm.
  + cbn [ms_mem mkst]. exact HSN5.
  + exact Hgood.
- (* kr = 24: the 24-byte global header is in the frame's buffer *)
  rewrite branch_ne_U, (U_atom E 10%nat kr E10 ltac:(rewrite Hkr; clear - Hnn HnC; lia)),
    (U_lit E 24 ltac:(clear; lia)) in Hc.
  apply Bool.negb_false_iff, Z.eqb_eq in Hc.
  assert (Hn24 : 24 <= o_n cx) by (rewrite Hkr in Hc; clear - Hc; lia).
  assert (HlenC : (24 <= length (o_C cx))%nat) by (clear - Hn24 Hnn; lia).
  rewrite Hc in Hgarr, HSRC. change (Z.to_nat 24) with 24%nat in Hgarr.
  assert (HB : forall j, (j < 4)%nat ->
    val_mem SEGS (rdW W3 (ms_mem ms3)) (oF cx fpos + OP_HDR + Z.of_nat j) 1 (nth j (o_C cx) 0) /\
    0 <= nth j (o_C cx) 0 < 256).
  { intros j Hj.
    destruct (Hgarr j ltac:(rewrite length_firstn; clear - Hj HlenC; lia)) as (Hv & Hr).
    rewrite (opb_nth_firstn (o_C cx) 24 j 0 ltac:(clear - Hj; lia)) in Hv, Hr.
    split; assumption. }
  assert (Dpf : o_ps cx + 24 <= oF cx fpos \/ oF cx fpos + 128 <= o_ps cx).
  { destruct (Z_le_gt_dec (o_ps cx + 24) (oF cx fpos)) as [Hq|Hq]; [left; exact Hq|].
    destruct (Z_le_gt_dec (oF cx fpos + 128) (o_ps cx)) as [Hq2|Hq2]; [right; exact Hq2|].
    exfalso. destruct (Z_le_gt_dec (oF cx fpos) (o_ps cx)) as [Hq3|Hq3].
    - apply (NWps (o_ps cx) ltac:(clear; lia)). unfold opb_wr. left. clear - Hq3 Hq2. lia.
    - apply (NWps (oF cx fpos) ltac:(clear - Hq3 Hq; lia)). unfold opb_wr. left. clear; lia. }
  (* the environment, now with the four header bytes *)
  clear E HEI EL EREG EX E22 E21 E19 E23 E24 E8 E2 E10 E43 E44 U22 U21 U19 U23 U8 U2 U10 U43 HSAV HCH HS SHOK.
  set (E := Eimg (Ereg (ms_regs ms3) (opb_extra_hdr cx fpos f))).
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms3) (opb_extra_hdr cx fpos f)) n)
    by (intros n Hn; subst E; apply Eimg_low; exact Hn).
  assert (EREG : forall n (r : Prelude.reg), Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r).
  { intros n r Hr. rewrite EL; [exact (ew_Ereg_nat _ _ n r Hr)|].
    pose proof (u5_range r) as Hu. unfold A_TEXT. clear - Hr Hu. lia. }
  assert (EX : forall j, (j < 17)%nat -> ew E (32 + j) = nth j (opb_extra_hdr cx fpos f) (w64 0))
    by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ j)).
  assert (E22 : ew E 22 = w64 (oF cx fpos)) by (rewrite (EREG 22%nat 22%bv eq_refl); exact M22).
  assert (E21 : ew E 21 = w64 (oSH cx fpos)) by (rewrite (EREG 21%nat 21%bv eq_refl); exact M21).
  assert (E19 : ew E 19 = w64 (o_ps cx)) by (rewrite (EREG 19%nat 19%bv eq_refl); exact M19).
  assert (E23 : ew E 23 = w64 SHADOW_OFF) by (rewrite (EREG 23%nat 23%bv eq_refl); exact M23).
  assert (E24 : ew E 24 = w64 (SHADOW_OFF + o_ps cx / 8)) by (rewrite (EREG 24%nat 24%bv eq_refl); exact M24).
  assert (E8 : ew E 8 = w64 (spZ (o_regs cx))) by (rewrite (EREG 8%nat 8%bv eq_refl); exact M8).
  assert (E2 : ew E 2 = w64 (osp1 cx)) by (rewrite (EREG 2%nat 2%bv eq_refl); exact M2).
  assert (E43 : ew E 43 = w64 f).
  { pose proof (EX 11%nat ltac:(lia)) as Hq43. cbn [Nat.add nth opb_extra opb_extra_hdr app] in Hq43.
    exact Hq43. }
  assert (E44 : ew E 44 = w64 (oFL cx fpos)).
  { pose proof (EX 12%nat ltac:(lia)) as Hq44. cbn [Nat.add nth opb_extra opb_extra_hdr app] in Hq44.
    exact Hq44. }
  assert (E45 : ew E 45 = w64 (nth 0 (o_C cx) 0)).
  { pose proof (EX 13%nat ltac:(lia)) as Hq45. cbn [Nat.add nth opb_extra opb_extra_hdr app] in Hq45.
    exact Hq45. }
  assert (E46 : ew E 46 = w64 (nth 1 (o_C cx) 0)).
  { pose proof (EX 14%nat ltac:(lia)) as Hq46. cbn [Nat.add nth opb_extra opb_extra_hdr app] in Hq46.
    exact Hq46. }
  assert (E47 : ew E 47 = w64 (nth 2 (o_C cx) 0)).
  { pose proof (EX 15%nat ltac:(lia)) as Hq47. cbn [Nat.add nth opb_extra opb_extra_hdr app] in Hq47.
    exact Hq47. }
  assert (E48 : ew E 48 = w64 (nth 3 (o_C cx) 0)).
  { pose proof (EX 16%nat ltac:(lia)) as Hq48. cbn [Nat.add nth opb_extra opb_extra_hdr app] in Hq48.
    exact Hq48. }
  assert (U22 : bv_unsigned (ew E 22) = oF cx fpos) by (rewrite E22; apply unsigned_lit_small; clear - HFlt; lia).
  assert (U21 : bv_unsigned (ew E 21) = oSH cx fpos)
    by (rewrite E21; apply unsigned_lit_small; clear - HSHlt; lia).
  assert (U19 : bv_unsigned (ew E 19) = o_ps cx) by (rewrite E19; apply unsigned_lit_small; clear - Hpsb; lia).
  assert (U23 : bv_unsigned (ew E 23) = SHADOW_OFF)
    by (rewrite E23; apply unsigned_lit_small; unfold SHADOW_OFF; clear; lia).
  assert (U8 : bv_unsigned (ew E 8) = spZ (o_regs cx))
    by (rewrite E8; apply unsigned_lit_small; clear - Hspr; lia).
  assert (U2 : bv_unsigned (ew E 2) = osp1 cx)
    by (rewrite E2; apply unsigned_lit_small; clear - Hsp1r Hspr Hsplo C1 HTS; lia).
  assert (U43 : bv_unsigned (ew E 43) = f) by (rewrite E43; apply unsigned_lit_small; clear - Hf64; lia).
  assert (U45 : bv_unsigned (ew E 45) = nth 0 (o_C cx) 0)
    by (rewrite E45; apply unsigned_lit_small; pose proof (proj2 (HB 0%nat ltac:(lia))) as Hq; clear - Hq; lia).
  assert (U46 : bv_unsigned (ew E 46) = nth 1 (o_C cx) 0)
    by (rewrite E46; apply unsigned_lit_small; pose proof (proj2 (HB 1%nat ltac:(lia))) as Hq; clear - Hq; lia).
  assert (U47 : bv_unsigned (ew E 47) = nth 2 (o_C cx) 0)
    by (rewrite E47; apply unsigned_lit_small; pose proof (proj2 (HB 2%nat ltac:(lia))) as Hq; clear - Hq; lia).
  assert (U48 : bv_unsigned (ew E 48) = nth 3 (o_C cx) 0)
    by (rewrite E48; apply unsigned_lit_small; pose proof (proj2 (HB 3%nat ltac:(lia))) as Hq; clear - Hq; lia).
  assert (HSAV : forall j, (j < 11)%nat ->
    val_mem SEGS (rdW W3 (ms_mem ms3)) (spZ (o_regs cx) + (-8 - 8 * Z.of_nat j)) 8
      (bv_unsigned (nth j (opb_extra_hdr cx fpos f) (w64 0)))).
  { intros j Hj. apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)).
    replace (nth j (opb_extra_hdr cx fpos f) (w64 0)) with (nth j (opb_extra cx fpos f) (w64 0))
      by (unfold opb_extra_hdr; rewrite app_nth1; [reflexivity | cbn [length opb_extra]; clear - Hj; lia]).
    destruct j as [|j'];
    [ replace (spZ (o_regs cx) + (-8 - 8 * Z.of_nat 0)) with (spZ (o_regs cx) - 8) by (clear; lia);
      cbn [nth opb_extra]; exact Hra8 |].
    replace (spZ (o_regs cx) + (-8 - 8 * Z.of_nat (S j'))) with (spZ (o_regs cx) - 16 - 8 * Z.of_nat j')
      by (clear; lia).
    rewrite (Hsav (Z.of_nat j') ltac:(clear - Hj; lia)). f_equal.
    do 10 (destruct j' as [|j']; [cbn [nth opb_extra Z.ltb Z.compare]; reflexivity|]).
    cbn [length] in Hj. clear - Hj. lia. }
  assert (HCH : forall j, (j < 11)%nat -> YP09.chunk_ok SEGS E (rdW W3 (ms_mem ms3)) (spZ (o_regs cx))
     (YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (32 + j) 0)))).
  { intros j Hj.
    apply (chunk_ok_val SEGS E _ (spZ (o_regs cx)) (-8 - 8 * Z.of_nat j) 8 (SOff (32 + j) 0)
      (bv_unsigned (nth j (opb_extra_hdr cx fpos f) (w64 0))));
    [ cbn [sv_denot]; rewrite (EX j ltac:(clear - Hj; lia)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | pose proof (u64_range (nth j (opb_extra_hdr cx fpos f) (w64 0))) as Hu;
      change (8 * Z.of_N 8) with 64; clear - Hu; lia
    | zside
    | exact (HSAV j Hj) ]. }
  assert (HCHH : forall j, (j < 4)%nat -> YP09.chunk_ok SEGS E (rdW W3 (ms_mem ms3)) (oF cx fpos)
     (YP09.mkChunk (32 + Z.of_nat j) (CVal 1 (SOff (45 + j) 0)))).
  { intros j Hj.
    apply (chunk_ok_val SEGS E _ (oF cx fpos) (32 + Z.of_nat j) 1 (SOff (45 + j) 0) (nth j (o_C cx) 0));
    [ cbn [sv_denot]; rewrite Z.add_0_r;
      do 4 (destruct j as [|j]; [cbn [Nat.add]; first [rewrite U45 | rewrite U46 | rewrite U47 | rewrite U48];
                                  reflexivity|]); cbn in Hj; clear - Hj; lia
    | change (8 * Z.of_N 1) with 8; exact (proj2 (HB j Hj))
    | zside
    | replace (oF cx fpos + (32 + Z.of_nat j)) with (oF cx fpos + OP_HDR + Z.of_nat j)
        by (unfold OP_HDR; clear; lia);
      exact (proj1 (HB j Hj)) ]. }
  assert (HS : st_ok_pi SEGS VAL E (opb_ss OP_CUT_READ opb_sr_read2 opb_rs_hdr opb_facts)
            (restrict (w_H W3) ms3)).
  { assert (HS0 : st_ok_pi SEGS VAL E (opb_ss OP_CUT_READ sr_atoms opb_rs_hdr opb_facts)
              (restrict (w_H W3) ms3)).
    { rewrite (opb_ms_eta ms3 Hfrg Hsvc Hresv Hfcsr), Hpc, Hrom, restrict_mkst_fx.
      unfold opb_ss, opb_rs_hdr, opb_facts. apply pa_entry_st_ok_full.
      - apply regs_ok_Eimg_Ereg.
      - vm_compute. reflexivity.
      - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]];
        unfold region_ok, opb_stack, opb_ps_ro, opb_hdr;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        + rewrite U8. split; [clear - Hsplo C1 HTS; lia|]. split; [clear - Hspr; lia|].
          split; [intros o Ho; clear - Ho; lia|].
          unfold opb_stack_chunks. apply Forall_map, Forall_forall. intros j Hj.
          apply in_seq in Hj. apply HCH. clear - Hj. lia.
        + rewrite U19. split; [clear - Hpsb; lia|]. split; [clear - Hpsb; lia|].
          split; [intros o Ho; clear - Ho; lia|].
          apply Forall_cons; [|apply Forall_nil].
          apply (chunk_ok_val SEGS E _ (o_ps cx) 0 8 (SOff 43 0) f);
          [ cbn [sv_denot]; rewrite E43, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          | change (8 * Z.of_N 8) with 64; clear - Hf64; lia | zside | rewrite Z.add_0_r; exact Hvf ].
        + rewrite U22. split; [clear - HF4096; lia|]. split; [clear - HFceil C1; lia|].
          split; [intros o Ho; clear - Ho; lia|].
          apply Forall_cons; [exact (HCHH 0%nat ltac:(lia))|].
          apply Forall_cons; [exact (HCHH 1%nat ltac:(lia))|].
          apply Forall_cons; [exact (HCHH 2%nat ltac:(lia))|].
          apply Forall_cons; [exact (HCHH 3%nat ltac:(lia))|]. apply Forall_nil.
      - apply pairwise_disjoint_of_extents.
        unfold opb_rs_hdr, opb_stack, opb_ps_ro, opb_hdr, extent_of_region.
        cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U8, U19, U22.
        cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
        clear - Hsplo C1 HTS Hpsb Hgceil Hfa2 Hfa1 HF4096 HFceil Dpf. repeat split; lia.
      - split; [|split; [exact I | exact I]].
        cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        repeat split; rewrite ?U2, ?U8, ?U19, ?U21, ?U22, ?U23;
        try exact I;
        try (change (2 ^ 6) with 64); try (change (2 ^ 5) with 32); try (change (2 ^ 4) with 16);
        try (change (2 ^ 3) with 8); try (change (2 ^ 0) with 1);
        first [ exact Hsp1m32 | exact Hal16 | exact Hps8 | exact HSHm8 | exact HFal | apply Z.mod_1_r
              | unfold OPB_SB, SHADOW_OFF; clear; lia
              | clear - Hsp1r Hsplo Hshi Hwhi H47 Htop Htop2 C1 HTS Hpsb HSHb HFlt HF4096 HFceil Hspr; lia ]. }
    unfold opb_sr_read2, opb_sr_read, opb_sr, opb_sr_epi.
    refine (ast_ok_pi_set_reg_fp E _ _ (10%bv : bv 5) (SLit 24)
      (ast_ok_pi_set_reg_fp E _ _ (25%bv : bv 5) (SLit 24)
        (ast_ok_pi_set_reg_fp E _ _ (20%bv : bv 5) (SOff 22 32)
          (ast_ok_pi_set_reg_fp E _ _ (24%bv : bv 5) opb_sh8
            (ast_ok_pi_set_reg_fp E _ _ (18%bv : bv 5) (SOff 22 0) HS0 ltac:(vm_compute; reflexivity) _)
            ltac:(vm_compute; reflexivity) _)
          ltac:(vm_compute; reflexivity) _)
        ltac:(vm_compute; reflexivity) _)
      ltac:(vm_compute; reflexivity) _).
    - cbn [ms_regs restrict mkst]. cbn [sv_denot]. rewrite U22, Z.add_0_r. exact (eq_sym M18).
    - cbn [ms_regs restrict mkst]. unfold opb_sh8.
      rewrite (shadow_decl_ok E 19%nat 23%nat 24%nat (o_ps cx) SHADOW_OFF E19 ltac:(clear - Hpsb; lia) E23 E24).
      cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E24. exact (eq_sym M24).
    - cbn [ms_regs restrict mkst]. cbn [sv_denot]. rewrite U22. exact (eq_sym M20).
    - cbn [ms_regs restrict mkst]. cbn [sv_denot]. exact (eq_sym M25).
    - cbn [ms_regs restrict mkst]. cbn [sv_denot]. rewrite <- Hc. exact (eq_sym M10). }
  assert (SHOK : sh_ok SEGS OPB_Bx OPB_SH E (rdW W3 (ms_mem ms3))).
  { unfold sh_ok, OPB_SH, OPB_Bx. apply Forall_cons; [|apply Forall_nil].
    unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
    rewrite (U_atom E 23%nat SHADOW_OFF E23 ltac:(unfold SHADOW_OFF; clear; lia)).
    rewrite (U_atom E 19%nat (o_ps cx) E19 ltac:(clear - Hpsb; lia)).
    split.
    - rewrite Z.add_0_r. rewrite <- (aview_rd_of SEGS). exact Hsh3.
    - intros a Ha. cbn [Z.min Z.max] in Ha. unfold SHADOW_OFF.
      clear - Ha Hgapp Hfa1 Hfa2 Hgnn. lia. }
  (* 0x81600..0x81630: the four header bytes and the first magic test *)
  paj_run_tok RUN HS HJ3 SHOK OPB_span;
    [ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?ownx =>
        let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx ownx) end;
      apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; clear; lia|];
      apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; clear; lia|];
      apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; clear; lia|];
      apply awr_ok_nil |].
  assert (Hmm : ms_mem ms = ms_mem ms3).
  { apply (opb_frame_nil E (ss_mem (opb_ss OP_CUT_READ opb_sr_read2 opb_rs_hdr opb_facts)));
    [ intros r Hr0; cbn [opb_ss ss_mem opb_rs_hdr In] in Hr0;
      destruct Hr0 as [<- | [<- | [<- | []]]]; cbn; clear; lia
    | exact HF ]. }
  assert (HMU : U E (SAlu ALU_OR
      (SAlu ALU_OR (SAlu ALU_SLL (SExt false 8 (SOff 46 0)) (SLit 8)) (SExt false 8 (SOff 45 0)))
      (SAlu ALU_OR (SAlu ALU_SLL (SExt false 8 (SOff 47 0)) (SLit 16))
                   (SAluw ALU_SLL (SExt false 8 (SOff 48 0)) (SLit 24))))
    = pcap_magicZ (o_C cx) + (if nth 3 (o_C cx) 0 <? 128 then 0 else 2 ^ 64 - 2 ^ 32)).
  { unfold pcap_magicZ.
    exact (opb_magic_U E 45%nat 46%nat 47%nat 48%nat (nth 0 (o_C cx) 0) (nth 1 (o_C cx) 0)
             (nth 2 (o_C cx) 0) (nth 3 (o_C cx) 0) E45 E46 E47 E48
             (proj2 (HB 0%nat ltac:(lia))) (proj2 (HB 1%nat ltac:(lia)))
             (proj2 (HB 2%nat ltac:(lia))) (proj2 (HB 3%nat ltac:(lia)))). }
  pose proof (proj2 (HB 0%nat ltac:(lia))) as HB0. pose proof (proj2 (HB 1%nat ltac:(lia))) as HB1.
  pose proof (proj2 (HB 2%nat ltac:(lia))) as HB2. pose proof (proj2 (HB 3%nat ltac:(lia))) as HB3.
  psrr_branch_tok RUN BR HS SHOK OPB_span.
  + (* 0x81630 taken: magic 0xd4c3b2a1, ps->swapped = 1 *)
    rewrite branch_eq_U, HMU, (U_lit E 18446744072984179361 ltac:(clear; lia)) in Hc0.
    apply Z.eqb_eq in Hc0.
    assert (HMG : pcap_magicZ (o_C cx) = 0xD4C3B2A1).
    { unfold pcap_magicZ in Hc0 |- *. destruct (Z.ltb_spec (nth 3 (o_C cx) 0) 128) as [Hq|Hq];
      clear - Hc0 HB0 HB1 HB2 HB3 Hq; lia. }
    paj_run_to_tok RUNTO HS HJ3 SHOK OPB_span OPB_SWAP;
      [ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?ownx =>
          let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx ownx) end;
        apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; clear; lia|];
        apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; clear; lia|];
        apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; clear; lia|];
        apply awr_ok_nil |].
    assert (Hmm2 : ms_mem ms0 = ms_mem ms3).
    { rewrite <- Hmm.
      lazymatch goal with
      | [ Hq : frame_of _ ?rs (ms_mem ms) (ms_mem ms0) |- _ ] =>
        apply (opb_frame_nil E rs);
        [ intros r Hr0; vm_compute in Hr0;
          repeat (destruct Hr0 as [<- | Hr0]; [cbn; clear; lia|]); destruct Hr0
        | exact Hq ]
      end. }
  pose proof HS as (Mfrg & Mpc & Msvc & Mresv & Mfcsr & Mrom & _);
  cbn [restrict ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom] in Mfrg, Mpc, Msvc, Mresv, Mfcsr, Mrom;
  cbn [abs_ss setpc ss_pc ss_resv resv_denot opb_ss] in Mpc, Mresv;
  prreg HS (2%bv : bv 5) P2; prreg HS (3%bv : bv 5) P3; prreg HS (4%bv : bv 5) P4;
  prreg HS (8%bv : bv 5) P8; prreg HS (18%bv : bv 5) P18; prreg HS (19%bv : bv 5) P19;
  prreg HS (21%bv : bv 5) P21; prreg HS (22%bv : bv 5) P22; prreg HS (23%bv : bv 5) P23;
  prreg HS (26%bv : bv 5) P26; prreg HS (27%bv : bv 5) P27;
  lazymatch type of HS with
  | st_ok_pi _ _ _ _ (restrict _ ?msx) =>
    assert (P24 : getr (ms_regs msx) 24 = w64 (SHADOW_OFF + o_ps cx / 8));
    [ pose proof (st_ok_pi_restrict_reg (w_H W3) E _ msx (24%bv : bv 5) HS) as Q24r;
      cbn [ms_regs restrict mkst] in Q24r;
      lazymatch type of Q24r with getr _ _ = sv_denot _ ?e =>
        let e' := eval vm_compute in e in change e with e' in Q24r end;
      rewrite (shadow_decl_ok E 19%nat 23%nat 24%nat (o_ps cx) SHADOW_OFF E19 ltac:(clear - Hpsb; lia) E23 E24)
        in Q24r;
      cbn [sv_denot] in Q24r; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E24 in Q24r; exact Q24r
    | ];
    eapply (opb_accept_tail cx fpos ly3 S3 W3 msx _ (o_k cx + 1) _ f 1 HPRE)
  end;
  [ first [ left; split; reflexivity | right; split; reflexivity ]
  | exact Mpc | exact Mresv | exact Msvc | exact Mrom | exact Mfrg | exact Mfcsr
  | exact HJ3
  | unfold EV_FUZZ_FOPEN; clear; lia
  | exact Hfrs3 | exact Hnin | exact Hab | exact Hincl | exact Hmo | exact Hf4096 | exact Hf16
  | rewrite Hmm2; exact HSRC
  | exact Hbinblk
  | rewrite P2, E2; reflexivity
  | rewrite P8, E8; reflexivity
  | rewrite P18, E22; reflexivity
  | rewrite P19, E19; reflexivity
  | rewrite P21, E21; reflexivity
  | rewrite P22, E22; reflexivity
  | rewrite P23, E23; reflexivity
  | exact P24
  | rewrite P3, (EREG 3%nat 3%bv eq_refl); exact M3
  | rewrite P4, (EREG 4%nat 4%bv eq_refl); exact M4
  | rewrite P26, (EREG 26%nat 26%bv eq_refl); exact M26
  | rewrite P27, (EREG 27%nat 27%bv eq_refl); exact M27
  | rewrite Hmm2; exact Hra8
  | rewrite Hmm2; exact Hsav
  | rewrite Hmm2; exact Hflagp
  | rewrite Hmm2; exact Hsh3
  | rewrite Hmm2; exact Hvf
  | exact Hf64
  | rewrite Hmm2; exact Hv12
  | rewrite Hmm2; exact Hv16
  | rewrite Hmm2; exact Hv20
  | rewrite Hmm2; exact Hkeep8
  | rewrite Hmm2; exact HKEPT
  | repeat rewrite (proj1 (opb_wvb_fds_fs _ _ _)); exact Hfds
  | repeat rewrite (proj2 (opb_wvb_fds_fs _ _ _)); exact Hfsm
  | unfold pcap_goodZ; rewrite HMG;
    destruct (Z.leb_spec 24 (Z.of_nat (length (o_C cx)))) as [Hq|Hq];
    [reflexivity | exfalso; clear - Hq HlenC; lia]
  | unfold pcap_swZ; rewrite HMG; reflexivity ].
  + (* 0x81630 not taken: not the swapped magic *)
    rewrite branch_eq_U, HMU, (U_lit E 18446744072984179361 ltac:(clear; lia)) in Hc0.
    apply Z.eqb_neq in Hc0.
    assert (HM1 : pcap_magicZ (o_C cx) <> 0xD4C3B2A1).
    { unfold pcap_magicZ in Hc0 |- *. intros Hq. apply Hc0.
      destruct (Z.ltb_spec (nth 3 (o_C cx) 0) 128) as [Hq2|Hq2];
      clear - Hq Hq2 HB0 HB1 HB2 HB3; lia. }
    (* 0x81634..0x8163c: the native magic test *)
    paj_run_tok RUN HS HJ3 SHOK OPB_span;
      [ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?ownx =>
          let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx ownx) end;
        repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; clear; lia|]);
        apply awr_ok_nil |].
    lazymatch goal with
    | |- SRr _ _ (mkCfg ?msx _) _ =>
      assert (Hmm2 : ms_mem msx = ms_mem ms3);
      [ rewrite <- Hmm;
        lazymatch goal with
        | [ Hq : frame_of _ ?rs (ms_mem ms) (ms_mem msx) |- _ ] =>
          apply (opb_frame_nil E rs);
          [ intros r Hr0; vm_compute in Hr0;
            repeat (destruct Hr0 as [<- | Hr0]; [cbn; clear; lia|]); destruct Hr0
          | exact Hq ]
        end
      | ]
    end.
    psrr_branch_tok RUN BR HS SHOK OPB_span.
    * (* 0x8163c taken: neither magic, the stream is closed *)
      rewrite branch_ne_U, HMU, (U_lit E 18446744072127431636 ltac:(clear; lia)) in Hc1.
      apply Bool.negb_true_iff, Z.eqb_neq in Hc1.
      assert (HM2 : pcap_magicZ (o_C cx) <> 0xA1B2C3D4).
      { unfold pcap_magicZ in Hc1 |- *. intros Hq. apply Hc1.
        destruct (Z.ltb_spec (nth 3 (o_C cx) 0) 128) as [Hq2|Hq2];
        clear - Hq Hq2 HB0 HB1 HB2 HB3; lia. }
      assert (Hgood : pcap_goodZ (o_C cx) = false).
      { unfold pcap_goodZ.
        destruct (Z.eqb_spec (pcap_magicZ (o_C cx)) 0xA1B2C3D4) as [Hq|Hq]; [exfalso; exact (HM2 Hq)|].
        destruct (Z.eqb_spec (pcap_magicZ (o_C cx)) 0xD4C3B2A1) as [Hq2|Hq2]; [exfalso; exact (HM1 Hq2)|].
        cbn [orb]. apply andb_false_r. }
    (* 0x81668..0x81674: the shadow check of ps, ps->f reloaded, the fclose wrapper *)
    paj_run_tok RUN HS HJ3 SHOK OPB_span;
      [ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?ownx =>
          let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx ownx) end;
        repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; clear; lia|]);
        apply awr_ok_nil |].
    lazymatch goal with
    | |- SRr _ _ (mkCfg ?msx _) _ =>
      assert (Hmm4 : ms_mem msx = ms_mem ms3);
      [ rewrite <- Hmm2;
        lazymatch goal with
        | [ Hq : frame_of _ ?rs (ms_mem ms0) (ms_mem msx) |- _ ] =>
          apply (opb_frame_nil E rs);
          [ intros r Hr0; vm_compute in Hr0;
            repeat (destruct Hr0 as [<- | Hr0]; [cbn; clear; lia|]); destruct Hr0
          | exact Hq ]
        end
      | ]
    end.
    assert (Hvf' : val_mem SEGS (rdW W3 (ms_mem ms1)) (o_ps cx) 8 f) by (rewrite Hmm4; exact Hvf).
    assert (Hv12' : val_mem SEGS (rdW W3 (ms_mem ms1)) (o_ps cx + 12) 4 0) by (rewrite Hmm4; exact Hv12).
    assert (Hv16' : val_mem SEGS (rdW W3 (ms_mem ms1)) (o_ps cx + 16) 4 0) by (rewrite Hmm4; exact Hv16).
    assert (Hv20' : val_mem SEGS (rdW W3 (ms_mem ms1)) (o_ps cx + 20) 2 0) by (rewrite Hmm4; exact Hv20).
    pmkst HS.
    prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
    prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
    prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (21%bv : bv 5) Q21.
    prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
    prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
    assert (Q24s : getr (ms_regs ms1) 24 = w64 (SHADOW_OFF + o_ps cx / 8)).
    { pose proof (st_ok_restrict_reg SEGS (w_H W3) E _ ms1 (24%bv : bv 5) HS) as Q24r.
      cbn [ms_regs restrict mkst] in Q24r.
      lazymatch type of Q24r with getr _ _ = sv_denot _ ?e =>
        let e' := eval vm_compute in e in change e with e' in Q24r end.
      rewrite (shadow_decl_ok E 19%nat 23%nat 24%nat (o_ps cx) SHADOW_OFF E19 ltac:(clear - Hpsb; lia) E23 E24)
        in Q24r.
      cbn [sv_denot] in Q24r. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E24 in Q24r. exact Q24r. }
    assert (Hspc : spZ (ms_regs ms1) = o_sp0 cx + (osp1 cx - o_sp0 cx)).
    { unfold spZ. rewrite Q2, E2. unfold w64.
      rewrite unsigned_lit_small by (clear - Hsp1r Hspr Hsplo C1 HTS; lia). clear; lia. }
    eapply SRr_bind.
    { eapply (cl_callS B LAWS W3 (ms_regs ms1) (ms_mem ms1) _ (o_STK cx) (o_sp0 cx) (o_FP cx) (o_ly cx) (o_S cx)
        (o_W0 cx) (o_mem0 cx) (o_md0 cx) ((OP_CID, fpos) :: o_own cx) ly3 S3 _ (o_k cx + 1)
        PFCLOSE_STK (asource_fp f) 2 (osp1 cx - o_sp0 cx) (Z_to_bv 64 (BASE + OPB_RET2))
        ((spZ (o_regs cx), raZ (o_regs cx), s0Z (o_regs cx)) :: o_ch cx)
        (fun ly5 S5 W5 regs5 mem5 md5 =>
           getr regs5 10 = Z_to_bv 64 0 /\ Permutation (ablocks B ly5 S5) (ablocks B (o_lyc cx) (o_Sc cx)) /\
           frames S5 = frames S3 /\ asource_none SEGS K (rdW W5 mem5) /\
           m_fds md5 = m_fds md3 /\ m_fs md5 = m_fs md3) HJ3 Hspc).
      - rewrite Zminus_mod, Hsp1m16, Hsp0al. reflexivity.
      - clear - Hsp1r Hwhi. lia.
      - unfold PFCLOSE_STK. clear; lia.
      - rewrite HFS. clear - Hsp1r Hwlo Hwhi HTS. lia.
      - rewrite Q3, (EREG 3%nat 3%bv eq_refl), M3. exact Hgp.
      - rewrite Q4, (EREG 4%nat 4%bv eq_refl), M4. exact Htp.
      - exact Q1.
      - apply ret_ok_codeptr_v; [unfold OPB_RET2; clear; lia | reflexivity].
      - rewrite unsigned_lit_small by (pose proof (pa_base_lo (PL := PL_pcap) (PI := PI));
          pose proof pa_B_ok as (HB0' & HB1' & _); unfold OPB_RET2; clear - HB0' HB1'; lia).
        pose proof (pa_base_lo (PL := PL_pcap) (PI := PI)). unfold OPB_RET2. clear - H. lia.
      - replace (o_sp0 cx + (osp1 cx - o_sp0 cx)) with (osp1 cx) by (clear; lia).
        unfold s0Z. rewrite Q8, E8. unfold w64. rewrite unsigned_lit_small by (clear - Hspr; lia).
        rewrite Hmm4. exact Hchain3.
      - intros HPRE1. eapply SRr_mono.
        + eapply (AFCLOSE W3 ly3 S3 (ms_regs ms1) (ms_mem ms1) _ _ f (o_b cx) (o_M cx) (o_C cx) 24
            (ablocks B (o_lyc cx) (o_Sc cx)) HPRE1).
          * rewrite Q10, E43. reflexivity.
          * exact HPf.
          * rewrite Hmm4. exact HSRC.
          * exact Hbinblk.
          * rewrite Hmm4. exact HMETA3.
          * rewrite Hmm4. intros a Ha Ho He. exact (HROD3 a Ha Ho He).
          * exact HEVf.
          * exact HUfc1.
          * exact HUfc2.
        + cbv beta. intros W5 c5 _ (ly5 & S5 & regs5 & mem5 & md5 & -> & HJc5 & HP5 & Ha05 & HPm5 & Hfrs5 &
            HSN5 & HGB5 & HFD5 & HFS5).
          exists ly5, S5, regs5, mem5, md5. split; [rewrite Q1; reflexivity|].
          split; [exact HJc5|]. split; [exact HP5|].
          split; [exact Ha05|]. split; [exact HPm5|]. split; [exact Hfrs5|]. split; [exact HSN5|].
          split; [rewrite HFD5; repeat rewrite (proj1 (opb_wvb_fds_fs _ _ _)); reflexivity
                 | rewrite HFS5; repeat rewrite (proj2 (opb_wvb_fds_fs _ _ _)); reflexivity].
      - exact HFPinc. }
    cbv beta. intros W5 c5 _ (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ5 & HJc5 & HP5 & Ha05 & HPm5 & Hfrs5 &
      HSN5 & HFD5 & HFS5).
    replace (o_sp0 cx + (osp1 cx - o_sp0 cx)) with (osp1 cx) in HJc5 by (clear; lia).
    pose proof HJc5 as (HAR5 & _ & _ & _ & _ & _ & _ & _ & G1 & _ & _ & G4 & _).
    assert (Hfdisj : forall a, o_ps cx <= a < o_ps cx + 24 -> ~ inFP (asource_fp f) a).
    { intros a Ha Hcf.
      pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 f SRC_FILE_BLOCK
        (o_cid cx) (o_pos cx) HAR3 Hfin Hin3) as Dfg.
      unfold zdisjoint in Dfg. cbn [fst snd] in Dfg. change (req_size SRC_FILE_BLOCK) with 1304 in Dfg.
      rewrite <- (Elay (o_cid cx) (o_pos cx)) in Dfg.
      destruct (in_asource_fp f a Hcf) as [Hq | Hq]; unfold SRC_FILE_BLOCK in Hq;
      [clear - Hq Ha Dfg Hfa1 Hfa2 | clear - Hq Ha Hpsb]; lia. }
    assert (KPS5 : forall a, o_ps cx <= a < o_ps cx + 24 ->
              aview SEGS (w_H W5) mem5 a = aview SEGS (w_H W3) (ms_mem ms1) a).
    { intros a Ha. apply (G4 (o_cid cx) (o_pos cx) a Hin3); [|exact (Hfdisj a Ha)].
      left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite <- (Elay (o_cid cx) (o_pos cx)).
      clear - Ha Hfa1 Hfa2. lia. }
    assert (KST5 : forall a, spZ (o_regs cx) - 96 <= a < spZ (o_regs cx) ->
              aview SEGS (w_H W5) mem5 a = aview SEGS (w_H W3) (ms_mem ms1) a)
      by (intros a Ha; apply G1; [clear - Ha Hsplo C1 HTS Hspr; lia | clear - Ha Hsp1r HFS; lia]).
    assert (KFL5 : forall a, oF cx fpos <= a < oF cx fpos + 128 ->
              aview SEGS (w_H W5) mem5 a = aview SEGS (w_H W3) (ms_mem ms1) a).
    { intros a Ha. apply (G4 OP_CID fpos a HinF).
      - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF.
        change (fs_frame_bytes OP_CID) with 128. clear - Ha. lia.
      - intros Hcf.
        pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 f SRC_FILE_BLOCK OP_CID fpos
          HAR3 Hfin HinF) as DfF.
        unfold zdisjoint in DfF. cbn [fst snd] in DfF. change (req_size SRC_FILE_BLOCK) with 1304 in DfF.
        rewrite EF in DfF. change (fs_frame_bytes OP_CID) with 128 in DfF.
        destruct (in_asource_fp f a Hcf) as [Hq | Hq]; unfold SRC_FILE_BLOCK in Hq;
        [clear - Hq Ha DfF | clear - Hq Ha HF4096]; lia. }
    assert (HR5 : forall (r : Prelude.reg), acallee_saved (bv_unsigned r) ->
              getr regs5 r = getr (ms_regs ms1) r)
      by (intros r Hr; pose proof (HP5 (bv_unsigned r) Hr) as Hq; rewrite !Z_to_bv_bv_unsigned in Hq;
          exact Hq).
    eapply (opb_refuse_tail cx fpos ly5 S5 W5
      (mkst regs5 (Z_to_bv 64 (BASE + OPB_RET2)) mem5 (seg_rom SEGS)) md5 (o_k cx + 1 + 2) OPB_RET2 f
      HPRE (or_intror eq_refl) eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl).
    ** exact HJ5.
    ** unfold EV_OPEN, EV_FUZZ_FOPEN. clear; lia.
    ** rewrite Hfrs5. exact Hfrs3.
    ** exact Hnin.
    ** exact HPm5.
    ** intros b0 m0 Hb0. apply (Permutation_in _ (Permutation_sym HPm5)). exact Hb0.
    ** unfold OPEN_METER.
      exact (mle_station MT _ _ _ _ _ MLAW Hmo (asfm_close SK SEGS B MT FM _ _ _ _ _ _ _ _ _ _ _ _ _ _
               f (ablocks B (o_lyc cx) (o_Sc cx)) HJc5 HPf HPm5)).
    ** cbn [ms_regs mkst]. rewrite (HR5 2%bv ltac:(clear; unfold acallee_saved; change (bv_unsigned 2%bv) with 2; lia)), Q2, E2. reflexivity.
    ** cbn [ms_regs mkst]. rewrite (HR5 8%bv ltac:(clear; unfold acallee_saved; change (bv_unsigned 8%bv) with 8; lia)), Q8, E8. reflexivity.
    ** cbn [ms_regs mkst]. rewrite (HR5 18%bv ltac:(clear; unfold acallee_saved; change (bv_unsigned 18%bv) with 18; lia)), Q18, E22. reflexivity.
    ** cbn [ms_regs mkst]. rewrite (HR5 19%bv ltac:(clear; unfold acallee_saved; change (bv_unsigned 19%bv) with 19; lia)), Q19, E19. reflexivity.
    ** cbn [ms_regs mkst]. rewrite (HR5 21%bv ltac:(clear; unfold acallee_saved; change (bv_unsigned 21%bv) with 21; lia)), Q21, E21. reflexivity.
    ** cbn [ms_regs mkst]. rewrite (HR5 22%bv ltac:(clear; unfold acallee_saved; change (bv_unsigned 22%bv) with 22; lia)), Q22, E22. reflexivity.
    ** cbn [ms_regs mkst]. rewrite (HR5 23%bv ltac:(clear; unfold acallee_saved; change (bv_unsigned 23%bv) with 23; lia)), Q23, E23. reflexivity.
    ** cbn [ms_regs mkst].
      rewrite (HR5 24%bv ltac:(clear; unfold acallee_saved; change (bv_unsigned 24%bv) with 24; lia)).
      exact Q24s.
    ** cbn [ms_regs mkst]. rewrite (HR5 3%bv ltac:(clear; unfold acallee_saved; change (bv_unsigned 3%bv) with 3; lia)), Q3,
        (EREG 3%nat 3%bv eq_refl). exact M3.
    ** cbn [ms_regs mkst]. rewrite (HR5 4%bv ltac:(clear; unfold acallee_saved; change (bv_unsigned 4%bv) with 4; lia)), Q4,
        (EREG 4%nat 4%bv eq_refl). exact M4.
    ** cbn [ms_regs mkst]. rewrite (HR5 26%bv ltac:(clear; unfold acallee_saved; change (bv_unsigned 26%bv) with 26; lia)), Q26,
        (EREG 26%nat 26%bv eq_refl). exact M26.
    ** cbn [ms_regs mkst]. rewrite (HR5 27%bv ltac:(clear; unfold acallee_saved; change (bv_unsigned 27%bv) with 27; lia)), Q27,
        (EREG 27%nat 27%bv eq_refl). exact M27.
    ** cbn [ms_mem mkst]. rewrite (opb_rdword_ext (aview SEGS (w_H W3) (ms_mem ms1))
        (aview SEGS (w_H W5) mem5) (spZ (o_regs cx) - 8)
        ltac:(intros i Hi; apply KST5; clear - Hi; lia)), Hmm4. exact Hra8.
    ** cbn [ms_mem mkst]. intros j Hj.
      rewrite (opb_rdword_ext (aview SEGS (w_H W3) (ms_mem ms1)) (aview SEGS (w_H W5) mem5)
        (spZ (o_regs cx) - 16 - 8 * j) ltac:(intros i Hi; apply KST5; clear - Hi Hj; lia)), Hmm4.
      exact (Hsav j Hj).
    ** cbn [ms_mem mkst]. rewrite (opb_rdword_ext (aview SEGS (w_H W3) (ms_mem ms1))
        (aview SEGS (w_H W5) mem5) (oF cx fpos + OP_FLAGPTR)
        ltac:(intros i Hi; apply KFL5; unfold OP_FLAGPTR; clear - Hi; lia)), Hmm4. exact Hflagp.
    ** cbn [ms_mem mkst]. apply (ra_frame (aview SEGS (w_H W3) (ms_mem ms3))); [exact Hsh3|].
      intros x Hx. unfold shadow_of_addr. rewrite <- Hmm4.
      apply (G4 (o_cid cx) (o_pos cx) (SHADOW_OFF + x / 8) Hin3).
      *** right. unfold in_zr. cbn [fst snd]. rewrite <- (Elay (o_cid cx) (o_pos cx)).
        pose proof (frame_al64 SEGS B (o_lyc cx) (o_Sc cx) (o_W cx) (o_memc cx) (o_mdc cx) (o_cid cx) (o_pos cx)
          HAR Hin) as (Hga & Hgb & _).
        destruct (opb_div8_mul64 _ Hga) as (Hd1 & He1). destruct (opb_div8_mul64 _ Hgb) as (Hd2 & He2).
        assert (Hlo : frame_addr (o_lyc cx) (o_cid cx) (o_pos cx) / 8 <= x / 8)
          by (apply Z.div_le_mono; [clear; lia | clear - Hx Hfa1; lia]).
        assert (Hhi : x / 8 < frame_addr (o_lyc cx) (o_cid cx) (o_pos cx) / 8 + fs_frame_bytes (o_cid cx) / 8)
          by (apply Z.div_lt_upper_bound; [clear; lia | rewrite Hd1, Hd2; clear - Hx Hfa2 He1 He2; lia]).
        unfold shadow_addr, SHADOW_OFF. clear - Hlo Hhi. lia.
      *** intros Hcf.
        assert (Hx44 : x / 8 < 2 ^ 44)
          by (apply Z.div_lt_upper_bound; [clear; lia | clear - Hx Hfa2 Hgceil C1; lia]).
        assert (Hx0 : 0 <= x / 8) by (apply Z.div_pos; [clear - Hx Hpsb; lia | clear; lia]).
        destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 f SRC_FILE_BLOCK HAR3 Hfin)
          as (_ & Hq1 & Hq2 & Hq3 & _ & _).
        unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hq3.
        change (req_size SRC_FILE_BLOCK) with 1304 in Hq2, Hq3.
        destruct (in_asource_fp f (SHADOW_OFF + x / 8) Hcf) as [Hq | Hq]; unfold SRC_FILE_BLOCK in Hq;
        unfold SHADOW_OFF in Hq; clear - Hq Hx44 Hx0 Hq1 Hq2 Hq3; lia.
    ** cbn [ms_mem mkst]. eapply opb_vm_frame; [|exact Hvf'].
      intros x Hx. apply (mbyte_of_aview SEGS). apply KPS5. clear - Hx. cbn in Hx. lia.
    ** exact Hf64.
    ** cbn [ms_mem mkst]. eapply opb_vm_frame; [|exact Hv12'].
      intros x Hx. apply (mbyte_of_aview SEGS). apply KPS5. clear - Hx. cbn in Hx. lia.
    ** cbn [ms_mem mkst]. eapply opb_vm_frame; [|exact Hv16'].
      intros x Hx. apply (mbyte_of_aview SEGS). apply KPS5. clear - Hx. cbn in Hx. lia.
    ** cbn [ms_mem mkst]. eapply opb_vm_frame; [|exact Hv20'].
      intros x Hx. apply (mbyte_of_aview SEGS). apply KPS5. clear - Hx. cbn in Hx. lia.
    ** cbn [ms_mem mkst]. intros i Hi. rewrite (KPS5 (o_ps cx + i) ltac:(clear - Hi; lia)), Hmm4.
      exact (Hkeep8 i Hi).
    ** cbn [ms_mem mkst].
      exact (opb_kept_call cx fpos ly3 S3 W3 (ms_mem ms1) _ ly5 S5 W5 mem5 md5 f (o_k cx + 1)
               HJ3 HJc5 Hfin Hfresh Hincl
               ltac:(intros b0 m0 Hb0; apply (Permutation_in _ (Permutation_sym HPm5)); exact Hb0)
               Hfrs3 Elay ltac:(clear - Hsp1r HFS HTS; lia) ltac:(clear - Hsp1r; lia) Hsplo Hsphi
               ltac:(rewrite Hmm4; exact HKEPT)).
    ** cbn [ms_mem mkst]. rewrite HFD5. exact Hfds.
    ** cbn [ms_mem mkst]. rewrite HFS5. exact Hfsm.
    ** cbn [ms_mem mkst]. exact HSN5.
    ** exact Hgood.
    * (* 0x8163c not taken: the native magic, ps->swapped = 0 *)
      rewrite branch_ne_U, HMU, (U_lit E 18446744072127431636 ltac:(clear; lia)) in Hc1.
      apply Bool.negb_false_iff, Z.eqb_eq in Hc1.
      assert (HMG : pcap_magicZ (o_C cx) = 0xA1B2C3D4).
      { unfold pcap_magicZ in Hc1 |- *. destruct (Z.ltb_spec (nth 3 (o_C cx) 0) 128) as [Hq|Hq];
        clear - Hc1 HB0 HB1 HB2 HB3 Hq; lia. }
      paj_run_to_tok RUNTO HS HJ3 SHOK OPB_span OPB_NATIVE;
        [ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?ownx =>
            let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx ownx) end;
          repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; clear; lia|]);
          apply awr_ok_nil |].
      lazymatch goal with
      | |- SRr _ _ (mkCfg ?msx _) _ =>
        assert (Hmm3 : ms_mem msx = ms_mem ms3);
        [ rewrite <- Hmm2;
          lazymatch goal with
          | [ Hq : frame_of _ ?rs (ms_mem ms0) (ms_mem msx) |- _ ] =>
            apply (opb_frame_nil E rs);
            [ intros r Hr0; vm_compute in Hr0;
              repeat (destruct Hr0 as [<- | Hr0]; [cbn; clear; lia|]); destruct Hr0
            | exact Hq ]
          end
        | ]
      end.
      pose proof HS as (Mfrg & Mpc & Msvc & Mresv & Mfcsr & Mrom & _);
      cbn [restrict ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom] in Mfrg, Mpc, Msvc, Mresv, Mfcsr, Mrom;
      cbn [abs_ss setpc ss_pc ss_resv resv_denot opb_ss] in Mpc, Mresv;
      prreg HS (2%bv : bv 5) P2; prreg HS (3%bv : bv 5) P3; prreg HS (4%bv : bv 5) P4;
      prreg HS (8%bv : bv 5) P8; prreg HS (18%bv : bv 5) P18; prreg HS (19%bv : bv 5) P19;
      prreg HS (21%bv : bv 5) P21; prreg HS (22%bv : bv 5) P22; prreg HS (23%bv : bv 5) P23;
      prreg HS (26%bv : bv 5) P26; prreg HS (27%bv : bv 5) P27;
      lazymatch type of HS with
      | st_ok_pi _ _ _ _ (restrict _ ?msx) =>
        assert (P24 : getr (ms_regs msx) 24 = w64 (SHADOW_OFF + o_ps cx / 8));
        [ pose proof (st_ok_pi_restrict_reg (w_H W3) E _ msx (24%bv : bv 5) HS) as Q24r;
          cbn [ms_regs restrict mkst] in Q24r;
          lazymatch type of Q24r with getr _ _ = sv_denot _ ?e =>
            let e' := eval vm_compute in e in change e with e' in Q24r end;
          rewrite (shadow_decl_ok E 19%nat 23%nat 24%nat (o_ps cx) SHADOW_OFF E19 ltac:(clear - Hpsb; lia) E23 E24)
            in Q24r;
          cbn [sv_denot] in Q24r; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E24 in Q24r; exact Q24r
        | ];
        eapply (opb_accept_tail cx fpos ly3 S3 W3 msx _ (o_k cx + 1) _ f 0 HPRE)
      end;
      [ first [ left; split; reflexivity | right; split; reflexivity ]
      | exact Mpc | exact Mresv | exact Msvc | exact Mrom | exact Mfrg | exact Mfcsr
      | exact HJ3
      | unfold EV_FUZZ_FOPEN; clear; lia
      | exact Hfrs3 | exact Hnin | exact Hab | exact Hincl | exact Hmo | exact Hf4096 | exact Hf16
      | rewrite Hmm3; exact HSRC
      | exact Hbinblk
      | rewrite P2, E2; reflexivity
      | rewrite P8, E8; reflexivity
      | rewrite P18, E22; reflexivity
      | rewrite P19, E19; reflexivity
      | rewrite P21, E21; reflexivity
      | rewrite P22, E22; reflexivity
      | rewrite P23, E23; reflexivity
      | exact P24
      | rewrite P3, (EREG 3%nat 3%bv eq_refl); exact M3
      | rewrite P4, (EREG 4%nat 4%bv eq_refl); exact M4
      | rewrite P26, (EREG 26%nat 26%bv eq_refl); exact M26
      | rewrite P27, (EREG 27%nat 27%bv eq_refl); exact M27
      | rewrite Hmm3; exact Hra8
      | rewrite Hmm3; exact Hsav
      | rewrite Hmm3; exact Hflagp
      | rewrite Hmm3; exact Hsh3
      | rewrite Hmm3; exact Hvf
      | exact Hf64
      | rewrite Hmm3; exact Hv12
      | rewrite Hmm3; exact Hv16
      | rewrite Hmm3; exact Hv20
      | rewrite Hmm3; exact Hkeep8
      | rewrite Hmm3; exact HKEPT
      | repeat rewrite (proj1 (opb_wvb_fds_fs _ _ _)); exact Hfds
      | repeat rewrite (proj2 (opb_wvb_fds_fs _ _ _)); exact Hfsm
      | unfold pcap_goodZ; rewrite HMG;
        destruct (Z.leb_spec 24 (Z.of_nat (length (o_C cx)))) as [Hq|Hq];
        [reflexivity | exfalso; clear - Hq HlenC; lia]
      | unfold pcap_swZ; rewrite HMG; reflexivity ].
Qed.

End e.
End d.
End b.
