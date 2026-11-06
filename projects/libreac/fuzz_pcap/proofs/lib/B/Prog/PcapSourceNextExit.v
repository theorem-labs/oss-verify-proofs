(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, with its module paths and module names changed; 693 of its 715 lines of code are new or changed and 308 lines of the source are left out. *)
(* pcap_source_next (fuzz_pcap.asan-ubsan 0x815b8, listing offset AF_pcap_source_next = 0xe30) on the
   ASan+UBSan build of libreac v1.9.0: the last two phases of the walk, from the exit join NP_exit
   (0x818b4) and from NP_x0 (0x818cc) to the `ret` at NP_ret (0x8196c).

   Every number is read from the pinned fuzz_pcap.asan-ubsan image
   (sha256 9e66f771f22af67a...); symbols and the capstone 5 disassembly of 0x815b8..0x81c38 from its unstripped
   twin fuzz_pcap.asan-ubsan (sha256 c969d83cdd59) (same .text, sha256 of the section 29db9ad9acab107d...).
   The listing starts at 0x80788 (lib/B/Prog/PcapAddr.v pcap_text), so a listing offset is the address - 0x80788.

   THE CODE. Every open-reader exit (cap = 0 at 0x81818 and a short chunk at 0x8184c through NP_xm1 0x818a8, a
   short header at 0x8197c / 0x81984, a short record at 0x819b4, the timestamp path at 0x81b60) arrives at 0x818b4
   with a1 = the result, a6 = the slot 0x68(s1) (__asan_stack_malloc_0's result F) and s3 = the slot 0x40(s1) (F)
   already reloaded; the closed reader comes through 0x818c4 (`li a1,-1; ld a6,0x68(s1)`, s3 = F still). s9 is the
   frame's shadow address from 0x8169c on.
     0x818b4 li a0,-8; sb a0,4(s9); sb a0,5(s9); j    `ph` out of scope (shadow bytes 4 and 5 := 0xf8)  (NP_exit)
     0x818cc lui/addiw a0 = 0x45e0360e; sd a0,0(s3)     the retired-frame magic at F                      (NP_x0)
     0x818d8 beqz a6                                    a6 = F >= 4096: the machine-frame arm 0x8190c..0x81928
                                                        (eight `sb zero`) is not taken
     0x818dc li a0,-11; sb a0,4,5,6,7,0,1,2,3(s9)       the frame's eight shadow bytes := 0xf5
     0x81900 ld a0,0x38(a6); sb zero,0(a0); j           the slot's last word is its flag byte's address:
                                                        the FLAG STORE gives the frame back (aj_flag_store_pi)
     0x8192c mv a0,a1; addi sp,s0,-0x100; ld ra..s11; addi sp,sp,0x100; ret            (NP_epi .. NP_ret)
   The machine-stack arm is dead: the frame is the side-stack frame F the journal holds
   (frames S3 = (NX_CID, fp) :: frames Sc), and F >= 4096.

   THE PROOF. One symbolic run from the start pc to the `ret`, through PcapFrame.aj_flag_store_pi (the
   journal loses the frame: own (NX_CID, fp) :: own' becomes own', the state stack_free_state), then
   PcapPaLib.paj_ret_at. The run writes 17 bytes, nxb_tail_wr: F..F+8, the frame's shadow, the flag byte.
   None of them is a byte the caller sees (nxb_tail_out), so the caller-facing facts nx_fin carries are kept
   (nxb_fin_tail). The control flow is a Theorem Labs lane's v1.9 run table (pcap-v190-next.md (sha256 b1d06d8683d6; internal record), lib/B
   psn_epi 0x8192c -> ret 0x8196c). *)
(* Modified by Theorem Labs, 2026-10: lib/B twin of lib/A/Prog/PcapSourceNextExit.v (a Theorem Labs lane): the code,
   pcs, registers and frame are the asan-ubsan image's; the tail run is stated over the caller's data
   (implicit section context, premises bundled in nxb_cp / nxb_fp), and the two phases are its instances. *)
(* Modified by Theorem Labs, 2026-10: Section f's vm_frame / asource_at_frame (a copy of lib/B/Prog/PcapSourceClose.v's,
   over an implicit segs) deleted; their uses name lib/A/Prog/PcapSourceCloseSpec.v's vm_frame_segs /
   asource_at_frame_segs. *)
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
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05 PcapImgEnd YE00 YG0p YC5d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym PaShadow.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaRun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSyms PcapList PcapAddr PcapPa PcapPaLib.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapBase YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import YC1g YC1h YC85 PcapFrame.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta PFreadISpec.
(* The shared statement and its image-free constants (NxCore-2's Spec, 607d702cbb4): Required directly, so the
   alias AN below does not depend on what lib/B's Defs Require-Exports. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require PcapSourceNextSpec.
(* The stream predicates read only their footprint: the segs-generic vm_frame_segs / asource_at_frame_segs of
   lib/A/Prog/PcapSourceCloseSpec.v (a Theorem Labs lane, image-free), Required without Import and used qualified. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require PcapSourceCloseSpec.
(* lib/B's phase layer, LAST: lib/B's names shadow the shared ones. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSourceNextDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* The shared statement and its image-free data (the class-0 frame NX_CID, the flag word's offset
   NX_FLAGPTR, the struct layout, EV_NEXT, nx_bufn, nx_fin / nx_kept / nx_wrset / nx_wr_ok / nx_ps_at,
   tpcap_source_next_post), by Spec's names. *)
Module AN := OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog.PcapSourceNextSpec.

Lemma nxb_regs_ok_havoc_hi : forall E k ws regs,
  (32 <= k)%nat -> regs_ok E sr_atoms regs -> regs_ok (havoc E k ws) sr_atoms regs.
Proof.
intros E k ws regs Hk H. apply (regs_ok_agree 32 E);
[ apply (env_agree_havoc_ge 32 k E E ws Hk (env_agree_refl 32 E)) | vm_compute; reflexivity | exact H ].
Qed.

(* The flag byte reads 0 after the run: its region is the head of the run's region list, and the
   store `sb zero,0(a0)` (0x81904) left the chunk 0 there. Copied from lib/A's PcapSourceNextExit.v
   `nx_flag0` (a Theorem Labs lane's lib/A/Prog/ACbf.v `flag0`, itself from cgif lib/A/ACbf.v), with E528 the flag
   atom's value. *)
Ltac nxb_flag0 E528 EFL :=
let msr := fresh "msr" in let HSr := fresh "HSr" in let HR := fresh "HR" in let V := fresh "V" in
intros msr HSr; rewrite ?EFL;
lazymatch type of HSr with st_ok_pi _ _ ?Ex ?ssx _ =>
pose proof (st_ok_pi_region_nth Ex ssx msr 0 _ HSr eq_refl) as HR;
lazymatch type of HR with region_ok _ _ _ (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex (ms_mem msr) n _ cs lo hi wlo whi 0 1%N (SLit 0) 0 HR
ltac:(rewrite E528; apply unsigned_lit_small; lia)
ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V end end;
rewrite Z.add_0_r in V; pose proof (V 0%nat ltac:(lia)) as V0; cbn [Z.of_nat] in V0; rewrite Z.add_0_r in V0; exact V0.

(* ---- the symbolic state of the tail ---- *)

(* Atoms: 0..31 the registers at the start pc, 240..511 the image, 528 the frame's flag byte, and
   540..552 the entry values of ra, s0, s1, s2..s11, which the epilogue reloads from the machine frame
   (0x81934..0x81964: ra at sp0 - 8, s0 at sp0 - 16, .., s11 at sp0 - 104; saved at 0x815c0..0x815f0). *)
Definition nxb_saved_chunks : list YP09.chunk :=
  [ YP09.mkChunk (-104) (CVal 8 (SOff 552 0)); YP09.mkChunk (-96) (CVal 8 (SOff 551 0));
    YP09.mkChunk (-88) (CVal 8 (SOff 550 0)); YP09.mkChunk (-80) (CVal 8 (SOff 549 0));
    YP09.mkChunk (-72) (CVal 8 (SOff 548 0)); YP09.mkChunk (-64) (CVal 8 (SOff 547 0));
    YP09.mkChunk (-56) (CVal 8 (SOff 546 0)); YP09.mkChunk (-48) (CVal 8 (SOff 545 0));
    YP09.mkChunk (-40) (CVal 8 (SOff 544 0)); YP09.mkChunk (-32) (CVal 8 (SOff 543 0));
    YP09.mkChunk (-24) (CVal 8 (SOff 542 0)); YP09.mkChunk (-16) (CVal 8 (SOff 541 0));
    YP09.mkChunk (-8) (CVal 8 (SOff 540 0)) ].

(* The regions: the flag byte (atom 528, written), the frame F (s3 = atom 19; F+0..8 written, the slot's
   last word F+56 holds the flag byte's address), its eight shadow bytes (s9 = atom 25, written), and the
   saved registers below s0 (atom 8, read only). Both starts have the same regions: neither reads a spill
   slot (a6 and s3 are reloaded before 0x818b4). *)
Definition nxb_regions : YP09.smem :=
  [ YP09.mkRegion (Some 528%nat) 0 1 0 1 [];
    YP09.mkRegion (Some 19%nat) 0 64 0 8 [YP09.mkChunk 56 (CVal 8 (SOff 528 0))];
    YP09.mkRegion (Some 25%nat) 0 8 0 8 [];
    YP09.mkRegion (Some 8%nat) (-104) 0 0 0 nxb_saved_chunks ].
(* F is a pointer at least 4096, 64-aligned (the branch `beqz a6` 0x818d8 is decided by it); so is the
   flag byte's address (any alignment). *)
Definition nxb_tail_G : facts := mkFacts [(19%nat, HPTR 6); (528%nat, HPTR 0)] [] [].

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg pcap_listing}.
#[local] Notation SEGS := (@pa_segs _ pcap_listing PI).
#[local] Notation VAL := (@pa_val _ pcap_listing PI).
#[local] Notation BASE := (@pa_val _ pcap_listing PI A_TEXT).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).

(* A saved-register chunk from the word the invariant gives. *)
Lemma nxb_saved_chunk : forall (E : env) (H : word -> bool) (mem : word -> option byte) n sp off (w : word),
  ew E n = w -> rdword (aview SEGS H mem) (sp + off) = Some (bv_unsigned w) ->
  YP09.chunk_ok SEGS E (mrestrict H mem) sp (YP09.mkChunk off (CVal 8 (SOff n 0))).
Proof.
intros E H mem n sp off w Hn Hr.
apply (chunk_ok_val SEGS E (mrestrict H mem) sp off 8 (SOff n 0) (bv_unsigned w)).
- cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- pose proof (bv_unsigned_in_range 64 w) as Q. change (bv_modulus 64) with (2 ^ 64) in Q.
  change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact Q.
- cbn; lia.
- exact (val_mem_of_rdword SEGS _ _ _ _ Hr).
Qed.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable KS : asource_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis MTF : ameter_fs_laws MT.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis ASIL : @asource_img_laws SK SEGS B KS.
Let RET := paj_ret_at (PL := PL_pcap) (PI := PI).
Let RUNF := aj_flag_store_pi B LAWS ML ASF FFL.

(* ---- the caller's data: exactly the shared statement's variables and the premises the tail uses ---- *)
Section t.
Context {STK sp0 : Z} {FP : list (Z * Z)} {ly : alayout} {S : astate} {W0 : world SEGS}
  {mem0 : word -> option byte} {md0 : Model} {own : list (Z * Z)} {lyc : alayout} {Sc : astate}
  {W : world SEGS} {memc : word -> option byte} {mdc : Model} {k : Z} {regs0 : bvmap 5 word}.
(* The stack this call and its callees use below the caller's sp (the image's NX_STK). *)
Context {nstk : Z}.
Context {ps buf cap ts h b p sw lol lvt lvid tsv : Z} {C bj pad : list Z}.
(* The caller's journal and stack window, as the shared statement states them; the machine frame (0x100
   bytes, `addi sp,sp,-0x100` 0x815b8) lies in the window. One hypothesis, so that every lemma below takes
   it as its first argument. *)
Definition nxb_cp : Prop :=
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\
  sp0 - STK <= spZ regs0 - nstk /\ spZ regs0 <= sp0 /\ 256 <= nstk.
Hypothesis HCP : nxb_cp.

#[local] Notation xF fp := (frame_addr lyc AN.NX_CID fp).
#[local] Notation xFL fp := (flag_addr lyc AN.NX_CID fp).
#[local] Notation xSH fp := (shadow_of_addr SHADOW_OFF (frame_addr lyc AN.NX_CID fp)).
#[local] Notation AJ3 fp ly3 S3 W3 mem3 md3 k2 :=
  (ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 ((AN.NX_CID, fp) :: own) ly3 S3 W3 mem3 md3 k2).

(* The bytes the tail writes: the retired-frame magic at F (0x818d4), the frame's eight shadow bytes
   (0x818b8, 0x818bc, 0x818e0..0x818fc) and the flag byte (0x81904). *)
Definition nxb_tail_wr (fp a : Z) : Prop :=
  (xF fp <= a < xF fp + 8) \/ (xSH fp <= a < xSH fp + 8) \/ a = xFL fp.

(* What the run leaves: the `ret` taken to the caller's ra, the journal without the frame (the flag
   store gave it back), the caller's callee-saved registers, a0 = the value a1 had, the descriptor table
   and the file system as they were, and the memory changed only at nxb_tail_wr. *)
Definition nxb_tail_post (fp k2 : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (mem3 : word -> option byte) (md3 : Model) (r : word) : world SEGS -> config -> Prop :=
  fun W2 c2 => W2 = W3 /\ exists regs2 mem2 md2,
    c2 = mkCfg (mkst regs2 (getr regs0 1) mem2 (seg_rom SEGS)) md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly3 (stack_free_state AN.NX_CID fp S3) W3 mem2 md2 k2 /\
    aregs_preserved regs0 regs2 /\ getr regs2 10 = r /\
    m_fds md2 = m_fds md3 /\ m_fs md2 = m_fs md3 /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ nxb_tail_wr fp a ->
       aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) mem3 a) /\
    (forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) mem2 a).

(* The facts about F, its shadow and its flag byte that the tail uses, from the two journals. *)
Lemma nxb_tail_facts : forall fp k2 ly3 S3 W3 mem3 md3,
  AJ3 fp ly3 S3 W3 mem3 md3 k2 ->
  (forall c q, frame_addr ly3 c q = frame_addr lyc c q) /\
  (forall c q, flag_addr ly3 c q = flag_addr lyc c q) /\
  frames S3 = (AN.NX_CID, fp) :: frames Sc /\
  4096 <= xF fp /\ xF fp + 64 <= alloc_ceiling /\ xF fp mod 64 = 0 /\
  in_app (xF fp) 64 /\ off_img (xF fp) 64 /\
  xSH fp = shadow_addr (xF fp) /\ xSH fp = SHADOW_OFF + 8 * (xF fp / 64) /\
  0x7fff8000 <= xSH fp /\ xSH fp + 8 <= 0x10007fff8000 /\
  (xSH fp + 8 <= xF fp \/ xF fp + 64 <= xSH fp) /\
  4096 <= xFL fp /\ xFL fp < alloc_ceiling /\ ~ in_img SEGS (xFL fp) /\
  (xFL fp + 1 <= xF fp \/ xF fp + 64 <= xFL fp) /\
  (xFL fp + 1 <= xSH fp \/ xSH fp + 8 <= xFL fp) /\
  (forall a, xF fp <= a < xF fp + 64 -> apresent (w_H W3) mem3 a /\ ~ aowned B ly3 S3 a) /\
  (forall o, 0 <= o < 8 -> apresent (w_H W3) mem3 (xSH fp + o) /\ ~ aowned B ly3 S3 (xSH fp + o)) /\
  apresent (w_H W3) mem3 (xFL fp) /\ aowned B ly3 S3 (xFL fp) /\
  alloc_ceiling + nstk <= spZ regs0 /\ spZ regs0 <= 2 ^ 47 /\
  0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000.
Proof.
intros fp k2 ly3 S3 W3 mem3 md3 HJ3.
pose proof HCP as (HJ0 & Hwlo & Hwhi & Hnstk).
pose proof HJ0 as (HAR0 & Hly0 & _ & _ & _ & Hfrs0 & _ & _ & _ & _ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof HJ3 as (HAR3 & Hly3 & _ & _ & _ & Hfrs3 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (EFA : forall c q, frame_addr ly3 c q = frame_addr lyc c q).
{ intros c q. unfold frame_addr.
  pose proof Hly3 as (_ & _ & _ & _ & _ & EF3 & _). pose proof Hly0 as (_ & _ & _ & _ & _ & EF0 & _).
  rewrite EF3, EF0. reflexivity. }
assert (EFL : forall c q, flag_addr ly3 c q = flag_addr lyc c q).
{ intros c q. unfold flag_addr.
  pose proof Hly3 as (_ & _ & _ & _ & _ & EF3 & _). pose proof Hly0 as (_ & _ & _ & _ & _ & EF0 & _).
  rewrite EF3, EF0. reflexivity. }
assert (Efr : frames S3 = (AN.NX_CID, fp) :: frames Sc) by (rewrite Hfrs3, Hfrs0; reflexivity).
assert (Hfin3 : In (AN.NX_CID, fp) (frames S3)) by (rewrite Efr; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ AN.NX_CID fp HAR3 Hfin3) as (_ & HFapp & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ AN.NX_CID fp HAR3 Hfin3) as (HF4096 & HFceil & _).
destruct (frame_al64 SEGS B _ _ _ _ _ AN.NX_CID fp HAR3 Hfin3) as (HF64 & _ & _).
pose proof (frm_off_imgP B _ _ _ _ _ AN.NX_CID fp HAR3 Hfin3) as HFimg.
destruct (FFL _ _ _ _ _ AN.NX_CID fp HAR3 Hfin3) as (HFLpres & HFLown & (HFLapp & HFLimg) & (HFL4096 & _ & HFLceil)).
rewrite EFA in HFapp, HFpres, HFSpres, HF4096, HFceil, HF64, HFimg.
rewrite EFL in HFLpres, HFLown, HFLapp, HFLimg, HFL4096, HFLceil.
change (fs_frame_bytes AN.NX_CID) with 64 in *.
change (64 / 8) with 8 in HFSpres.
assert (ESH : xSH fp = shadow_addr (xF fp)) by reflexivity.
assert (EF : xF fp = 64 * (xF fp / 64)) by (pose proof (Z.div_mod (xF fp) 64 ltac:(lia)); lia).
assert (EF8 : xF fp / 8 = 8 * (xF fp / 64)).
{ rewrite EF at 1. replace (64 * (xF fp / 64)) with (8 * (xF fp / 64) * 8) by lia.
  apply Z.div_mul. lia. }
assert (ESHv : xSH fp = SHADOW_OFF + 8 * (xF fp / 64)) by (rewrite ESH; unfold shadow_addr; rewrite EF8; reflexivity).
pose proof HFapp as HFapp'. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp'.
pose proof HFimg as HFimg'. unfold off_img in HFimg'.
assert (HS0 : SHADOW_OFF = 0x7fff8000) by reflexivity.
refine (conj EFA (conj EFL (conj Efr _))).
split; [lia|]. split; [lia|]. split; [exact HF64|]. split; [exact HFapp|]. split; [exact HFimg|].
split; [exact ESH|]. split; [exact ESHv|].
split; [rewrite ESHv, HS0; lia|]. split; [rewrite ESHv, HS0; lia|].
split; [rewrite ESHv, HS0; destruct HFapp' as (_ & [Hlow | [Hhi1 Hhi2]]); [right | left]; lia|].
split; [lia|]. split; [lia|]. split; [exact HFLimg|].
split.
{ destruct (Z_lt_ge_dec (xFL fp) (xF fp)) as [Hlt|Hge]; [left; lia|].
  destruct (Z_lt_ge_dec (xFL fp) (xF fp + 64)) as [Hlt2|Hge2]; [exfalso | right; lia].
  exact (proj2 (HFpres (xFL fp) ltac:(lia)) HFLown). }
split.
{ destruct (Z_lt_ge_dec (xFL fp) (xSH fp)) as [Hlt|Hge]; [left; lia|].
  destruct (Z_lt_ge_dec (xFL fp) (xSH fp + 8)) as [Hlt2|Hge2]; [exfalso | right; lia].
  pose proof (proj2 (HFSpres (xFL fp - xSH fp) ltac:(lia))) as Hno.
  rewrite <- ESH in Hno. replace (xSH fp + (xFL fp - xSH fp)) with (xFL fp) in Hno by lia.
  exact (Hno HFLown). }
split; [exact HFpres|].
split; [intros o Ho; rewrite ESH; exact (HFSpres o Ho)|].
split; [exact HFLpres|]. split; [exact HFLown|].
split; [lia|]. split; [lia|]. exact C1.
Qed.

(* The run to the `ret`, from NP_exit (xe = true) or from NP_x0 (xe = false). The registers it reads:
   a6 = s3 = F, s9 = F's shadow, s0 = the entry sp, a1 = the result, gp and tp; the memory it reads: the
   saved registers and the slot's flag word. *)
Lemma nxb_tail_run : forall (xe : bool) fp k2 ly3 S3 W3 ms3 md3,
  YK0s.ret_ok (getr regs0 1) ->
  AJ3 fp ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  ms_pc_val ms3 = w64 (BASE + (if xe then NP_exit else NP_x0)) -> ms_resv ms3 = None ->
  ms_svc_pending ms3 = None ->
  ms_rom ms3 = seg_rom SEGS -> ms_fregs ms3 = fp_regs -> ms_fcsr ms3 = fp_csr ->
  getr (ms_regs ms3) 8 = w64 (spZ regs0) ->
  getr (ms_regs ms3) 3 = getr regs0 3 -> getr (ms_regs ms3) 4 = getr regs0 4 ->
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (spZ regs0 - 8) = Some (raZ regs0) ->
  (forall j, 0 <= j < 12 ->
     rdword (aview SEGS (w_H W3) (ms_mem ms3)) (spZ regs0 - 16 - 8 * j) =
     Some (bv_unsigned (getr regs0 (Z_to_bv 5 (if j <? 2 then 8 + j else 16 + j))))) ->
  getr (ms_regs ms3) 16 = w64 (xF fp) ->
  getr (ms_regs ms3) 19 = w64 (xF fp) ->
  getr (ms_regs ms3) 25 = w64 (xSH fp) ->
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (xF fp + AN.NX_FLAGPTR) = Some (xFL fp) ->
  SRr SEGS W3 (mkCfg ms3 md3) (nxb_tail_post fp k2 ly3 S3 W3 (ms_mem ms3) md3 (getr (ms_regs ms3) 11)).
Proof.
intros xe fp k2 ly3 S3 W3 ms3 md3 Hraw HJ3 Hpc Hresv Hsvc Hrom Hfregs Hfcsr Rs0 Rgp3 Rtp3 Hra_sv Hsv
  R16 R19 R25 HFLW.
pose proof HCP as (HJ0 & Hwlo & Hwhi & Hnstk).
destruct (nxb_tail_facts fp k2 ly3 S3 W3 (ms_mem ms3) md3 HJ3) as
  (EFA & EFL & Efr3 & HF4096 & HFceil & HF64 & HFapp & HFimg & ESH & ESHv & HSHlo & HSHhi & HdFS &
   HFL4096 & HFLceil & HFLimg & HdFFL & HdFLS & HFpres & HFSpres & HFLpres & HFLown & Hsplo & Hsphi & C1).
assert (EFAly3 : frame_addr ly3 AN.NX_CID fp = xF fp) by (rewrite EFA; reflexivity).
assert (EFLly3 : flag_addr ly3 AN.NX_CID fp = xFL fp) by (rewrite EFL; reflexivity).
assert (Ems3 : ms3 = mkst (ms_regs ms3) (w64 (BASE + (if xe then NP_exit else NP_x0))) (ms_mem ms3) (seg_rom SEGS)).
{ clear - Hpc Hresv Hsvc Hrom Hfregs Hfcsr.
  destruct ms3 as [rg fr pcv svp rv fc mm rm];
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in *.
  subst. reflexivity. }
remember (havoc (havoc (Eimg (Ereg (ms_regs ms3) [])) 528 [Z_to_bv 64 (xFL fp)]) 540
  [getr regs0 1; getr regs0 8; getr regs0 9; getr regs0 18;
   getr regs0 19; getr regs0 20; getr regs0 21; getr regs0 22;
   getr regs0 23; getr regs0 24; getr regs0 25; getr regs0 26;
   getr regs0 27]) as E eqn:HE.
assert (EWlow : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r).
{ intros n r Hn Hr. rewrite HE. rewrite !ew_havoc_old by lia. apply ew_Eimg_Ereg_nat. exact Hr. }
assert (E3 : ew E 3 = getr regs0 3)
  by (rewrite (EWlow 3%nat (3%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)); exact Rgp3).
assert (E4 : ew E 4 = getr regs0 4)
  by (rewrite (EWlow 4%nat (4%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)); exact Rtp3).
assert (E8 : ew E 8 = Z_to_bv 64 (spZ regs0))
  by (rewrite (EWlow 8%nat (8%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)); exact Rs0).
assert (E19 : ew E 19 = Z_to_bv 64 (xF fp))
  by (rewrite (EWlow 19%nat (19%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)); exact R19).
assert (E25 : ew E 25 = Z_to_bv 64 (xSH fp))
  by (rewrite (EWlow 25%nat (25%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)); exact R25).
assert (E11 : ew E 11 = getr (ms_regs ms3) 11)
  by (apply EWlow; [lia | vm_compute; reflexivity]).
assert (E528 : ew E 528 = Z_to_bv 64 (xFL fp)).
{ rewrite HE. rewrite ew_havoc_old by lia.
  exact (ew_havoc_new _ 528 [Z_to_bv 64 (xFL fp)] 0 (Z_to_bv 64 0) ltac:(cbn; lia)). }
assert (E540 : ew E 540 = getr regs0 1) by (rewrite HE; cbn [ew havoc Nat.ltb Nat.leb nth Nat.sub]; reflexivity).
assert (E541 : ew E 541 = getr regs0 8) by (rewrite HE; cbn [ew havoc Nat.ltb Nat.leb nth Nat.sub]; reflexivity).
assert (E542 : ew E 542 = getr regs0 9) by (rewrite HE; cbn [ew havoc Nat.ltb Nat.leb nth Nat.sub]; reflexivity).
assert (E543 : ew E 543 = getr regs0 18) by (rewrite HE; cbn [ew havoc Nat.ltb Nat.leb nth Nat.sub]; reflexivity).
assert (E544 : ew E 544 = getr regs0 19) by (rewrite HE; cbn [ew havoc Nat.ltb Nat.leb nth Nat.sub]; reflexivity).
assert (E545 : ew E 545 = getr regs0 20) by (rewrite HE; cbn [ew havoc Nat.ltb Nat.leb nth Nat.sub]; reflexivity).
assert (E546 : ew E 546 = getr regs0 21) by (rewrite HE; cbn [ew havoc Nat.ltb Nat.leb nth Nat.sub]; reflexivity).
assert (E547 : ew E 547 = getr regs0 22) by (rewrite HE; cbn [ew havoc Nat.ltb Nat.leb nth Nat.sub]; reflexivity).
assert (E548 : ew E 548 = getr regs0 23) by (rewrite HE; cbn [ew havoc Nat.ltb Nat.leb nth Nat.sub]; reflexivity).
assert (E549 : ew E 549 = getr regs0 24) by (rewrite HE; cbn [ew havoc Nat.ltb Nat.leb nth Nat.sub]; reflexivity).
assert (E550 : ew E 550 = getr regs0 25) by (rewrite HE; cbn [ew havoc Nat.ltb Nat.leb nth Nat.sub]; reflexivity).
assert (E551 : ew E 551 = getr regs0 26) by (rewrite HE; cbn [ew havoc Nat.ltb Nat.leb nth Nat.sub]; reflexivity).
assert (E552 : ew E 552 = getr regs0 27) by (rewrite HE; cbn [ew havoc Nat.ltb Nat.leb nth Nat.sub]; reflexivity).
assert (HRO : regs_ok E sr_atoms (ms_regs ms3)).
{ rewrite HE. apply nxb_regs_ok_havoc_hi; [lia|]. apply nxb_regs_ok_havoc_hi; [lia|].
  apply regs_ok_Eimg_Ereg. }
assert (HEI : img_env VAL A_LIM E).
{ rewrite HE. apply img_env_havoc_hi; [|unfold A_LIM; lia].
  apply img_env_havoc_hi; [|unfold A_LIM; lia]. apply Eimg_env. }
assert (H4 : Forall (region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms3))) nxb_regions).
{ unfold nxb_regions.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
    + unfold region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E528, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. replace (xFL fp + o) with (xFL fp) by lia.
      apply (apresent_writable SEGS). exact HFLpres.
    + unfold region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E19, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split.
      * intros o Ho. apply (apresent_writable SEGS). apply (proj1 (HFpres (xF fp + o) ltac:(lia))).
      * apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS E _ (xF fp) 56 8 (SOff 528 0) (xFL fp)).
        -- cbn [sv_denot]. rewrite E528, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
        -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
        -- cbn; lia.
        -- unfold AN.NX_FLAGPTR in HFLW. exact (val_mem_of_rdword SEGS _ _ _ _ HFLW).
    + unfold region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E25, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS). apply (proj1 (HFSpres o ltac:(lia))).
    + unfold region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E8, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
      unfold nxb_saved_chunks.
      apply Forall_cons; [apply (nxb_saved_chunk E _ _ 552%nat _ _ _ E552);
        replace (spZ regs0 + -104) with (spZ regs0 - 16 - 8 * 11) by lia; exact (Hsv 11 ltac:(lia))|].
      apply Forall_cons; [apply (nxb_saved_chunk E _ _ 551%nat _ _ _ E551);
        replace (spZ regs0 + -96) with (spZ regs0 - 16 - 8 * 10) by lia; exact (Hsv 10 ltac:(lia))|].
      apply Forall_cons; [apply (nxb_saved_chunk E _ _ 550%nat _ _ _ E550);
        replace (spZ regs0 + -88) with (spZ regs0 - 16 - 8 * 9) by lia; exact (Hsv 9 ltac:(lia))|].
      apply Forall_cons; [apply (nxb_saved_chunk E _ _ 549%nat _ _ _ E549);
        replace (spZ regs0 + -80) with (spZ regs0 - 16 - 8 * 8) by lia; exact (Hsv 8 ltac:(lia))|].
      apply Forall_cons; [apply (nxb_saved_chunk E _ _ 548%nat _ _ _ E548);
        replace (spZ regs0 + -72) with (spZ regs0 - 16 - 8 * 7) by lia; exact (Hsv 7 ltac:(lia))|].
      apply Forall_cons; [apply (nxb_saved_chunk E _ _ 547%nat _ _ _ E547);
        replace (spZ regs0 + -64) with (spZ regs0 - 16 - 8 * 6) by lia; exact (Hsv 6 ltac:(lia))|].
      apply Forall_cons; [apply (nxb_saved_chunk E _ _ 546%nat _ _ _ E546);
        replace (spZ regs0 + -56) with (spZ regs0 - 16 - 8 * 5) by lia; exact (Hsv 5 ltac:(lia))|].
      apply Forall_cons; [apply (nxb_saved_chunk E _ _ 545%nat _ _ _ E545);
        replace (spZ regs0 + -48) with (spZ regs0 - 16 - 8 * 4) by lia; exact (Hsv 4 ltac:(lia))|].
      apply Forall_cons; [apply (nxb_saved_chunk E _ _ 544%nat _ _ _ E544);
        replace (spZ regs0 + -40) with (spZ regs0 - 16 - 8 * 3) by lia; exact (Hsv 3 ltac:(lia))|].
      apply Forall_cons; [apply (nxb_saved_chunk E _ _ 543%nat _ _ _ E543);
        replace (spZ regs0 + -32) with (spZ regs0 - 16 - 8 * 2) by lia; exact (Hsv 2 ltac:(lia))|].
      apply Forall_cons; [apply (nxb_saved_chunk E _ _ 542%nat _ _ _ E542);
        replace (spZ regs0 + -24) with (spZ regs0 - 16 - 8 * 1) by lia; exact (Hsv 1 ltac:(lia))|].
      apply Forall_cons; [apply (nxb_saved_chunk E _ _ 541%nat _ _ _ E541);
        replace (spZ regs0 + -16) with (spZ regs0 - 16 - 8 * 0) by lia; exact (Hsv 0 ltac:(lia))|].
      apply Forall_cons; [apply (nxb_saved_chunk E _ _ 540%nat _ _ _ E540);
        replace (spZ regs0 + -8) with (spZ regs0 - 8) by lia; exact Hra_sv|].
      apply Forall_nil. }
assert (HS0 : st_ok_pi SEGS VAL E
  (mkSS (if xe then NP_exit else NP_x0) sr_atoms nxb_regions None nxb_tail_G)
  (restrict (w_H W3) ms3)).
{ rewrite Ems3. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - exact HRO.
  - vm_compute; reflexivity.
  - exact H4.
  - unfold nxb_regions; cbn [app pairwise_disjoint all_disjoint];
      unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
      rewrite E528, E19, E25, E8, !unsigned_lit_small by lia;
      repeat split; lia.
  - unfold facts_ok, nxb_tail_G. cbn [f_atoms f_conds f_alias].
    split; [|split; [exact I | exact I]].
    cbn [atoms_ok]. split; [|split; [|exact I]].
    + unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
      rewrite E19, unsigned_lit_small by lia. change (2 ^ 6) with 64.
      split; [lia|]. split; [exact HF64 | lia].
    + unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
      rewrite E528, unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia. }
(* a6 holds F too (the slot 0x68(s1)); `beqz a6` and the load at 0x81900 go through it. *)
lazymatch type of HS0 with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (16%bv : bv 5) (SOff 19 0) HS0
    ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot ms_regs restrict]; rewrite E19, unsigned_lit_small by lia;
          rewrite Z.add_0_r; symmetry; exact R16)) as HS end.
clear HS0.
destruct xe.
all: lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
all: paj_run_flag_sh RUNF HS HJ3.
(* the frame's class is 0 *)
all: try (unfold AN.NX_CID; lia).
(* every byte the run writes is the frame's, its shadow's, or the flag byte *)
1,4: (intros a (r & Hin & Ha);
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      first
      [ exfalso; lia
      | rewrite E528, unsigned_lit_small in Ha by lia; right; rewrite EFLly3; lia
      | rewrite E19, unsigned_lit_small in Ha by lia; left; right; right; right;
        exists AN.NX_CID, fp; split; [left; reflexivity|]; left; unfold in_zr; cbn [fst snd];
        rewrite EFAly3; change (fs_frame_bytes AN.NX_CID) with 64; lia
      | rewrite E25, unsigned_lit_small in Ha by lia; left; right; right; right;
        exists AN.NX_CID, fp; split; [left; reflexivity|]; right; unfold in_zr; cbn [fst snd];
        rewrite EFAly3, <- ESH; change (fs_frame_bytes AN.NX_CID / 8) with 8; lia ]
    | ]);
  destruct Hin).
(* the flag byte reads 0 after the store *)
1,3: nxb_flag0 E528 EFLly3.
(* the `ret` and the post *)
all: prreg HS (1%bv : bv 5) Rra_f; prreg HS (10%bv : bv 5) Ra0_f;
  lazymatch goal with |- SRr _ ?Wx _ _ =>
    eapply (RET Wx _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)) end;
  intros mat2; unfold nxb_tail_post; split; [reflexivity|];
  lazymatch goal with |- exists _ _ _, mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ => exists rg, mm, mdx end.
all: split; [rewrite Rra_f, E540;
    replace (v_jalr (getr regs0 1) 0) with (getr regs0 1) by (symmetry; exact Hraw);
    reflexivity|].
all: split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ3|].
all: split; [apply aregs_preserved_eqs;
    [ prreg HS (2%bv : bv 5) Q2; rewrite Q2, E8; unfold spZ; apply Z_to_bv_bv_unsigned
    | prreg HS (3%bv : bv 5) Q3; rewrite Q3; exact E3
    | prreg HS (4%bv : bv 5) Q4; rewrite Q4; exact E4
    | prreg HS (8%bv : bv 5) Q8; rewrite Q8; exact E541
    | prreg HS (9%bv : bv 5) Q9; rewrite Q9; exact E542
    | prreg HS (18%bv : bv 5) Q18; rewrite Q18; exact E543
    | prreg HS (19%bv : bv 5) Q19; rewrite Q19; exact E544
    | prreg HS (20%bv : bv 5) Q20; rewrite Q20; exact E545
    | prreg HS (21%bv : bv 5) Q21; rewrite Q21; exact E546
    | prreg HS (22%bv : bv 5) Q22; rewrite Q22; exact E547
    | prreg HS (23%bv : bv 5) Q23; rewrite Q23; exact E548
    | prreg HS (24%bv : bv 5) Q24; rewrite Q24; exact E549
    | prreg HS (25%bv : bv 5) Q25; rewrite Q25; exact E550
    | prreg HS (26%bv : bv 5) Q26; rewrite Q26; exact E551
    | prreg HS (27%bv : bv 5) Q27; rewrite Q27; exact E552 ]|].
all: split; [rewrite Ra0_f; exact E11|].
all: split; [destruct md3; reflexivity|].
all: split; [destruct md3; reflexivity|].
all: split; [|intros a Hp; eapply apresent_grows; [exact HG | exact Hp]].
all: intros a Ha Hn; apply (aview_eq_of SEGS); apply HFr; rewrite unsigned_lit_small by lia;
  intros (r & Hin & Hr);
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
  cbn [In] in Hin; unfold nxb_tail_wr in Hn;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      first
      [ lia
      | rewrite E528, unsigned_lit_small in Hr by lia; apply Hn; right; right; lia
      | rewrite E19, unsigned_lit_small in Hr by lia; apply Hn; left; lia
      | rewrite E25, unsigned_lit_small in Hr by lia; apply Hn; right; left; lia ]
    | ]);
  destruct Hin.
Qed.

(* ---- the bytes the tail writes are none of the caller's ---- *)

(* Each of them is below the allocator's ceiling, outside the image, in no block and in no frame the
   caller holds nor in that frame's shadow. *)
Lemma nxb_tail_out : forall fp k2 ly3 S3 W3 mem3 md3 a,
  AJ3 fp ly3 S3 W3 mem3 md3 k2 ->
  ablocks B ly3 S3 = ablocks B lyc Sc ->
  nxb_tail_wr fp a ->
  0 <= a < alloc_ceiling /\ ~ in_img SEGS a /\
  (forall b m, In (b, m) (ablocks B lyc Sc) -> ~ (b <= a < b + req_size m)) /\
  (forall c q, In (c, q) (frames Sc) ->
     ~ in_zr a (frame_rng lyc (c, q)) /\
     ~ in_zr a (shadow_addr (frame_addr lyc c q), fs_frame_bytes c / 8)).
Proof.
intros fp k2 ly3 S3 W3 mem3 md3 a HJ3 Eab Ha.
destruct (nxb_tail_facts fp k2 ly3 S3 W3 mem3 md3 HJ3) as
  (EFA & EFL & Efr3 & HF4096 & HFceil & HF64 & HFapp & HFimg & ESH & ESHv & HSHlo & HSHhi & HdFS &
   HFL4096 & HFLceil & HFLimg & HdFFL & HdFLS & HFpres & HFSpres & HFLpres & HFLown & Hsplo & Hsphi & C1).
pose proof (proj1 HJ3) as HAR3.
assert (HS0 : SHADOW_OFF = 0x7fff8000) by reflexivity.
assert (EF : xF fp = 64 * (xF fp / 64)) by (pose proof (Z.div_mod (xF fp) 64 ltac:(lia)); lia).
pose proof HFapp as HFapp'. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp'.
pose proof HFimg as HFimg'. unfold off_img, YImgTop.IMG_LO in HFimg'.
unfold nxb_tail_wr in Ha.
split; [lia|].
split.
{ intros Hi. pose proof (pa_img_range a Hi) as Hr. pose proof (pa_segs_low a Hi) as Hr2. unfold kLowMemEnd in Hr2.
  unfold pcap_img_end in Hr.
  destruct Ha as [Ha | [Ha | Ha]]; [lia | lia | subst a; exact (HFLimg Hi)]. }
split.
{ intros b0 m Hb Hr. rewrite <- Eab in Hb.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b0 m HAR3 Hb) as (_ & Hb4096 & Hbceil & Hbapp & Hbpres & _).
  pose proof Hbapp as Hbapp'. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp'.
  destruct Ha as [Ha | [Ha | Ha]].
  - pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 mem3 md3 b0 m AN.NX_CID fp HAR3 Hb
      ltac:(rewrite Efr3; left; reflexivity)) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite (EFA AN.NX_CID fp) in Hd.
    change (fs_frame_bytes AN.NX_CID) with 64 in Hd. lia.
  - lia.
  - subst a. exact (proj2 (Hbpres (xFL fp) Hr) HFLown). }
intros c q Hcq. unfold frame_rng, in_zr. cbn [fst snd]. rewrite <- (EFA c q).
assert (Hcq3 : In (c, q) (frames S3)) by (rewrite Efr3; right; exact Hcq).
destruct (al_frames _ _ LAWS _ _ _ _ _ c q HAR3 Hcq3) as (_ & HGapp & HGpres & HGSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ c q HAR3 Hcq3) as (HG4096 & HGceil & _).
destruct (frame_al64 SEGS B _ _ _ _ _ c q HAR3 Hcq3) as (HG64 & HGb64 & HGb).
apply in_split in Hcq as (l1 & l2 & El).
pose proof (sep_frames_pos SEGS B LAWS ly3 S3 W3 mem3 md3 (AN.NX_CID, fp) (c, q) [] l1 l2 HAR3
  ltac:(rewrite Efr3, El; reflexivity)) as Hd.
unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite (EFA AN.NX_CID fp) in Hd.
change (fs_frame_bytes AN.NX_CID) with 64 in Hd.
pose proof HGapp as HGapp'. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HGapp'.
destruct Ha as [Ha | [Ha | ->]].
3: { split; intros Hr.
     - exact (proj2 (HGpres (xFL fp) Hr) HFLown).
     - pose proof (proj2 (HGSpres (xFL fp - shadow_addr (frame_addr ly3 c q)) ltac:(lia))) as Hno.
       replace (shadow_addr (frame_addr ly3 c q) + (xFL fp - shadow_addr (frame_addr ly3 c q)))
         with (xFL fp) in Hno by lia.
       exact (Hno HFLown). }
all: assert (EG : frame_addr ly3 c q = 64 * (frame_addr ly3 c q / 64))
       by (pose proof (Z.div_mod (frame_addr ly3 c q) 64 ltac:(lia)); lia).
all: assert (Enb : fs_frame_bytes c = 64 * (fs_frame_bytes c / 64))
       by (pose proof (Z.div_mod (fs_frame_bytes c) 64 ltac:(lia)); lia).
all: assert (EG8 : frame_addr ly3 c q / 8 = 8 * (frame_addr ly3 c q / 64))
       by (rewrite EG at 1; replace (64 * (frame_addr ly3 c q / 64)) with (8 * (frame_addr ly3 c q / 64) * 8) by lia;
           apply Z.div_mul; lia).
all: assert (Enb8 : fs_frame_bytes c / 8 = 8 * (fs_frame_bytes c / 64))
       by (rewrite Enb at 1; replace (64 * (fs_frame_bytes c / 64)) with (8 * (fs_frame_bytes c / 64) * 8) by lia;
           apply Z.div_mul; lia).
all: assert (ESG : shadow_addr (frame_addr ly3 c q) = 0x7fff8000 + 8 * (frame_addr ly3 c q / 64))
       by (unfold shadow_addr; rewrite EG8, HS0; reflexivity).
all: rewrite ESG, Enb8; split; intros Hr; lia.
Qed.

(* So none of them is a byte the caller's journal lets this call write. *)
Lemma nxb_tail_not_awr : forall fp k2 ly3 S3 W3 mem3 md3 a,
  AJ3 fp ly3 S3 W3 mem3 md3 k2 ->
  ablocks B ly3 S3 = ablocks B lyc Sc ->
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a ->
  ~ nxb_tail_wr fp a.
Proof.
intros fp k2 ly3 S3 W3 mem3 md3 a HJ3 Eab Hw Ht.
destruct (nxb_tail_out fp k2 ly3 S3 W3 mem3 md3 a HJ3 Eab Ht) as (Ha & _ & Hblk & Hfrm).
pose proof HCP as (HJ0 & Hwlo & Hwhi & Hnstk).
pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrs0 & _ & _ & _ & _ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (_ & _ & Hceil & Hslo & _).
destruct Hw as [Hs | [(_ & b0 & n & Hin & Hr) | [(b0 & n & Hin & _ & Hr) | (c & q & Hown & Hr)]]].
- lia.
- exact (Hblk b0 n Hin Hr).
- exact (Hblk b0 n Hin Hr).
- assert (Hcq : In (c, q) (frames Sc)) by (rewrite Hfrs0; apply in_or_app; left; exact Hown).
  destruct (Hfrm c q Hcq) as [H1 H2]. destruct Hr as [Hr | Hr]; [exact (H1 Hr) | exact (H2 Hr)].
Qed.

(* The caller's kept bytes stay kept across the tail's writes. *)
Lemma nxb_kept_tail : forall fp k2 ly3 S3 W3 mem3 md3 mem2 sp (Er : Z -> Prop),
  AJ3 fp ly3 S3 W3 mem3 md3 k2 ->
  ablocks B ly3 S3 = ablocks B lyc Sc ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ nxb_tail_wr fp a ->
     aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) mem3 a) ->
  (forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) mem2 a) ->
  AN.nx_kept SEGS nstk B lyc Sc W memc W3 mem3 sp Er ->
  AN.nx_kept SEGS nstk B lyc Sc W memc W3 mem2 sp Er.
Proof.
intros fp k2 ly3 S3 W3 mem3 md3 mem2 sp Er HJ3 Eab HFR HPR (K1 & K2 & K3 & K4 & K5 & K6).
pose proof HCP as (HJ0 & Hwlo & Hwhi & Hnstk).
pose proof (proj1 HJ0) as HAR0.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [|split; [|split; [|split; [|split]]]].
- intros a Ha Hs HE. rewrite <- (K1 a Ha Hs HE). apply HFR; [lia|]. intros Ht.
  destruct (nxb_tail_out fp k2 ly3 S3 W3 mem3 md3 a HJ3 Eab Ht) as (Ht1 & _). lia.
- intros b0 m i Hb Hi HE. rewrite <- (K2 b0 m i Hb Hi HE).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b0 m HAR0 Hb) as (_ & Hb4096 & Hbceil & _).
  apply HFR; [lia|]. intros Ht.
  destruct (nxb_tail_out fp k2 ly3 S3 W3 mem3 md3 (b0 + i) HJ3 Eab Ht) as (_ & _ & Hblk & _).
  exact (Hblk b0 m Hb ltac:(lia)).
- intros a Hi Hno He. rewrite <- (K3 a Hi Hno He).
  pose proof (pa_segs_low a Hi) as Hr2. unfold kLowMemEnd in Hr2.
  apply HFR; [lia|]. intros Ht.
  destruct (nxb_tail_out fp k2 ly3 S3 W3 mem3 md3 a HJ3 Eab Ht) as (_ & Hni & _).
  exact (Hni Hi).
- intros c q a Hcq Hr HE. rewrite <- (K4 c q a Hcq Hr HE).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ c q HAR0 Hcq) as (Hg4096 & Hgceil & _).
  pose proof (fs_frame_bytes_nonneg c) as Hnn.
  pose proof (shadow_addr_bounds (frame_addr lyc c q) ltac:(lia)) as Hsb1.
  pose proof (shadow_addr_bounds (frame_addr lyc c q + fs_frame_bytes c) ltac:(lia)) as Hsb2.
  pose proof (shadow_range_end (frame_addr lyc c q) (fs_frame_bytes c) Hnn) as Hse.
  apply HFR.
  { unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr. destruct Hr; lia. }
  intros Ht.
  destruct (nxb_tail_out fp k2 ly3 S3 W3 mem3 md3 a HJ3 Eab Ht) as (_ & _ & _ & Hfrm).
  destruct (Hfrm c q Hcq) as [H1 H2]. destruct Hr as [Hr | Hr]; [exact (H1 Hr) | exact (H2 Hr)].
- intros a Ha Hs Hp. apply HPR. exact (K5 a Ha Hs Hp).
- intros a Ha. apply HPR. exact (K6 a Ha).
Qed.

(* The premises of the shared statement the final facts' frame needs: the struct's bounds and the right
   to write it, the buffer block, the timestamp cell and the stream's two blocks. *)
Definition nxb_fp : Prop :=
  4096 <= ps /\ ps + AN.PS_LEN <= 2 ^ 47 /\
  (h <> 0 -> AN.nx_wr_ok nstk B STK sp0 FP ly S lyc Sc own (spZ regs0) ps AN.PS_LEN) /\
  (h <> 0 -> In (buf, AN.nx_bufn cap) (ablocks B lyc Sc) /\ Z.of_nat (length bj) = AN.nx_bufn cap) /\
  (h <> 0 -> ts <> 0 ->
     4096 <= ts /\ ts + 8 <= 2 ^ 47 /\ AN.nx_wr_ok nstk B STK sp0 FP ly S lyc Sc own (spZ regs0) ts 8) /\
  (h <> 0 -> In (h, SRC_FILE_BLOCK) (ablocks B lyc Sc) /\ In (b, Z.of_nat (length C)) (ablocks B lyc Sc)).
Hypothesis HFP : nxb_fp.

#[local] Notation FIN W3 mem3 r :=
  (AN.nx_fin SEGS nstk B KS lyc Sc W memc (spZ regs0) ps buf cap ts h b p sw lol lvt lvid tsv C bj pad W3 mem3 r).

(* The call's final facts (nx_fin) stay true across the tail's writes. *)
Lemma nxb_fin_tail : forall fp k2 ly3 S3 W3 mem3 md3 mem2 r,
  AJ3 fp ly3 S3 W3 mem3 md3 k2 ->
  ablocks B ly3 S3 = ablocks B lyc Sc ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ nxb_tail_wr fp a ->
     aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) mem3 a) ->
  (forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) mem2 a) ->
  FIN W3 mem3 r -> FIN W3 mem2 r.
Proof.
intros fp k2 ly3 S3 W3 mem3 md3 mem2 r HJ3 Eab HFR HPR HF.
pose proof HCP as (HJ0 & Hwlo & Hwhi & Hnstk).
pose proof HFP as (Hps4096 & Hps47 & Hwrps & Hbuf & Hts & Hstream).
pose proof (proj1 HJ0) as HAR0.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HMB : forall a, 0 <= a < 2 ^ 64 -> ~ nxb_tail_wr fp a ->
  mbyte SEGS (rdW W3 mem2) a = mbyte SEGS (rdW W3 mem3) a)
  by (intros a Ha Hn; apply (mbyte_of_aview SEGS); exact (HFR a Ha Hn)).
assert (HNA : forall a, awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a -> ~ nxb_tail_wr fp a)
  by (intros a Hw; exact (nxb_tail_not_awr fp k2 ly3 S3 W3 mem3 md3 a HJ3 Eab Hw)).
assert (HNB : forall b0 m a, In (b0, m) (ablocks B lyc Sc) -> b0 <= a < b0 + req_size m ->
    ~ nxb_tail_wr fp a).
{ intros b0 m a Hb Hr Ht.
  destruct (nxb_tail_out fp k2 ly3 S3 W3 mem3 md3 a HJ3 Eab Ht) as (_ & _ & Hblk & _).
  exact (Hblk b0 m Hb Hr). }
destruct HF as [(Hh & Hr & HK) | (Hh & Hr & HK & HSRC & HPS & (bj' & HGB & Hlen & Hpre) & HTS)].
- left. split; [exact Hh|]. split; [exact Hr|].
  exact (nxb_kept_tail fp k2 ly3 S3 W3 mem3 md3 mem2 _ _ HJ3 Eab HFR HPR HK).
- right. split; [exact Hh|]. split; [exact Hr|].
  split; [exact (nxb_kept_tail fp k2 ly3 S3 W3 mem3 md3 mem2 _ _ HJ3 Eab HFR HPR HK)|].
  destruct (Hstream Hh) as (Hinh & Hinb).
  destruct (Hbuf Hh) as (Hinbuf & HlenBJ).
  split.
  { apply (PcapSourceCloseSpec.asource_at_frame_segs _ KS (rdW W3 mem3) (rdW W3 mem2)); [|exact HSRC].
    intros a Ha. destruct Ha as [Ha | [Ha | Ha]].
    - destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hinh) as (_ & H4 & Hc & _).
      change (req_size SRC_FILE_BLOCK) with 1304 in Hc. unfold SRC_FILE_BLOCK in Ha.
      apply HMB; [lia|]. apply (HNB _ _ a Hinh). change (req_size SRC_FILE_BLOCK) with 1304. lia.
    - destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hinb) as (_ & H4 & Hc & _).
      pose proof (req_size_pos (Z.of_nat (length C)) ltac:(lia)) as [_ Hrq].
      apply HMB; [lia|]. apply (HNB _ _ a Hinb). lia.
    - destruct (asil_env _ _ _ _ ASIL a Ha) as (Hi & _ & _).
      pose proof (pa_segs_low a Hi) as Hr2. unfold kLowMemEnd in Hr2.
      apply HMB; [lia|]. intros Ht.
      destruct (nxb_tail_out fp k2 ly3 S3 W3 mem3 md3 a HJ3 Eab Ht) as (_ & Hni & _).
      exact (Hni Hi). }
  split.
  { destruct HPS as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
    assert (HX : forall x, ps <= x < ps + 24 ->
      mbyte SEGS (rdW W3 mem2) x = mbyte SEGS (rdW W3 mem3) x).
    { intros x Hx. apply HMB; [unfold AN.PS_LEN in Hps47; lia|]. apply HNA. exact (proj1 (Hwrps Hh x Hx)). }
    split; [eapply PcapSourceCloseSpec.vm_frame_segs; [|exact P1]; intros x Hx; apply HX; unfold AN.PS_F_OFF in Hx;
            change (Z.of_nat 8) with 8 in Hx; clear - Hx; lia|].
    split; [eapply PcapSourceCloseSpec.vm_frame_segs; [|exact P2]; intros x Hx; apply HX; unfold AN.PS_SW_OFF in Hx;
            change (Z.of_nat 4) with 4 in Hx; clear - Hx; lia|].
    split; [eapply PcapSourceCloseSpec.vm_frame_segs; [|exact P3]; intros x Hx; apply HX; unfold AN.PS_OL_OFF in Hx;
            change (Z.of_nat 4) with 4 in Hx; clear - Hx; lia|].
    split; [eapply PcapSourceCloseSpec.vm_frame_segs; [|exact P4]; intros x Hx; apply HX; unfold AN.PS_VT_OFF in Hx;
            change (Z.of_nat 4) with 4 in Hx; clear - Hx; lia|].
    split; [eapply PcapSourceCloseSpec.vm_frame_segs; [|exact P5]; intros x Hx; apply HX; unfold AN.PS_VID_OFF in Hx;
            change (Z.of_nat 2) with 2 in Hx; clear - Hx; lia|].
    split; [|exact P7].
    apply (garr8_frame SEGS _ _ _ _ P6). intros x Hx. apply HX. rewrite P7 in Hx.
    change (Z.of_nat 2) with 2 in Hx. clear - Hx. lia. }
  split.
  { exists bj'. split; [|split; [exact Hlen | exact Hpre]].
    apply (garr8_frame SEGS _ _ _ _ HGB). intros x Hx.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hinbuf) as (_ & H4 & Hc & _).
    pose proof (req_size_pos (AN.nx_bufn cap) ltac:(unfold AN.nx_bufn; lia)) as [_ Hrq].
    rewrite Hlen, HlenBJ in Hx.
    apply HMB; [lia|]. apply (HNB _ _ x Hinbuf). lia. }
  intros Hts0. specialize (HTS Hts0).
  destruct (Hts Hh Hts0) as (Hts4096 & Hts47 & Hwrts).
  eapply PcapSourceCloseSpec.vm_frame_segs; [|exact HTS]. intros x Hx. change (Z.of_nat 8) with 8 in Hx.
  apply HMB; [lia|]. apply HNA. exact (proj1 (Hwrts x ltac:(lia))).
Qed.

(* What the run leaves is the call's post: the journal without the frame, at k + EV_NEXT; the caller's
   blocks, frames and meter; and the final facts, kept across the tail's writes. *)
Lemma nxb_tail_close : forall fp k2 ly3 S3 W3 mem3 md3 r W2 c2,
  AJ3 fp ly3 S3 W3 mem3 md3 k2 ->
  k2 = k + AN.EV_NEXT ->
  ablocks B ly3 S3 = ablocks B lyc Sc ->
  mo_le MT Sc S3 0 ->
  m_fds md3 = m_fds mdc -> m_fs md3 = m_fs mdc ->
  FIN W3 mem3 r ->
  nxb_tail_post fp k2 ly3 S3 W3 mem3 md3 r W2 c2 ->
  AN.tpcap_source_next_post SK SEGS nstk B MT KS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
    regs0 ps buf cap ts h b p sw lol lvt lvid tsv C bj pad W2 c2.
Proof.
intros fp k2 ly3 S3 W3 mem3 md3 r W2 c2 HJ3 Hk2 Eab HMLE Hfds Hfs HFIN
  (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & Ha0 & Hfds2 & Hfs2 & HFR & HPR).
pose proof HCP as (HJ0 & Hwlo & Hwhi & Hnstk).
unfold AN.tpcap_source_next_post.
exists ly3, (stack_free_state AN.NX_CID fp S3), regs2, mem2, md2.
split; [reflexivity|].
split; [rewrite <- Hk2; exact HJ2|].
split; [exact HP|].
split; [change (ablocks B ly3 (stack_free_state AN.NX_CID fp S3)) with (ablocks B ly3 S3); exact Eab|].
split.
{ pose proof HJ2 as (_ & _ & _ & _ & _ & Hfr2 & _). pose proof HJ0 as (_ & _ & _ & _ & _ & Hfr0 & _).
  rewrite Hfr2, Hfr0. reflexivity. }
split; [unfold stack_free_state; apply (mo_le_set_fs_r MT MTF); exact HMLE|].
split; [rewrite Hfds2; exact Hfds|].
split; [rewrite Hfs2; exact Hfs|].
rewrite Ha0. exact (nxb_fin_tail fp k2 ly3 S3 W3 mem3 md3 mem2 _ HJ3 Eab HFR HPR HFIN).
Qed.

End t.

(* ---- the two phases ---- *)

(* The caller's journal and window, from nx_base: the window is NX_STK_B = 272 + AFREAD_STK >= 256. *)
Lemma nxb_cp_of_base : forall cx, nx_base SK B KS cx ->
  @nxb_cp (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx) (n_own cx)
    (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) (n_k cx) (n_regs cx) NX_STK_B.
Proof.
intros cx HB.
pose proof HB as (HJ0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwlo & Hwhi & _).
split; [exact HJ0|]. split; [exact Hwlo|]. split; [exact Hwhi|]. unfold NX_STK_B, AFREAD_STK. lia.
Qed.

(* What the run leaves is this call's post: nxb_tail_close at the context's data, with the premises of the
   final facts' frame (nxb_fp) read off nx_base. *)
Lemma nxb_post_at : forall cx fp k2 ly3 S3 W3 mem3 md3 r W2 c2,
  nx_base SK B KS cx ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly3 S3 W3 mem3 md3 k2 ->
  nx_jbk B MT cx k2 ly3 S3 md3 ->
  nx_fin_at B KS cx W3 mem3 r ->
  @nxb_tail_post (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    (n_own cx) (n_lyc cx) (n_regs cx) fp k2 ly3 S3 W3 mem3 md3 r W2 c2 ->
  nx_post SK B MT KS cx W2 c2.
Proof.
intros cx fp k2 ly3 S3 W3 mem3 md3 r W2 c2 HB HJ3 (Hk2 & Eab & HMLE & Hfds & Hfs) HFIN HP.
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hps4096 & Hps47 &
  _ & _ & _ & _ & _ & _ & _ & _ & Hwrps & Hbuf & Hts & Hstream & _).
unfold nx_post. unfold nx_fin_at in HFIN.
refine (nxb_tail_close (nxb_cp_of_base cx HB) _ fp k2 ly3 S3 W3 mem3 md3 r W2 c2 HJ3 Hk2 Eab HMLE Hfds Hfs
  HFIN HP).
unfold nxb_fp.
split; [exact Hps4096|]. split; [exact Hps47|]. split; [exact Hwrps|].
split; [intros Hh; destruct (Hbuf Hh) as (Hin & _ & _ & _ & Hlen & _); exact (conj Hin Hlen)|].
split; [intros Hh Hts0; destruct (Hts Hh Hts0) as (_ & _ & H4096 & H47 & _ & _ & Hwr & _);
        exact (conj H4096 (conj H47 Hwr))|].
intros Hh. destruct (Hstream Hh) as (Hinh & Hinb & _). exact (conj Hinh Hinb).
Qed.

(* NP_x0 (0x818cc) to the `ret`: both readers. *)
Theorem nx_x0_ph : nx_from SK B KS (nx_post SK B MT KS) (nx_x0_inv B MT KS).
Proof.
intros cx fp k2 ly3 S3 W3 ms3 md3 HB HJ3 _ (HBODY & R19 & R16 & HJBK & HFIN).
pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfregs & Hfcsr & (_ & Rs0 & _ & Rgp3 & Rtp3) & (Hra_sv & Hsv) &
  _ & HFLW & _ & _ & R25 & _).
pose proof HB as (_ & _ & Hraw & _).
eapply SRr_mono;
  [exact (nxb_tail_run (nxb_cp_of_base cx HB) false fp k2 ly3 S3 W3 ms3 md3 Hraw HJ3 Hpc Hresv Hsvc Hrom
            Hfregs Hfcsr Rs0 Rgp3 Rtp3 Hra_sv Hsv R16 R19 R25 HFLW)|].
cbv beta. intros W2 c2 _ HP.
exact (nxb_post_at cx fp k2 ly3 S3 W3 (ms_mem ms3) md3 _ W2 c2 HB HJ3 HJBK HFIN HP).
Qed.

(* NP_exit (0x818b4) to the `ret`: the open reader's exits. One run covers 0x818b4..0x818c0 and the x0
   tail, so the phase does not need the x0 phase; nx_exit_from states it in the top's shape. *)
Theorem nx_exit_ph : nx_from SK B KS (nx_post SK B MT KS) (nx_exit_inv B MT KS).
Proof.
intros cx fp k2 ly3 S3 W3 ms3 md3 HB HJ3 _ ((HBODY & _) & R19 & R16 & HJBK & HFIN).
pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfregs & Hfcsr & (_ & Rs0 & _ & Rgp3 & Rtp3) & (Hra_sv & Hsv) &
  _ & HFLW & _ & _ & R25 & _).
pose proof HB as (_ & _ & Hraw & _).
eapply SRr_mono;
  [exact (nxb_tail_run (nxb_cp_of_base cx HB) true fp k2 ly3 S3 W3 ms3 md3 Hraw HJ3 Hpc Hresv Hsvc Hrom
            Hfregs Hfcsr Rs0 Rgp3 Rtp3 Hra_sv Hsv R16 R19 R25 HFLW)|].
cbv beta. intros W2 c2 _ HP.
exact (nxb_post_at cx fp k2 ly3 S3 W3 (ms_mem ms3) md3 _ W2 c2 HB HJ3 HJBK HFIN HP).
Qed.

Theorem nx_exit_from : nx_from SK B KS (nx_post SK B MT KS) (nx_x0_inv B MT KS) ->
  nx_from SK B KS (nx_post SK B MT KS) (nx_exit_inv B MT KS).
Proof. intros _. exact nx_exit_ph. Qed.

End c.
End b.
End a.

(* SK is explicit at every use (as lib/B/Prog/PcapSourceNextDefs.v's nx_from / nx_post). *)
Arguments nx_x0_ph {fx rc} SK {PI}.
Arguments nx_exit_ph {fx rc} SK {PI}.
Arguments nx_exit_from {fx rc} SK {PI}.
