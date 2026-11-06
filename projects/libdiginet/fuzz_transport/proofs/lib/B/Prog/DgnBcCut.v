(* Modified by Theorem Labs, 2026-10: libdiginet/fuzz_frame image B's copy of this unit's image-A cut statements lib/A/Prog/DgnBcCut.v: module paths lib/B (the image-B core's YB1v / YE2k / YCbq / YC5d, the listing names of lib/B/Prog/FrameBSyms.v / FrameBList.v / FrameBPa.v, the B statement texts), the listing instance PI_frameb, and image B's cut offsets (the scan at +0x1f8, the release at +0x2d0). *)
(* DgnBcCut (image B): the cuts of the walk of diginet_body_check (fuzz_decode.asan-ubsan 0x82970 = dgndecb_sigma
   DDB_diginet_body_check, AF_diginet_body_check = 0x2db0 of lib/B/Prog/DgnDecodeBList.v), as STATEMENTS only.
   The walk has four pieces; each proves the cut at its start from the cuts after it:
     +0x000 .. +0x168  the frame, the saves, the realign, the two runtime cells, `jal __asan_stack_malloc_2` (+0x70),
                       the class-2 frame's slots, header and shadow, `jal diginet_cursor_init` (+0x158) and the four
                       constants of the loop (s10 = 1, s11 = 0xf0, s2 = 3, s4 = 0x13): the head, up to bc_loop_stmt;
     +0x16c .. +0x1f4  the loop: `jal diginet_msg_next` (+0x174); a result of 1 runs the sysex test (+0x184 ..
                       +0x1dc: m.status, m.sysex_len, m.sysex (its UBSan null check, +0x198), then the body bytes at
                       m.sysex and m.sysex + 2 (the pointer-overflow check, +0x1b8), each behind a shadow check);
                       another nonzero result goes back to +0x16c; 0 goes to the prefix scan at +0x1f8 (bc_scan_stmt);
                       a refused sysex goes to +0x43c (`li a0, -10`) and the release (bc_rel_stmt);
     +0x1f8 .. +0x2cc  the prefix scan (len >= 4: body[i], body[i + 1], body[i + 3] for i < len - 3, each behind a
                       shadow check and the UBSan pointer checks of body + i, + 1, + 3), to +0x2cc (`li a0, 0`) or
                       +0x43c (`li a0, -10`), then the release;
     +0x2d0 .. +0x438  the release: the shadow of c and m set to 0xf8, the header word 0x45e0360e, the frame's 32
                       shadow bytes set to 0xf5 and its flag byte cleared (the word at frame + 248), the 13 reloads
                       and `ret`.
   Each cut holds the caller's facts (bc_fix), the walk's own journal and the bytes it carries (bc_cur), the
   registers the code after the cut reads (bc_regs_rel, bc_regs_scan, bc_regs_loop), and concludes the statement's
   post at the cut's pc. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0p YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib DgnTransportBCJ.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg diginet_body_check_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require diginet_msg_next_cg.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module BMN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_msg_next_cg.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The three cut points, as offsets from the listing's base. *)
Definition BC_LOOP : Z := AF_diginet_body_check + 0x16c.
Definition BC_SCAN : Z := AF_diginet_body_check + 0x1f8.
Definition BC_REL : Z := AF_diginet_body_check + 0x2d0.
(* The words the prologue saves, as (distance below the entry sp, register): ra, s0, s1, s2 .. s11. *)
Definition BC_SAVED : list (Z * Z) :=
  [(8, 1); (16, 8); (24, 9); (32, 18); (40, 19); (48, 20); (56, 21); (64, 22); (72, 23); (80, 24);
   (88, 25); (96, 26); (104, 27)].
(* The class-2 frame's size (fs_frame_bytes 2). *)
Definition BC_FBYTES : Z := 256.

Section cut. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* The facts of the record every piece uses (premises of transport_diginet_body_check_cg_holds_stmt), the record's
   facts that no byte of G_HARNESS_B or TRANS_RO_RD is an owned static or errno last (trans_src_ok_acall carries a
   body in G or TRANS_RO_RD across diginet_msg_next with them). *)
Definition bc_laws : Prop :=
  transport_cells B /\ AR_laws segs B /\ ameter_laws MT /\ ameter_fs_laws MT /\
  astack_free_law segs B /\ frame_flag_lawP segs B /\
  (trans_g_unowned B /\ trans_g_no_errno B /\ trans_ro_rd_unowned B /\ trans_rom_no_errno B).

(* The caller's facts (the premises of decode_diginet_body_check_cg at entry regs), and what the walk fixes before
   the first cut: sp1, the realigned stack pointer; pos, the slot of the class-2 frame the stack malloc gave; F,
   the frame's address. *)
Definition bc_fix (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model) (k : Z)
    (regs : bvmap 5 word) (body : Z) (bb : list byte) (pos sp1 F : Z) : Prop :=
  @ajournal rc tfib_sink_head segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\
  YK0s.ret_ok (YK11.getr regs 1) /\ 4096 <= raZ regs /\
  YK11.getr regs 3 = w64 (as_gp B) /\ YK11.getr regs 4 = w64 (as_tp B) /\
  spZ regs mod 16 = 0 /\ sp0 - STK <= spZ regs - TRANS_BC_STK /\ spZ regs <= sp0 /\
  (body <> 0 \/ length bb = 0%nat) /\
  ((0 < length bb)%nat -> trans_src_ok B lyc Sc W memc body (Z.of_nat (length bb)) /\
     decode_off_win regs TRANS_BC_STK body (Z.of_nat (length bb))) /\
  count_cid TRANS_BC_CID (frames Sc) < fs_frames TRANS_BC_CID /\
  st_nev S + k + TRANS_BC_EV <= EV_MAX /\
  sp1 = 32 * ((spZ regs - TRANS_BC_FRAME) / 32) /\
  F = frame_addr lyc TRANS_BC_CID pos /\
  4096 <= F /\ F mod 32 = 0 /\ F + BC_FBYTES <= alloc_ceiling /\ in_app F BC_FBYTES.

(* The state at a cut: the walk's own journal (started at entry with this function's stack budget and no
   footprint; its own list is the class-2 frame), the caller's blocks, the meter, the 13 saved words, the two
   slots the code after the cut reads (len at sp1 + 16, the frame at sp1 + 24), the frame's flag pointer (its last
   word), the body bytes, and, when there are some, where they lie at the cut's state (trans_src_ok). *)
Definition bc_cur (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model)
    (regs : bvmap 5 word) (body : Z) (bb : list byte) (pos sp1 F : Z)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) : Prop :=
  @ajournal rc tfib_sink_head segs B TRANS_BC_STK (spZ regs) [] lyc Sc W memc mdc
    [(TRANS_BC_CID, pos)] ly2 S2 W2 mem2 md2 0 /\
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
  mo_le MT Sc S2 0 /\
  Forall (fun o : Z * Z => rdword (aview segs (w_H W2) mem2) (spZ regs - fst o) =
      Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) BC_SAVED /\
  rdword (aview segs (w_H W2) mem2) (sp1 + 16) = Some (Z.of_nat (length bb)) /\
  rdword (aview segs (w_H W2) mem2) (sp1 + 24) = Some F /\
  rdword (aview segs (w_H W2) mem2) (F + BC_FBYTES - 8) = Some (flag_addr lyc TRANS_BC_CID pos) /\
  garr8 segs (mrestrict (w_H W2) mem2) body (map bz bb) /\
  ((0 < length bb)%nat -> trans_src_ok B ly2 S2 W2 mem2 body (Z.of_nat (length bb))).

(* The registers the release reads: sp = sp1, gp, tp, s0 = the entry sp, s1 = sp1, s7 = the frame's shadow
   address, s8 = the frame. *)
Definition bc_regs_rel (regs regs2 : bvmap 5 word) (sp1 F : Z) : Prop :=
  YK11.getr regs2 2 = w64 sp1 /\ YK11.getr regs2 3 = YK11.getr regs 3 /\ YK11.getr regs2 4 = YK11.getr regs 4 /\
  YK11.getr regs2 8 = w64 (spZ regs) /\ YK11.getr regs2 9 = w64 sp1 /\
  YK11.getr regs2 23 = w64 (SHADOW_OFF + F / 8) /\ YK11.getr regs2 24 = w64 F.
(* The scan also reads s3 = body and s9 = the shadow base. *)
Definition bc_regs_scan (regs regs2 : bvmap 5 word) (body sp1 F : Z) : Prop :=
  bc_regs_rel regs regs2 sp1 F /\ YK11.getr regs2 19 = w64 body /\ YK11.getr regs2 25 = w64 SHADOW_OFF.
(* The loop also reads s5 = c, s6 = m and the four constants s2 = 3, s4 = 0x13, s10 = 1, s11 = 0xf0. *)
Definition bc_regs_loop (regs regs2 : bvmap 5 word) (body sp1 F : Z) : Prop :=
  bc_regs_scan regs regs2 body sp1 F /\
  YK11.getr regs2 18 = w64 3 /\ YK11.getr regs2 20 = w64 19 /\
  YK11.getr regs2 21 = w64 (F + 32) /\ YK11.getr regs2 22 = w64 (F + 96) /\
  YK11.getr regs2 26 = w64 1 /\ YK11.getr regs2 27 = w64 240.

(* The shadow bytes the head wrote 0 for c (granules 4 .. 7 of the frame) and m (granules 12 .. 16). *)
Definition bc_cm_zero (W2 : world segs) (mem2 : word -> option byte) (F : Z) : Prop :=
  forall i, (4 <= i < 8 \/ 12 <= i < 17) -> aview segs (w_H W2) mem2 (SHADOW_OFF + F / 8 + i) = Some 0.

(* The walk's own journal with no footprint keeps the bytes of a range trans_src_ok places outside its stack window
   (a heap block: the block clause, the block is still live as the footprint is empty; a side-stack frame of the
   caller: the frame clause; G and TRANS_RO_RD: the image clause, with the record's facts; the machine stack: the
   clause at or above alloc_ceiling), and the placement holds at the journal's state (trans_src_ok_inner, with
   decode_rd_ok there: decode_rd_ok_fake_kept, stack_zshadow_ra, trans_sh_any). *)
Lemma bc_src_journal : AR_laws segs B -> trans_g_unowned B -> trans_g_no_errno B ->
  trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  forall STK sp0 own lyc Sc (W : world segs) memc mdc ly2 S2 (W2 : world segs) mem2 md2 k q n,
  AR segs B lyc Sc W memc mdc ->
  @ajournal rc tfib_sink_head segs B STK sp0 [] lyc Sc W memc mdc own ly2 S2 W2 mem2 md2 k ->
  trans_src_ok B lyc Sc W memc q n -> 0 < n -> (q + n <= sp0 - STK \/ sp0 <= q) ->
  trans_src_ok B ly2 S2 W2 mem2 q n /\
  (forall a, q <= a < q + n -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).
Proof.
  intros LAWS HGU HGE HRU HRE STK sp0 own lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k q n HAR HJ Hs Hn Hoff.
  destruct HJ as (HAR2 & Hly & _ & _ & _ & Hfrs & _ & _ & KW & KB & KI & KF & KG & _ & _ & _ & _).
  destruct Hly as (_ & _ & _ & _ & _ & ELF & _ & _ & _ & Elo & Ehi & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (DEC : forall x y : Z * Z, {x = y} + {x <> y}) by (decide equality; apply Z.eq_dec).
  assert (Hbl : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2)).
  { intros [p m] Hin. destruct (in_dec DEC (p, m) (ablocks B ly2 S2)) as [H|H]; [exact H|].
    exfalso. destruct (al_blocks _ _ LAWS lyc Sc W memc mdc p m HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn0).
    pose proof (req_size_pos m (proj1 Hn0)) as [Hr _].
    exact (inFP_nil _ (KG p m 0 Hin H ltac:(lia))). }
  assert (Hf : forall f, In f (frames Sc) -> In f (frames S2))
    by (intros f Hf; rewrite Hfrs; apply in_or_app; right; exact Hf).
  assert (Hfa : forall cid pos, frame_addr ly2 cid pos = frame_addr lyc cid pos)
    by (intros cid pos; unfold frame_addr; rewrite ELF; reflexivity).
  assert (FS : forall a, @fp_spares tfib_sink_head [] a)
    by (intros a Ho; destruct Ho as (r & Hr & _); destruct Hr).
  assert (KV : forall a, q <= a < q + n -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).
  { intros a Ha. destruct Hs as [(bA & nA & Hin & B1 & B2) | (HL & _)].
    - destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bA nA HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn0).
      pose proof (req_size_pos nA (proj1 Hn0)) as [_ Hreq].
      replace a with (bA + (a - bA)) by lia.
      exact (KB bA nA (a - bA) Hin (Hbl _ Hin) ltac:(lia) (inFP_nil _)).
    - destruct HL as [(cid & pos & Hin & F1 & F2) | [(HG & _) | [(S1 & S3) | (HR & _)]]].
      + apply (KF cid pos a Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | exact (inFP_nil _)].
      + pose proof (HG a Ha) as Ga. exact (KI a (trans_g_img a Ga) (HGU a Ga) (HGE a Ga) (FS a)).
      + destruct (trans_stk_bounds B lyc Sc W memc mdc HAR) as [T1 T2]. apply KW; lia.
      + pose proof (HR a Ha) as Ra. destruct (trans_ro_rd_scoped B HRU HRE a Ra) as [Ho He].
        exact (KI a (trans_ro_img a Ra) Ho He (FS a)). }
  split; [|exact KV].
  destruct Hs as [(bA & nA & Hin & B1 & B2) | (HL & Hrd)].
  - left. exists bA, nA. split; [exact (Hbl _ Hin) | lia].
  - assert (Hrd2 : decode_rd_ok W2 mem2 q n).
    { destruct HL as [HF | [(_ & Hsh) | [(S1 & S3) | (_ & Hsh)]]].
      - apply (decode_rd_ok_fake_kept B LAWS lyc Sc W W2 memc mem2 mdc q n HAR HF Hrd Hn KV).
        intros cid pos s Hin Hs'. exact (KF cid pos s Hin (or_intror Hs') (inFP_nil _)).
      - destruct (Hsh ly2 S2 W2 mem2 md2 HAR2) as [Ha Hh]. exact (trans_rd_ok_sh W W2 memc mem2 q n Hrd KV Ha Hh).
      - destruct (stack_zshadow_ra B ly2 S2 W2 mem2 md2 q n HAR2 Hn ltac:(rewrite Elo; lia) ltac:(rewrite Ehi; lia))
          as [Ha Hh].
        exact (trans_rd_ok_sh W W2 memc mem2 q n Hrd KV Ha Hh).
      - destruct (Hsh ly2 S2 W2 mem2 md2 HAR2) as [Ha Hh]. exact (trans_rd_ok_sh W W2 memc mem2 q n Hrd KV Ha Hh). }
    exact (trans_src_ok_inner B lyc Sc W memc ly2 S2 W2 mem2 q n Hbl Hf Hfa Elo Ehi Hrd2 (or_intror (conj HL Hrd))).
Qed.

(* The release, +0x2d0 .. +0x438: from a0 = body_check bb, the post. *)
Definition bc_rel_stmt : Prop :=
  bc_laws ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (body : Z) (bb : list byte)
         (pos sp1 F : Z) (W2 : world segs) (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model)
         (ly2 : alayout) (S2 : astate),
    bc_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs body bb pos sp1 F ->
    bc_cur lyc Sc W memc mdc regs body bb pos sp1 F ly2 S2 W2 mem2 md2 ->
    bc_regs_rel regs regs2 sp1 F ->
    YK11.getr regs2 10 = w64 (body_check bb) ->
    SRr segs W2 (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + BC_REL)) mem2 (YK11.seg_rom segs)) md2)
      (@trans_bc_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs bb).

(* The prefix scan, +0x1f8 .. +0x2cc / +0x43c, then the release. *)
Definition bc_scan_stmt : Prop :=
  bc_laws ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (body : Z) (bb : list byte)
         (pos sp1 F : Z) (W2 : world segs) (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model)
         (ly2 : alayout) (S2 : astate),
    bc_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs body bb pos sp1 F ->
    bc_cur lyc Sc W memc mdc regs body bb pos sp1 F ly2 S2 W2 mem2 md2 ->
    bc_regs_scan regs regs2 body sp1 F ->
    SRr segs W2 (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + BC_SCAN)) mem2 (YK11.seg_rom segs)) md2)
      (@trans_bc_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs bb).

(* The loop head, +0x16c: the cursor at c = F + 32 holds (body, len, cp, st), m = F + 96 holds 40 bytes mj, and
   their shadow bytes read 0. *)
Definition bc_loop_stmt : Prop :=
  bc_laws ->
  (forall fx' : YK11.FPState, @BMN.transport_diginet_msg_next_cg fx' rc B MT (transportb_sigma TB_diginet_msg_next)) ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (body : Z) (bb : list byte)
         (pos sp1 F : Z) (W2 : world segs) (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model)
         (ly2 : alayout) (S2 : astate) (cp : nat) (st : Z) (mj : list byte),
    bc_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs body bb pos sp1 F ->
    bc_cur lyc Sc W memc mdc regs body bb pos sp1 F ly2 S2 W2 mem2 md2 ->
    bc_regs_loop regs regs2 body sp1 F ->
    (cp <= length bb)%nat -> st_ok st ->
    garr8 segs (mrestrict (w_H W2) mem2) (F + 32)
      (BMN.trans_mn_cur_bytes body (Z.of_nat (length bb)) cp st) ->
    length mj = 40%nat ->
    garr8 segs (mrestrict (w_H W2) mem2) (F + 96) (map bz mj) ->
    bc_cm_zero W2 mem2 F ->
    SRr segs W2 (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + BC_LOOP)) mem2 (YK11.seg_rom segs)) md2)
      (@trans_bc_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs bb).
End cut.
