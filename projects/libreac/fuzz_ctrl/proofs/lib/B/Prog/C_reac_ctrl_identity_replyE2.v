(* lib/B/Prog/C_reac_ctrl_identity_replyE2.v -- fuzz_ctrl image B (asan-ubsan, libreac v1.9.0): E2 of the cgif-form glue
   pb_reac_ctrl_identity_reply (reac_ctrl_identity_reply, 0x848fc), the call of reac_ctrl_parse (jal at 0x84a64, return
   0x84a68), in cgif continuation form.  Independent of S-B's journal: it starts from the journal AT THE CALL STATE.

   rule 24: no function proved here.  Released-proof lookup of record
   (`proof-index reac_ctrl_identity_reply reac_ctrl_identity_reply_contract_F`,
   lookup-reac_ctrl_identity_reply.txt (a working note, not in this delivery), checker a Theorem Labs lane CONFIRM in
   lookup-check.md (a working note, not in this delivery)): At ossv/recipes c5e779efe8c (2026-10-31), no released proof of the function by name or
   address outside this unit.  Written new.

   THE INTERFACE (the lead's composition meets this file on exactly these two names; shape of a Theorem Labs lane's
   cmPf_sm2_ret, lib/B/Prog/C_reac_box_catalogue_matchPf.v:299):
     rrB_E2_ret   what the stretch after the call (S-C) receives at parse's return 0x84a68, in BOTH forms:
                  (a) cgif: the journal at ((1, pos) :: own) and treac_ctrl_parse_post's conjuncts;
                  (b) the registers at the return, aregs_preserved spelled out;
                  (c) ctrl: the conversion's conclusions over VISIBLE addresses only (decisions.md item 19 / 19a):
                      the 36 bytes at G + 32 as bytes_at / rw_cells, the visible keep ctl_kept_vis and the visible
                      writability ctl_wmono_vis_off_img over the classes the call keeps, and stk of the window below
                      the call's sp.  Never raw munch / wmono.
     rrB_E2_stmt  from the journal at the call state to SRr at the call config, with the continuation over rrB_E2_ret.
   The call state is the left disjunct of C_reac_ctrl_identity_replyLib.rrB_QSB (lead, 65edc77b393): pc 0x83e04
   (REAC_CTRL_PARSE), ra = 0x84a68, sp = rA S, a0 = fr, a1 = len, a2 = G + 32, s0 = S, s1 = rA S, s2 = s10 = G, s3 = pn,
   s4 = pp, s5 = fr, s6 = pa, s7 = len, s8 = G + 32, s9 = G / 8 + ASAN_K, s11 = wa ASAN_K, with G = fs_frame FS 1 jj =
   frame_addr lyc 1 pos (B.ProgWorld.ctl_fs_geom).

   WHY ctl_kept_vis / ctl_wmono_vis_off_img AND NOT munch_vis / wmono_vis.  The callee post is view-level (aview,
   acall_kept), and parse takes and releases its OWN class-1 fake frame, which is not a frame of the call state; so
   munch_vis over parse's write list and the unrestricted wmono_vis are NOT derivable from the post (a Theorem Labs lane,
   ctl-post-callees.md section 0.4 (a) / (b), lines 149-177; section 6.3 table, lines 808 and 810 (a working note, not in this delivery)).  The
   derivable visible forms are mrd equality / writability at the visible addresses of the classes acall_kept keeps
   (same file, K1 / K2, lines 110-119).  The class used is B.ProgWorld.kept_class (lib/B/ProgWorld.v:669), the class
   of exactly acall_kept's four view clauses (YCbq.v:826-833), with the core's alloc_ceiling; see ctl_post below.

   THE CONVERSION ctl_post_reac_ctrl_parse (a NAMED Section hypothesis below; OWNER PENDING: a Theorem Labs lane
   lib/B/ProgWorld.v).  Text: a Theorem Labs lane's DRAFT ctl_post_reac_ctrl_parse_stmt, ctl-post-callees.md section 6.3, lines 775-800 (a working note, not in this delivery)
   (a Theorem Labs lane's lib/A/ProgWorld.v on a working branch 1d23ced37fd has NO
   statement for parse: its only mention is the comment at :392).  Transcribed to image B: segs := YB1v.tfibsegs,
   A.Img0.rsegs -> B.Img0.rsegs, Lib.X -> lib.Lib.X, ctl_out_bytes_stmt / ctl_kept_vis / ctl_wmono_vis_off_img ->
   B.ProgWorld's (lib/B/ProgWorld.v:929-947, the same texts).  Three changes, each needed for the statement to be TRUE
   and USABLE with the post it converts:
     (1) a Theorem Labs lane's placeholder `<kept clauses>` (ctl-post-callees.md line 788 (a working note, not in this delivery), "acall_kept ... spelled out as the six clauses of section 0.1")
         is acall_kept itself (YCbq.v:824-835 IS those six clauses), over lyc Sc in place of bl / frs / fra;
     (2) the conclusion's class is B.ProgWorld.kept_class (ProgWorld.v:669-679), not ctl_kept_cls: ctl_kept_cls
         (ProgWorld.v:930-941; also a Theorem Labs lane's text, not in this delivery) named, before its change at :921-925, lib.Reusable.YK06.alloc_ceiling = 0x7fff7f800000, the LOWEST
         ceiling, while acall_kept's clause (1) and astk_ok name the core's RunCeil field lib.Reusable.YM05.alloc_ceiling
         (YCbq.v:467-469: 0x7fff7f800000 <= alloc_ceiling), so a ctl_kept_cls conclusion would claim bytes in
         [0x7fff7f800000, alloc_ceiling) that no premise keeps; kept_class is ProgWorld's own class for acall_kept
         (ctl_post_acall_kept, ProgWorld.v:681, PROVED, concludes over it);
     (3) the premise `wle W W2` is added (the post's SRr gives it): without it an address visible in W but hidden in
         W2 keeps no view and the visible keep does not follow (ctl_post_acall_kept takes the same premise).
   Its premise `alloc_ceiling <= lo` is likewise the core's ceiling.
   The text so changed is PROVED here from B.ProgWorld's proved pieces (rrB_ctl_post_reac_ctrl_parse, after the
   interface; a Theorem Labs lane's own table marks each conclusion DERIVABLE, ctl-post-callees.md:805-811 (a working note, not in this delivery)).  rrB_E2 keeps the named
   hypothesis as the brief asks; rrB_E2_parse (end of file) is rrB_E2 with it discharged, TPARSE its one premise.

   OTHER NAMED HYPOTHESES (Section E2):
     TPARSE  C_reac_ctrl_parse.treac_ctrl_parse_spec at SEGS := YB1v.tfibsegs, passed EXPLICITLY (a5 keeps SEGS a
             Section Variable, as a Theorem Labs lane's classify does) - OWNER PENDING: a Theorem Labs lane, pb_reac_ctrl_parse (not Qed).
   PROVED facts used, not assumed: B.ProgWorld.ctl_out_bytes (ProgWorld.v:947), B.ProgWorld_Fs.ctl_frame_above_img
   (ProgWorld_Fs.v:531), B.ProgBridge.rsegs_spans (ProgBridge.v:81), RcParse.ctrlparse_length (RcParse.v:77).

   THE PROOF rrB_E2 : rrB_E2_stmt (Qed): YA0n.SRr_bind over TPARSE at the call registers (own' holds the frame
   (1, pos), so afobj / awr_byte for [G + 32, G + 68) are decided here), then ctl_post_reac_ctrl_parse on the
   post.  a Theorem Labs lane's caller-side lemmas rcpB_keep / rcpB_wkeep (from a working branch c3b01f505c2) (at head
   lib/B/Prog/C_reac_ctrl_parseLib.v:2313 / :2328) are neither used nor copied here: E2 has no pre- or post-call munch
   of its own.  rrB_E2_ret's ctl_kept_vis IS rcpB_keep's middle premise (the call's visible keep, K := kept_class ..),
   for the composer that chains S-B, E2 and S-C; rcpB_wkeep's middle premise is the unrestricted wmono_vis, which the
   post does not give (a Theorem Labs lane's ctl-post-callees.md section 0.4 (b) (a working note, not in this delivery)): the composer uses ctl_wmono_vis_off_img on the kept off-image classes.

   Image A is not Required.  Every unit module is Required qualified; the core copies of the six doubled modules
   (YI04 YI16 YK11 YK1b YM05 YO09) from the lib.Reusable path; the lib/Lib twins written lib.Lib.X. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YM05 YI16 YK0s YK04 YA0n.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG00 YG01 YG0f YG0n YG0v YG0d YCbq YE01 APostBase.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YB1v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Mem Frame Cells Step PropExec.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Img0 AsanRT ProgBridge ProgWorld ProgWorld_Fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcParse.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require reac_ctrl_parse_c C_reac_ctrl_parse.
(* rA (the aligned frame base of the function, (S - 128) / 32 * 32), from the generated copy of record (unit decision
   125), as C_reac_ctrl_identity_replyLib.rrB_QSB names it. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require reac_ctrl_identity_replyRB.
Import ListNotations.
Open Scope Z_scope.

#[local] Notation segs := lib.Reusable.YB1v.tfibsegs (only parsing).
#[local] Notation rsegs := lib.B.Img0.rsegs (only parsing).
#[local] Notation rA := lib.B.Prog.reac_ctrl_identity_replyRB.rA (only parsing).
#[local] Notation K_PARSE := lib.B.Prog.C_reac_ctrl_parse.REAC_CTRL_PARSE_STK (only parsing).

Section E2.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {SK : lib.Reusable.YI16.sink_head}.
Variable B : lib.Reusable.YG0f.asyms.
(* arodata_okS's read-only span, as C_reac_ctrl_identity_reply.treac_ctrl_identity_reply_spec and
   C_reac_ctrl_parse.treac_ctrl_parse_spec take it (decisions.md item 17). *)
Variables RLO RHI : Z.

(* ---- The conversion, image-B text (see the header for the source lines and the three changes). ---- *)
Definition ctl_post_reac_ctrl_parse_stmt : Prop :=
  lib.B.ProgWorld.ctl_out_bytes_stmt ->
  forall (lyc : lib.Reusable.YG0f.alayout) (Sc : lib.Reusable.YG00.astate) (W W2 : lib.Reusable.YA0n.world segs)
         (memc mem2 : word -> option byte) (regs regs2 : bvmap 5 word) (lo sp K o kres : Z) (out : list byte),
    lib.Reusable.YG0d.aregs_preserved regs regs2 ->                                                   (* ctl-post-callees.md (a working note, not in this delivery) *)
    lib.Reusable.YK11.getr regs2 10 = lib.Reusable.YG0d.w64 kres ->                                   (* ctl-post-callees.md (a working note, not in this delivery) *)
    length out = 36%nat ->                                                                            (* ctl-post-callees.md (a working note, not in this delivery) *)
    (o <> 0 -> forall i, (i < 36)%nat ->
       lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W2) mem2 (o + Z.of_nat i) =
       Some (bv_unsigned (nth i out (Z_to_bv 8 0)))) ->                                               (* ctl-post-callees.md (a working note, not in this delivery) *)
    lib.Reusable.YCbq.acall_kept segs B lyc Sc W memc W2 mem2 (sp - K) sp (fun a => o <= a < o + 36) -> (* ctl-post-callees.md (a working note, not in this delivery), (1) *)
    lib.Reusable.YA0n.wle W W2 ->                                                                     (* (3) *)
    0 <= o -> o + 36 <= 2 ^ 64 ->                                                                     (* ctl-post-callees.md (a working note, not in this delivery) *)
    (o <> 0 -> forall i, (i < 36)%nat -> ~ lib.Reusable.YG0d.in_img segs (o + Z.of_nat i)) ->         (* ctl-post-callees.md (a working note, not in this delivery) *)
    lib.Reusable.YM05.alloc_ceiling <= lo -> lo <= sp - K -> sp <= 2 ^ 64 ->                          (* ctl-post-callees.md (a working note, not in this delivery) *)
    (forall a, lo <= a < sp - K -> lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) memc a) ->    (* ctl-post-callees.md (a working note, not in this delivery) *)
    lib.Reusable.YK11.getr regs2 10 = Z_to_bv 64 kres /\                                              (* ctl-post-callees.md (a working note, not in this delivery) *)
    (o <> 0 -> lib.Lib.Mem.bytes_at rsegs mem2 o out /\
               lib.Lib.Step.rw_cells rsegs mem2 o (lib.Lib.Cells.CB 36 out :: nil)) /\                  (* ctl-post-callees.md (a working note, not in this delivery) *)
    lib.B.ProgWorld.ctl_kept_vis (lib.Reusable.YA0n.w_H W) memc mem2
      (lib.B.ProgWorld.kept_class B lyc Sc (sp - K) sp (fun a => o <= a < o + 36)) /\                (* ctl-post-callees.md (a working note, not in this delivery), (2) *)
    lib.B.ProgWorld.ctl_wmono_vis_off_img (lib.Reusable.YA0n.w_H W) memc mem2
      (lib.B.ProgWorld.kept_class B lyc Sc (sp - K) sp (fun a => o <= a < o + 36)) /\                (* ctl-post-callees.md (a working note, not in this delivery), (2) *)
    lib.Lib.Frame.stk rsegs mem2 lo sp.                                                               (* ctl-post-callees.md (a working note, not in this delivery) *)

(* ==== THE INTERFACE (1/2): what the stretch after the call receives at parse's return 0x84a68.  The world walk
   stands at mkCfg (mkst regs2 (Z_to_bv 64 0x84a68) mp (seg_rom rsegs)) md2, in world W2, entered at the call
   config in world W with the call memory m5 and the journal base (ly, S0, W0, mem0, md0), STK / sp0 / FP the
   caller's, own' = (1, pos) :: own (the function's class-1 frame held across the call), the call state (lyq, Sq).
   G is the function's class-1 frame (G = frame_addr lyq 1 pos), its 36 bytes at G + 32 parse's output.
   (a) cgif: the journal to the return state and treac_ctrl_parse_post's conjuncts (C_reac_ctrl_parse.v:49-57) at
       n := len, o := G + 32, fr := g, spZ := rA S; wle from the post's SRr; the output clause without its o <> 0
       guard (G + 32 <> 0).  a0 = w64 (fst (ctrlparse len g)) is also the ctrl form's a0 (w64 = Z_to_bv 64).
   (b) the registers at the return: aregs_preserved of the call registers, spelled out (sp = rA S, gp, tp, s0 = S,
       s1 = rA S, s2 = G, s3 = pn, s4 = pp, s5 = fr, s6 = pa, s7 = len, s8 = G + 32, s9 = G / 8 + ASAN_K, s10 = G,
       s11 = wa ASAN_K).  The world rule leaves every other register, ra included, unconstrained.
   (c) ctrl, visible addresses only: the 36 bytes, the visible keep and visible writability from the call memory m5
       to mp over the classes the call keeps (parse's window [rA S - 8800, rA S) and its output excluded), and stk of
       the function's window below the call's sp, [S - 9072, rA S). ==== *)
Definition rrB_E2_ret (STK sp0 : Z) (FP : list (Z * Z)) (ly : lib.Reusable.YG0f.alayout) (S0 : lib.Reusable.YG00.astate)
    (W0 : lib.Reusable.YA0n.world rsegs) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (pos : Z)
    (lyq : lib.Reusable.YG0f.alayout) (Sq : lib.Reusable.YG00.astate) (W : lib.Reusable.YA0n.world rsegs)
    (m5 : word -> option byte) (k : Z) (gp tp : word) (fr len pa pp pn S G : Z) (g : list byte)
    (W2 : lib.Reusable.YA0n.world rsegs) (ly2 : lib.Reusable.YG0f.alayout) (S2 : lib.Reusable.YG00.astate)
    (regs2 : bvmap 5 word) (mp : word -> option byte) (md2 : Model) : Prop :=
  (* (a) *)
  lib.Reusable.YA0n.wle W W2 /\
  lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 ((1, pos) :: own) ly2 S2 W2 mp md2 k /\
  lib.Reusable.YG01.frames S2 = lib.Reusable.YG01.frames Sq /\
  lib.Reusable.YG0d.ablocks B ly2 S2 = lib.Reusable.YG0d.ablocks B lyq Sq /\
  (exists ff, S2 = lib.Reusable.YG00.set_fs ff Sq) /\
  lib.Reusable.YK11.getr regs2 10 = lib.Reusable.YG0d.w64 (fst (lib.Prog.RcParse.ctrlparse len g)) /\
  (forall i, (i < 36)%nat ->
     lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W2) mp (G + 32 + Z.of_nat i) =
     Some (bv_unsigned (nth i (snd (lib.Prog.RcParse.ctrlparse len g)) lib.Prog.RcParse.cp_z))) /\
  lib.Reusable.YCbq.acall_kept rsegs B lyq Sq W m5 W2 mp (rA S - K_PARSE) (rA S) (fun a => G + 32 <= a < G + 32 + 36) /\
  (* (b) *)
  lib.Reusable.YK11.getr regs2 2 = Z_to_bv 64 (rA S) /\
  lib.Reusable.YK11.getr regs2 3 = gp /\
  lib.Reusable.YK11.getr regs2 4 = tp /\
  lib.Reusable.YK11.getr regs2 8 = Z_to_bv 64 S /\
  lib.Reusable.YK11.getr regs2 9 = Z_to_bv 64 (rA S) /\
  lib.Reusable.YK11.getr regs2 18 = Z_to_bv 64 G /\
  lib.Reusable.YK11.getr regs2 19 = Z_to_bv 64 pn /\
  lib.Reusable.YK11.getr regs2 20 = Z_to_bv 64 pp /\
  lib.Reusable.YK11.getr regs2 21 = Z_to_bv 64 fr /\
  lib.Reusable.YK11.getr regs2 22 = Z_to_bv 64 pa /\
  lib.Reusable.YK11.getr regs2 23 = Z_to_bv 64 len /\
  lib.Reusable.YK11.getr regs2 24 = Z_to_bv 64 (G + 32) /\
  lib.Reusable.YK11.getr regs2 25 = Z_to_bv 64 (G / 8 + lib.B.AsanRT.ASAN_K) /\
  lib.Reusable.YK11.getr regs2 26 = Z_to_bv 64 G /\
  lib.Reusable.YK11.getr regs2 27 = lib.Lib.Mem.wa lib.B.AsanRT.ASAN_K /\
  (* (c) *)
  lib.Lib.Mem.bytes_at rsegs mp (G + 32) (snd (lib.Prog.RcParse.ctrlparse len g)) /\
  lib.Lib.Step.rw_cells rsegs mp (G + 32) [lib.Lib.Cells.CB 36 (snd (lib.Prog.RcParse.ctrlparse len g))] /\
  lib.B.ProgWorld.ctl_kept_vis (lib.Reusable.YA0n.w_H W) m5 mp
    (lib.B.ProgWorld.kept_class B lyq Sq (rA S - K_PARSE) (rA S) (fun a => G + 32 <= a < G + 32 + 36)) /\
  lib.B.ProgWorld.ctl_wmono_vis_off_img (lib.Reusable.YA0n.w_H W) m5 mp
    (lib.B.ProgWorld.kept_class B lyq Sq (rA S - K_PARSE) (rA S) (fun a => G + 32 <= a < G + 32 + 36)) /\
  lib.Lib.Frame.stk rsegs mp (S - 9072) (rA S).

(* ==== THE INTERFACE (2/2): E2 in continuation form.  From the journal at the call state (own' = (1, pos) :: own)
   and parse's premises that the call state does not decide, to SRr at the call config (rrB_QSB's left disjunct,
   with the cfg_at form's fp_regs / fp_csr), the continuation taking rrB_E2_ret at the return state.  Premises:
     the journal at the call state (parse's P1); arodata_okS at the call memory (P2); gp / tp (P4); len's range;
     the function's window (9072 <= S < 2 ^ 64, [S - 9072, S) inside the caller's [sp0 - STK, sp0)) - parse's
     window [rA S - 8800, rA S) lies in it (P7); G the frame (1, pos) of the call state, 8-aligned, its 128 bytes
     below 2 ^ 64; the class-1 room (P8); the message's heap block (P9); G + 32's 36 bytes addressable in the view
     (afobj's shadow part); g and the message bytes in the view (P12, P13).
   Decided inside: ret_ok / raZ of 0x84a68, a0 / a1 / a2, sp's alignment and window, afobj's frame part and
   awr_byte (the frame (1, pos) is in own'), G off the image (ctl_frame_above_img from the journal's AR). ==== *)
Definition rrB_E2_stmt : Prop :=
  forall STK sp0 FP ly S0 (W0 : lib.Reusable.YA0n.world rsegs) mem0 md0 own pos lyq Sq
         (W : lib.Reusable.YA0n.world rsegs) (m5 : word -> option byte) md5 k
         (gp tp x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (fr len pa pp pn S G : Z) (g : list byte)
         (Q : lib.Reusable.YA0n.world rsegs -> config -> Prop),
    lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 ((1, pos) :: own) lyq Sq W m5 md5 k ->
    lib.Reusable.YE01.arodata_okS rsegs B RLO RHI (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) m5) ->
    gp = lib.Reusable.YG0d.w64 (lib.Reusable.YG0f.as_gp B) -> tp = lib.Reusable.YG0d.w64 (lib.Reusable.YG0f.as_tp B) ->
    0 <= len < 2 ^ 64 ->
    9072 <= S -> S < 2 ^ 64 -> sp0 - STK <= S - 9072 -> S <= sp0 ->
    G = lib.Reusable.YG0f.frame_addr lyq 1 pos -> G mod 8 = 0 -> G + 128 <= 2 ^ 64 ->
    lib.Reusable.YG01.count_cid 1 (lib.Reusable.YG01.frames Sq) < lib.Reusable.YG00.fs_frames 1 ->
    (50 <= len -> exists Lf : Z, In (fr, Lf) (lib.Reusable.YG0d.ablocks B lyq Sq) /\ 50 <= lib.Reusable.YG00.req_size Lf) ->
    lib.Reusable.YG0v.range_addressable (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) m5)
      lib.Reusable.YG0f.SHADOW_OFF (G + 32) 36 ->
    length g = 50%nat ->
    (50 <= len -> forall i, (i < 50)%nat ->
       lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) m5 (fr + Z.of_nat i) = Some (lib.Prog.RcParse.cp_v g i)) ->
    (forall W2 ly2 S2 regs2 mp md2,
       rrB_E2_ret STK sp0 FP ly S0 W0 mem0 md0 own pos lyq Sq W m5 k gp tp fr len pa pp pn S G g W2 ly2 S2 regs2 mp md2 ->
       lib.Reusable.YA0n.SRr rsegs W2
         (mkCfg (lib.Reusable.YK11.mkst regs2 (Z_to_bv 64 0x84a68) mp (lib.Reusable.YK11.seg_rom rsegs)) md2) Q) ->
    lib.Reusable.YA0n.SRr rsegs W
      (mkCfg (lib.Lib.MState.MS
                (lib.Lib.Frame.mkR (Z_to_bv 64 0x84a68) (Z_to_bv 64 (rA S)) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 (rA S))
                   (Z_to_bv 64 fr) (Z_to_bv 64 len) (Z_to_bv 64 (G + 32)) x13 x14 x15 x16 x17
                   (Z_to_bv 64 G) (Z_to_bv 64 pn) (Z_to_bv 64 pp) (Z_to_bv 64 fr) (Z_to_bv 64 pa)
                   (Z_to_bv 64 len) (Z_to_bv 64 (G + 32)) (Z_to_bv 64 (G / 8 + lib.B.AsanRT.ASAN_K))
                   (Z_to_bv 64 G) (lib.Lib.Mem.wa lib.B.AsanRT.ASAN_K) x28 x29 x30 x31)
                lib.Reusable.YK11.fp_regs (Z_to_bv 64 lib.B.Prog.reac_ctrl_parse_c.REAC_CTRL_PARSE) lib.Reusable.YK11.fp_csr
                None m5 (lib.Lib.PropExec.seg_rom rsegs)) md5) Q.

(* ---- A byte of image B lies below the hull end 0x5fe000 (B.ProgBridge.rsegs_spans: the four spans, vm_compute). ---- *)
Lemma rrB_E2_in_img_lt : forall a, lib.Reusable.YG0d.in_img segs a -> a < 0x5fe000.
Proof using.
  intros a (sg & Hin & Hlo & Hhi).
  assert (Hm : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg))
                 (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) rsegs))
    by exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) _ _ Hin).
  rewrite lib.B.ProgBridge.rsegs_spans in Hm.
  destruct Hm as [E | [E | [E | [E | []]]]]; injection E as E1 E2; lia.
Qed.

(* ---- The conversion's image-B text holds: every conclusion follows from the post by B.ProgWorld's PROVED pieces, as
   a Theorem Labs lane's own section 6.3 table marks each one DERIVABLE (ctl-post-callees.md:805-811 (a working note, not in this delivery)): the visible keep and writability
   by ctl_kept_of_view_eq (ProgWorld.v:1187) over acall_kept's four view clauses (the reasoning of ctl_post_acall_kept,
   ProgWorld.v:681, with the view moved from W2 to W at a W-visible byte by wle and aview_vis_mrd); the 36 bytes off
   the image by D2 / D3 (the proof of ctl_out_bytes, ProgWorld.v:960, read from aview instead of garr8;
   rw_cells_CB_of_present, ProgWorld.v:720); stk of [lo, sp) by acall_kept's two presence clauses (D4).  So the named
   hypothesis below is closed by this lemma (rrB_E2_parse after the Section). ---- *)
Lemma rrB_ctl_post_reac_ctrl_parse : ctl_post_reac_ctrl_parse_stmt.
Proof using.
  intros _ lyc Sc W W2 memc mem2 regs regs2 lo sp K o kres out _ H10 Hlen HOUT HKEPT Hle Ho0 Ho36 HNI Hlo Hlosp Hsp HPR.
  pose proof HKEPT as (K1 & K2 & K3 & K4 & K5 & K6).
  (* the view of a W-visible kept byte is kept *)
  assert (HV : forall x : word, lib.Reusable.YA0n.w_H W x = false ->
            lib.B.ProgWorld.kept_class B lyc Sc (sp - K) sp (fun a => o <= a < o + 36) (bv_unsigned x) ->
            lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) mem2 (bv_unsigned x) =
            lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) memc (bv_unsigned x)).
  { intros x Hx Hk.
    assert (Hx2 : lib.Reusable.YA0n.w_H W2 x = false).
    { destruct (lib.Reusable.YA0n.w_H W2 x) eqn:E2; [|reflexivity]. rewrite (Hle _ E2) in Hx. discriminate Hx. }
    assert (Hsame : lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) mem2 (bv_unsigned x) =
                    lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W2) mem2 (bv_unsigned x)).
    { rewrite (lib.B.ProgWorld.aview_vis_mrd W mem2 (bv_unsigned x)), (lib.B.ProgWorld.aview_vis_mrd W2 mem2 (bv_unsigned x))
        by (rewrite Z_to_bv_bv_unsigned; assumption).
      reflexivity. }
    rewrite Hsame.
    destruct Hk as [[H1 H2] | [(b & m & i & Hin & Hi & Ha & HE) | [(H1 & H2 & H3) | (cid & pos & Hin & Hr & HE)]]].
    - exact (K1 _ H1 H2).
    - rewrite Ha. exact (K2 b m i Hin Hi HE).
    - exact (K3 _ H1 H2 H3).
    - exact (K4 cid pos _ Hin Hr HE). }
  destruct (lib.B.ProgWorld.ctl_kept_of_view_eq (lib.Reusable.YA0n.w_H W) memc mem2 _ HV) as [HKV HWV].
  (* the window [lo, sp) present at mem2: below the callee's window by clause (5), inside it by clause (6) *)
  assert (HSTK : lib.Lib.Frame.stk rsegs mem2 lo sp).
  { pose proof lib.Reusable.YCbq.asan_consts as (C1 & _).
    split; [lia|]. split; [exact Hsp|].
    intros a Ha.
    assert (Hpa : lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W2) mem2 a).
    { destruct (Z_lt_le_dec a (sp - K)) as [Hlt|Hge].
      - apply K5; [lia | lia | apply HPR; lia].
      - apply K6. lia. }
    destruct Hpa as [_ [b Hb]].
    unfold lib.Lib.Mem.wa, lib.Lib.Mem.mrd. split.
    - unfold wview. rewrite Hb. discriminate.
    - exists b. rewrite Hb. reflexivity. }
  split; [exact H10|].
  split; [|split; [exact HKV|]; split; [exact HWV | exact HSTK]].
  (* the 36 bytes, off the image: present, visible, equal (D2), hence readable and writable (D3) *)
  intros Hnz.
  assert (E : forall j, (j < length out)%nat ->
            exists b, nth_error out j = Some b /\ mem2 (Z_to_bv 64 (o + Z.of_nat j)) = Some b).
  { intros j Hj. rewrite Hlen in Hj. exists (nth j out (Z_to_bv 8 0)).
    split; [apply nth_error_nth'; lia|].
    pose proof (HOUT Hnz j Hj) as Hv.
    pose proof (lib.Reusable.YCbq.seg_rom_none segs (o + Z.of_nat j) ltac:(lia) (HNI Hnz j Hj)) as Hnone.
    unfold lib.Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict in Hv.
    destruct (lib.Reusable.YA0n.w_H W2 (Z_to_bv 64 (o + Z.of_nat j))).
    - rewrite Hnone in Hv. discriminate Hv.
    - destruct (mem2 (Z_to_bv 64 (o + Z.of_nat j))) as [b0|] eqn:Em.
      + cbn [option_map] in Hv. injection Hv as Hb. f_equal. apply bv_eq. exact Hb.
      + rewrite Hnone in Hv. discriminate Hv. }
  assert (HB : lib.Lib.Mem.bytes_at rsegs mem2 o out).
  { split; [exact Ho0|]. split; [rewrite Hlen; exact Ho36|].
    intros i Hi. destruct (E i Hi) as (b & Hn & Hm). rewrite Hn.
    unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa. rewrite Hm. reflexivity. }
  split; [exact HB|].
  apply lib.B.ProgWorld.rw_cells_CB_of_present; [exact Hlen | exact Ho0 | exact Ho36 | |].
  - intros i Hi. rewrite <- Hlen in Hi. destruct (E i Hi) as (b & Hn & Hm). rewrite Hn.
    unfold lib.Lib.Mem.mrd. rewrite Hm. reflexivity.
  - intros i Hi. destruct (E (Z.to_nat i) ltac:(lia)) as (b & _ & Hm).
    rewrite Z2Nat.id in Hm by lia. rewrite Hm. discriminate.
Qed.

(* ---- THE PROOF OF E2 --------------------------------------------------------------------------------------------- *)
(* reac_ctrl_parse's contract, image B, with SEGS := Reusable.YB1v.tfibsegs passed EXPLICITLY (C_reac_ctrl_parse.v:33
   keeps SEGS a Section Variable).  OWNER PENDING: a Theorem Labs lane, pb_reac_ctrl_parse (not Qed). *)
Hypothesis TPARSE : lib.B.Prog.C_reac_ctrl_parse.treac_ctrl_parse_spec segs B RLO RHI.
(* The conversion of parse's cgif post to ctrl's visible form: the image-B text above (ctl-post-callees.md (a working note, not in this delivery),
   with the header's changes (1)-(3)); proved by rrB_ctl_post_reac_ctrl_parse above, which
   rrB_E2_parse passes.  OWNER PENDING: a Theorem Labs lane's lib/B/ProgWorld.v *)
Hypothesis ctl_post_reac_ctrl_parse : ctl_post_reac_ctrl_parse_stmt.

Lemma rrB_E2 : rrB_E2_stmt.
Proof using TPARSE ctl_post_reac_ctrl_parse.
  intros STK sp0 FP ly S0 W0 mem0 md0 own pos lyq Sq W m5 md5 k gp tp x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31
    fr len pa pp pn S G g Q HJ HRO Egp Etp Rlen HSK HS Hlo Hhi EG G8 GHI Hcnt HBLK HADDR Hg HMSG K.
  match goal with |- lib.Reusable.YA0n.SRr _ _ (mkCfg (lib.Lib.MState.MS ?r _ _ _ _ _ _) _) _ => set (regsC := r) end.
  (* rA S = 32 * ((S - 128) / 32): no S mod 16 premise is needed for what follows, so the bound is S - 159 *)
  assert (HA : rA S mod 32 = 0 /\ S - 159 <= rA S <= S - 128)
    by (unfold lib.B.Prog.reac_ctrl_identity_replyRB.rA; Z.div_mod_to_equations; lia).
  assert (EK : K_PARSE = 8800) by reflexivity.
  (* the journal at the call: AR, the live frames ((1, pos) among them), the caller's window present, astk_ok *)
  pose proof HJ as (HAR & _ & _ & _ & _ & HFR & _ & _ & _ & _ & _ & _ & _ & HPRES & HSTK & _ & _).
  destruct HSTK as (_ & _ & Hceil & Hslo & _).
  assert (Hin : In (1, pos) (lib.Reusable.YG01.frames Sq))
    by (rewrite HFR; apply in_or_app; left; left; reflexivity).
  pose proof (lib.B.ProgWorld_Fs.ctl_frame_above_img B lyq Sq W m5 md5 1 pos HAR Hin) as HGimg.
  rewrite <- EG in HGimg.
  assert (E128 : lib.Reusable.YG00.fs_frame_bytes 1 = 128) by reflexivity.
  (* the call registers *)
  assert (Hsp : lib.Reusable.YG0d.spZ regsC = rA S).
  { unfold lib.Reusable.YG0d.spZ. change (lib.Reusable.YK11.getr regsC 2) with (Z_to_bv 64 (rA S)).
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
  assert (Hret : lib.Reusable.YK0s.ret_ok (lib.Reusable.YK11.getr regsC 1)).
  { change (lib.Reusable.YK11.getr regsC 1) with (Z_to_bv 64 0x84a68).
    unfold lib.Reusable.YK0s.ret_ok. vm_compute. reflexivity. }
  assert (Hra : 4096 <= lib.Reusable.YG0d.raZ regsC).
  { unfold lib.Reusable.YG0d.raZ. change (lib.Reusable.YK11.getr regsC 1) with (Z_to_bv 64 0x84a68).
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    rewrite Z.mod_small by lia. lia. }
  assert (Hgp : lib.Reusable.YK11.getr regsC 3 = lib.Reusable.YG0d.w64 (lib.Reusable.YG0f.as_gp B))
    by (change (lib.Reusable.YK11.getr regsC 3) with gp; exact Egp).
  assert (Htp : lib.Reusable.YK11.getr regsC 4 = lib.Reusable.YG0d.w64 (lib.Reusable.YG0f.as_tp B))
    by (change (lib.Reusable.YK11.getr regsC 4) with tp; exact Etp).
  assert (Hal : lib.Reusable.YG0d.spZ regsC mod 16 = 0).
  { rewrite Hsp. unfold lib.B.Prog.reac_ctrl_identity_replyRB.rA. Z.div_mod_to_equations. lia. }
  assert (Hwlo : sp0 - STK <= lib.Reusable.YG0d.spZ regsC - K_PARSE) by (rewrite Hsp, EK; lia).
  assert (Hwhi : lib.Reusable.YG0d.spZ regsC <= sp0) by (rewrite Hsp; lia).
  (* afobj and awr_byte for parse's output [G + 32, G + 68): inside the frame (1, pos), which own' holds *)
  assert (HOBJ : G + 32 <> 0 -> lib.Reusable.APostBase.afobj segs B lyq Sq W m5 (G + 32) 36).
  { intros _. unfold lib.Reusable.APostBase.afobj. split; [|split].
    - exists 1, pos. rewrite <- EG, E128. split; [exact Hin|]. split; [lia|]. split; [exact G8|]. lia.
    - replace (G + 32) with (G + 4 * 8) by lia. rewrite Z_mod_plus_full. exact G8.
    - exact HADDR. }
  assert (HAWR : G + 32 <> 0 -> forall a, G + 32 <= a < G + 32 + 36 ->
            lib.Reusable.YCbq.awr_byte STK sp0 FP (lib.Reusable.YG0d.ablocks B ly S0)
              (lib.Reusable.YG0d.ablocks B lyq Sq) lyq ((1, pos) :: own) a).
  { intros _ a Ha. unfold lib.Reusable.YCbq.awr_byte. right; right; right.
    unfold lib.Reusable.YCbq.in_frames. exists 1, pos. split; [left; reflexivity|].
    left. unfold lib.Reusable.YG0n.in_zr. cbn [fst snd]. rewrite <- EG, E128. lia. }
  (* the call: parse's contract at the call config, in its cfg_at form (B.ProgBridge.cfg_at_MS, by conversion) *)
  match goal with |- lib.Reusable.YA0n.SRr _ _ ?c _ =>
    change c with (lib.Reusable.YG0d.cfg_at segs lib.B.Prog.C_reac_ctrl_parse.A_reac_ctrl_parseP regsC m5 md5) end.
  eapply lib.Reusable.YA0n.SRr_bind;
    [exact (TPARSE STK sp0 FP ly S0 W0 mem0 md0 ((1, pos) :: own) lyq Sq W m5 md5 k regsC fr len (G + 32) g
              HJ HRO Hret Hra Hgp Htp eq_refl eq_refl eq_refl Rlen Hal Hwlo Hwhi Hcnt HBLK HOBJ HAWR Hg HMSG) |].
  intros W2 c2 Hle (ly2 & S2 & regs2 & mp & md2 & Ec & HJ2 & HP & HFR2 & HAB & HSF & H10 & HOUT & HKEPT).
  subst c2. rewrite Hsp in HKEPT.
  (* the conversion at the return: G is off the image (above 0x5fe000), the window below parse's present at m5 *)
  assert (HNI : G + 32 <> 0 -> forall i, (i < 36)%nat -> ~ lib.Reusable.YG0d.in_img segs (G + 32 + Z.of_nat i)).
  { intros _ i Hi Himg. pose proof (rrB_E2_in_img_lt _ Himg) as Hlt. lia. }
  assert (HPR : forall a, S - 9072 <= a < rA S - K_PARSE ->
            lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) m5 a)
    by (intros a Ha; apply HPRES; rewrite EK in Ha; lia).
  destruct (ctl_post_reac_ctrl_parse lib.B.ProgWorld.ctl_out_bytes lyq Sq W W2 m5 mp regsC regs2
              (S - 9072) (rA S) K_PARSE (G + 32) (fst (lib.Prog.RcParse.ctrlparse len g))
              (snd (lib.Prog.RcParse.ctrlparse len g))
              HP H10 (lib.Prog.RcParse.ctrlparse_length len g) HOUT HKEPT Hle ltac:(lia) ltac:(lia) HNI
              ltac:(lia) ltac:(rewrite EK; lia) ltac:(lia) HPR)
    as (_ & HBY & HKV & HWV & HSTK2).
  destruct (HBY ltac:(lia)) as [HB1 HB2].
  change (lib.Reusable.YK11.getr regsC 1) with (Z_to_bv 64 0x84a68).
  apply (K W2 ly2 S2 regs2 mp md2).
  unfold rrB_E2_ret.
  (* (a) *)
  split; [exact Hle|]. split; [exact HJ2|]. split; [exact HFR2|]. split; [exact HAB|]. split; [exact HSF|].
  split; [exact H10|]. split; [intros i Hi; exact (HOUT ltac:(lia) i Hi)|]. split; [exact HKEPT|].
  (* (b): aregs_preserved, read at the concrete call registers *)
  split; [etransitivity; [exact (HP 2 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)) | reflexivity]|].
  split; [etransitivity; [exact (HP 3 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)) | reflexivity]|].
  split; [etransitivity; [exact (HP 4 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)) | reflexivity]|].
  split; [etransitivity; [exact (HP 8 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)) | reflexivity]|].
  split; [etransitivity; [exact (HP 9 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)) | reflexivity]|].
  split; [etransitivity; [exact (HP 18 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)) | reflexivity]|].
  split; [etransitivity; [exact (HP 19 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)) | reflexivity]|].
  split; [etransitivity; [exact (HP 20 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)) | reflexivity]|].
  split; [etransitivity; [exact (HP 21 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)) | reflexivity]|].
  split; [etransitivity; [exact (HP 22 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)) | reflexivity]|].
  split; [etransitivity; [exact (HP 23 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)) | reflexivity]|].
  split; [etransitivity; [exact (HP 24 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)) | reflexivity]|].
  split; [etransitivity; [exact (HP 25 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)) | reflexivity]|].
  split; [etransitivity; [exact (HP 26 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)) | reflexivity]|].
  split; [etransitivity; [exact (HP 27 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)) | reflexivity]|].
  (* (c) *)
  split; [exact HB1|]. split; [exact HB2|]. split; [exact HKV|]. split; [exact HWV | exact HSTK2].
Qed.
End E2.

(* E2 with the conversion closed by rrB_ctl_post_reac_ctrl_parse: reac_ctrl_parse's contract is its one premise. *)
Section E2P.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {SK : lib.Reusable.YI16.sink_head}.
Lemma rrB_E2_parse : forall (B : lib.Reusable.YG0f.asyms) (RLO RHI : Z),
  lib.B.Prog.C_reac_ctrl_parse.treac_ctrl_parse_spec segs B RLO RHI -> rrB_E2_stmt B RLO RHI.
Proof using.
  intros B RLO RHI TP. exact (rrB_E2 B RLO RHI TP (rrB_ctl_post_reac_ctrl_parse B)).
Qed.
End E2P.
