(* fuzz_preset, slice S5b, lane IproA (worker a Theorem Labs lane): parse_items' ENTRY SEGMENT in image A (asan), the boundary
   definition the element-loop lanes consume, and the segment's symbolic-run facts.

   THE SEGMENT is listing rows 1..107 of parse_items (image A 0x87298, whole-program listing lib/A/Listing_prog.v +
   lib/A/PAImg_prog.v, instances PL_prog_A / PI_prog_A, entry fact A_entry_parse_items):

     rows   1.. 15  the prologue: `addi sp, sp, -0x90` and ra, s0..s11 saved. THERE IS NO ASan FAKE FRAME HERE:
                    parse_items has no `jal __asan_stack_malloc_N` (its first `jal` is row 77, an errpath), because
                    its only locals are the four spill slots at 8(sp), 0x10(sp), 0x18(sp) and 0x20(sp). So this
                    function has ONE frame arm, the real stack, and it needs neither a frame-allocator contract nor
                    a class-full refusal arm. (parse_value, lane VproA, does take a class-0 frame; the frame
                    headroom conjunct of PRH_FnParse.rd_pre is that lane's, and this lane does not use it.)
     rows  16.. 33  the shadow base out of the GOT (A_OBJ 0 -> A_OBJ 12, rows 17-19), the node's type word
                    v->type = 5 + [o] (row 30, `sw a0, 0(s4)`, after the shadow check of v at rows 21-25), and the
                    shadow check of q + 0x10 (rows 29-33).
     rows  34.. 39  the depth word: a1 = q->depth, q->depth = a1 + 1 (row 37), s2 = -1, and `blt 31, a1` (row 39):
                    the DEPTH REFUSAL branch. Taken (a1 >= 32) -> rows 310..325, return -1.
     rows  40.. 53  the cursor: a0 = q->p, q->p = a0 + 1 (the opener is consumed), a2 = q->end, and `bgeu a3, a2`
                    (row 53): the text ends right after the opener -> row 78.
     rows  54.. 74  the inlined skip_ws loop (head row 59 = 0x8737c, back edge row 73). The mask of rows 56-58 is
                    0x100002600, which is PjGrammar.ws (0x20, 0x09, 0x0a, 0x0d).
     rows  78.. 89  the closer test: the byte at the cursor is read only when the cursor is below the end; for an
                    array (s3 = 0) row 87 jumps to the ']' test of row 294, for an object row 89 tests '}'.
     rows 294..304  the EMPTY CONTAINER exit: the closer is consumed, q->depth is written back as a1 (the entry
                    depth), s2 = 0, and rows 310..325 return 0 with the node left as the zeroed JArr [] / JObj [].
     rows  90.. 92  the first growth of the kids array: `mv a0, s4` (the node) and row 91 `jal -0xa40 <grow>`
                    (PCall AS_grow in the listing), then row 92 `bnez a0`: the GROW REFUSAL path, rows 310..325,
                    return -1.
     rows  93..107  the loop set-up, and row 108 (0x87440) is the head of the ELEMENT LOOP, which is also the
                    target of the back edge of row 282. vrd_ielem_a is the state there.

   EVERY errpath_* call reached from this range (row 77 and rows 347 onwards) is an ASan REPORT and is unreachable
   under the segment's premises: the shadow bytes of q (24 bytes) and of v (56 bytes) are zero by rd_pre's
   range_addressable conjuncts, which enter the symbolic runner as the shadow entries pi_SH, so the token engine
   resolves every `lb`/`lbu` of a shadow byte of q or v to 0 and never reaches the branch that calls an errpath_*.
   No contract is assumed for any errpath_* symbol. The measured witness is vrd_irun_entry / vrd_irun_depth /
   vrd_irun_cursor / vrd_irun_eot / vrd_irun_toskip below: each run ends with `sh_obls = []`, i.e. the run left no
   shadow obligation at all, and no run stops at an errpath slot.

   WHAT IS A HYPOTHESIS HERE (rule 24: no function is proved in this lane): the callee grow, by THE KIT'S PUBLISHED
   text PRH_FnReader.tgrow_specX, taken verbatim and by name. ROOM IS AN INVARIANT since kit b7722372682: the
   texts take `room_live_cf S` and give `room_live_cf S'` in every arm, so this lane counts nothing and carries
   no kr.

   THE GENERIC INVARIANT (a Theorem Labs lane's ruling, 2026-10-29 12:19Z): an SRr post is opaque once Qed, so the invariant
   must be in the segment's statement; the generic SRr_memnorm was measured not provable (a Theorem Labs lane), so it cannot
   be added afterwards. Every segment lemma here has a generic form `L_inv : forall Pm, srr_inv_laws segs Pm ->
   (srr_inv_call segs Pm ->) .. -> Pm <start memory> -> SRr .. (fun W' c' => <Q> W' c' /\ Pm (ms_mem (cfg_ms c')))`:
   srr_inv_call only where the segment crosses the first grow (vrd_igrow_inv, vrd_ipro_ok_of_iRet_inv,
   vrd_ipro_ok_inv), the single srr_inv_laws premise otherwise. Each old statement survives BYTE-IDENTICAL under its
   old name as the corollary at Pm := fun _ => True (vrd_inv_true / vrd_inv_call_true). vrd_iret and vrd_iref92 keep
   their old proofs; their generic forms vrd_iret_inv / vrd_iref92_inv carry Pm in the body Qb. The segment master
   is vrd_ipro_ok_inv; vrd_ipro_ok : forall d CTX, vrd_ipro_stmt d CTX is its corollary.

   THE POST-IMPLICATION RESTATEMENT (lane A'Ipro, a Theorem Labs lane's approval 2026-10-29: the old statements of
   vrd_ipro_stmt / vrd_ipost / vrd_iRet change, the generic _inv / _P siblings kept). Against the kit reader text
   (a working branch 3ac20a5c9e30 via a working branch 6b723d760c66: PRH_FnParse.v
   94232293d483, PRH_FnReader.v fb7b12dfa169, PRH_Base.v ee2f5cd7ed35, PRH_FnAlloc.v 95e26ff95e63):
   - the premises are the text's, vrd_ipre, with `.. ran most own`, the memnorm premise and the two live-count
     premises; there are NO room-position binders and no entry position (the record vrd_rpos is gone);
   - the returning arms' post is the text's post body, VrdIElem.vrd_items_q (position transfer, OUTCOME, the ledger
     move at most and the call's granted trace, the live requests); the loop head is VrdIElem's post-implication
     vrd_ielem_a;
   - the first grow is grow's kit text: its arms state their events with cf_head (prhPg_evs), the reader's post with
     PresetReqAt.HEAD, bridged by the Section hypothesis HI_head (a Theorem Labs lane's one spelling, discharged by reflexivity
     at CfParams_preset); the refusal arms read grow's advance from grow's own position-transfer conjunct (no event:
     the position stays; an object's keys refusal: the kids realloc's one event), and their OUTCOME clause holds
     because grow's refused arm excludes a granted run (vrd_excl_grow) and a chosen failure inside the window is
     excluded by the window premise (vrd_excl_fail). AGREE-PREFIX is not used.

   THE RE-HIDING MOVE (the free / realloc texts conclude SRr' segs RZ_cf, their journals at wle' segs RZ_cf, and grow's
   text with them: SRr' and the post fpostWmR at wle'). Every segment that crosses the first grow concludes SRr': the
   grow step (vrd_iDstep / vrd_iDstep_P), the step after it (vrd_iRet / vrd_iRet_P, whose journals are at wle') and
   every segment that ends in one of them, up to the master vrd_ipro_ok_inv. The call itself is vrd_call_WR, the
   R form of VrdArm.vrd_call_W at wle' (the engine's afn_pre_x_atR / ajournal_x_subR). The segments that cross no call
   keep their SRr statements: the depth refusal, the empty container (through the generic forms vrd_iretR /
   vrd_iret_invR at wle, and vrd_ipro_go_invR at wle with its grow step vacuous). vrd_iret / vrd_iref92 and their
   generic forms are the record of the refused arms after the grow: SRr' with the post fpostWFR at wle'.
   THE HULL PREMISE (the texts' threaded allocator hull): vrd_ipre's trailing slot carries the text's
   `PresetHullBudget.hull_budget Sa (rd_hevs (prhPi_gtrace d o ..))`; grow's budget is its prefix (vrd_gevs_prefix,
   PresetHullBudget.hull_budget_infix), and grow's `hull_used S S2 (prhPg_evs ..)` gives the post's hull_used over the
   call's granted events (vrd_hull_gtrace) and the loop head's over the events made so far. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i
YCbn YP0b YP0a YN3v YI04 YG0s YP07 YI00 YI16 YK04 YA0i YA0n YA0o YCbm YA0q YG0v YG00 YG0a YG01 YG0f YG0n YG0d YCbq
YM05 YG0p YK06 YP0d YP0c YC80 YPsym YC4aP YImgTop YC1fP YCbqG YC80x YC1fPx YC80xf YGcfNames YGcfRoomPre YGcfRoomKeep
YG0dcf YN0d YSRrMemnorm YC80xf_inv.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
PRH_Base PRH_Img PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse VrdFrame VrdPro VrdNum VrdArm VrdIElem VrdIStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require PRW_StepKit.
(* The kit's cut: the post's free order (PRH_PjOrder.pj_foR), the model's free list (PresetReqAt.jfl / gheld / arrz), the
   wild budget (YCbqGwild) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
(* the re-hiding move's SRr' / wle' and their generic forms (YA0nH), preset's zone (YGcfRehidePost.RZ_cf), and the
   threaded hull premise (PresetHullBudget) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
(* PRW_StepKit (through VrdIStep.v on the old-pin line) loads YF0v.v, which sets Zify's euclidean-division flag off
   GLOBALLY; this file's lia goals need it on (VrdIStep.v blob de23eae693b8 does the same) *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the addresses of the segment, read off the listing ---- *)
Definition PI_ENTRY : Z := 0x87298.      (* row 1, A_entry_parse_items *)
Definition PI_DEPTHBR : Z := 0x8732c.    (* row 39, `blt 31, a1`: the depth refusal branch *)
Definition PI_CURSBR : Z := 0x87364.     (* row 53, `bgeu a3, a2`: the text ends after the opener *)
Definition PI_SKIPHD : Z := 0x8737c.     (* row 59, the head of the inlined skip_ws loop *)
Definition PI_GROWRET : Z := 0x87400.    (* row 92, the return site of the first grow *)
Definition PI_ELEM : Z := 0x87440.       (* row 108, the head of the element loop *)
Definition PI_RETPC : Z := 0x877a4.      (* row 325, `ret` *)
Definition PI_FRAME : Z := 144.          (* row 2, `addi sp, sp, -0x90` *)
Definition PI_WSMASK : Z := 4294977024.  (* rows 56-58, the white-space mask: PjGrammar.ws *)
Definition PI_SB : Z := 2147450880.      (* SHADOW_OFF, the value the GOT cell holds *)

(* ============================================================================================================== *)
(* THE SEGMENT'S SYMBOLIC ENTRY STATE AND ITS RUNS.                                                               *)
(* ss_ipro is the symbolic state at parse_items' entry: the caller's frame window below sp, the GOT cell and the
   shadow-base cell, the cursor q (atom 10 = a0) with its three fields in atoms 33 (p), 34 (text + len) and 35 (the
   depth), and the node v (atom 11 = a1) with its first four bytes writable (the type word of row 30). The shadow
   entries pi_SH are rd_pre's two range_addressable conjuncts, for q (24 bytes) and for v (56 bytes).
   The five run lemmas below are the segment's control-flow map, machine-checked against the image's bytes: each
   leaves NO shadow obligation, so every ASan check of the segment is discharged by pi_SH alone. *)
(* The cursor q is THREE regions, not one: the footprint rd_fp q v names only [q, q + 8) (the p field, rows 48 and
   71) and [q + 16, q + 20) (the depth word, rows 37 and 303) as written, so the end field [q + 8, q + 16) and the
   4 bytes [q + 20, q + 24) must keep their values for the window clause of fpostWF. A region has ONE write window,
   so the three sub-ranges are three regions over the same base atom 10 (their extents are disjoint). *)
Definition pi_regions : smem :=
[ stack_region PI_FRAME; got_regionP; bcell_regionP 32;
  YP09.mkRegion (Some 10%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))];
  YP09.mkRegion (Some 10%nat) 8 16 8 8 [YP09.mkChunk 8 (CVal 8 (SOff 34 0))];
  YP09.mkRegion (Some 10%nat) 16 24 16 20 [YP09.mkChunk 16 (CVal 4 (SOff 35 0))];
  YP09.mkRegion (Some 11%nat) 0 56 0 4 [] ].
Definition pi_facts : facts := mkFacts
 [ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF 4096 (2^47 - 24) 3); (11%nat, mkAF 4096 (2^47 - 56) 3);
   (12%nat, mkAF 0 1 0); (32%nat, mkAF PI_SB PI_SB 0); (33%nat, mkAF 4096 (2^47 - 1) 0);
   (34%nat, mkAF 4096 (2^47 - 1) 0); (35%nat, mkAF 0 32 0) ] [] [].
Definition ss_ipro : sstate := mkSS (PI_ENTRY - A_prog_base) sr_atoms pi_regions None pi_facts.
Definition pi_Bx : sv := SOff 32 0.
Definition pi_SH : list shent := [mkSHE 10 0 24; mkSHE 11 0 56].
Definition pi_Bspan : Z * Z := (PI_SB, PI_SB + 2 ^ 44 - 1).
Definition pi_K : nat := 512.
Definition pi_run (ss : sstate) := sym_runN_pi_tok A_prog_tpi A_prog_tw pi_K pi_Bx pi_Bspan pi_SH FUEL ss.
Definition pi_runto (stop : Z) (ss : sstate) :=
  sym_run_toN_pi_tok A_prog_tpi A_prog_tw pi_K pi_Bx pi_Bspan pi_SH FUEL stop ss.

Lemma vrd_istatic_ok : sh_static_ok pi_K pi_Bx pi_Bspan pi_SH (ss_facts ss_ipro) (ss_mem ss_ipro) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma vrd_iK : run_K A_LIM pi_Bx pi_SH ss_ipro = pi_K.
Proof. vm_compute. reflexivity. Qed.

(* rows 1..39: the prologue, the type word, the depth increment, and the stop at the depth branch *)
Lemma vrd_irun_entry :
  A_prog_base + ss_pc (sh_ss (fst (pi_run ss_ipro))) = PI_DEPTHBR /\
  snd (pi_run ss_ipro) = PTS_stopped (SR_branch BC_LT (SLit 31) (SOff 35 0)) /\
  sh_obls (fst (pi_run ss_ipro)) = [].
Proof. vm_compute. repeat split; reflexivity. Qed.

Definition ss_idepth : sstate := add_cond (sh_ss (fst (pi_run ss_ipro))) (mkAC BC_LT (SLit 31) (SOff 35 0)).
Definition ss_igo : sstate := add_cond (sh_ss (fst (pi_run ss_ipro))) (mkAC (neg_bc BC_LT) (SLit 31) (SOff 35 0)).

(* the DEPTH REFUSAL arm, 31 < depth: rows 310..325 and the return, in one run *)
Lemma vrd_irun_depth :
  A_prog_base + ss_pc (sh_ss (fst (pi_run ss_idepth))) = PI_RETPC /\
  snd (pi_run ss_idepth) = PTS_stopped (SR_jalr (SOff 1 0)) /\
  sh_obls (fst (pi_run ss_idepth)) = [].
Proof. vm_compute. repeat split; reflexivity. Qed.

(* rows 40..53: the opener is consumed and the run stops at the end-of-text branch *)
Lemma vrd_irun_cursor :
  A_prog_base + ss_pc (sh_ss (fst (pi_run ss_igo))) = PI_CURSBR /\
  snd (pi_run ss_igo) = PTS_stopped (SR_branch BC_GEU (SOff 33 1) (SOff 34 0)) /\
  sh_obls (fst (pi_run ss_igo)) = [].
Proof. vm_compute. repeat split; reflexivity. Qed.

Definition ss_ieot : sstate := add_cond (sh_ss (fst (pi_run ss_igo))) (mkAC BC_GEU (SOff 33 1) (SOff 34 0)).
Definition ss_iws : sstate := add_cond (sh_ss (fst (pi_run ss_igo))) (mkAC (neg_bc BC_GEU) (SOff 33 1) (SOff 34 0)).

(* the text ends right after the opener: no byte is read, no closer test, straight to the first grow (row 91) *)
Lemma vrd_irun_eot :
  A_prog_base + ss_pc (sh_ss (fst (pi_run ss_ieot))) = PI_GROWRET /\
  snd (pi_run ss_ieot) = PTS_call AS_grow /\
  sh_obls (fst (pi_run ss_ieot)) = [].
Proof. vm_compute. repeat split; reflexivity. Qed.

(* there is a byte after the opener: rows 54..58 and the stop at the head of the inlined skip_ws loop *)
Lemma vrd_irun_toskip :
  A_prog_base + ss_pc (sh_ss (fst (pi_runto (PI_SKIPHD - A_prog_base) ss_iws))) = PI_SKIPHD /\
  snd (pi_runto (PI_SKIPHD - A_prog_base) ss_iws) = PTS_running /\
  sh_obls (fst (pi_runto (PI_SKIPHD - A_prog_base) ss_iws)) = [].
Proof. vm_compute. repeat split; reflexivity. Qed.

(* rows 93..107, the loop set-up: from the return site of the first grow to the element loop head. This is the
   measurement vrd_ielem_a's register and spill-slot conjuncts are written from: s0 = q and s9 = q + 16 and
   s19 = o and s20 = v and s23 = shadow(q + 8) and s27 = shadow(q) are carried in unchanged, and the set-up makes
   s18 = shadow(v + 40), s21 = 32, s22 = v + 40, s24 = v + 24, s25 = the white-space mask, with the four spill
   slots 8(sp) = q + 8, 0x10(sp) = shadow(q + 16), 0x18(sp) = shadow(v + 24) and 0x20(sp) = v + 32. *)
Definition ss_itail : sstate := mkSS (PI_GROWRET + 4 - A_prog_base) sr_atoms
  [ YP09.mkRegion (Some 2%nat) 0 PI_FRAME 0 PI_FRAME [] ]
  None (mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (20%nat, mkAF 4096 (2^47 - 56) 3);
                  (21%nat, mkAF 4096 (2^47 - 1) 0); (22%nat, mkAF 4096 (2^47 - 1) 0);
                  (26%nat, mkAF PI_SB PI_SB 0) ] [] []).
Definition pi_tailrun :=
  sym_run_toN_pi_tok A_prog_tpi A_prog_tw pi_K (SOff 26 0) pi_Bspan [] FUEL (PI_ELEM - A_prog_base) ss_itail.
Lemma vrd_irun_tail :
  A_prog_base + ss_pc (sh_ss (fst pi_tailrun)) = PI_ELEM /\
  snd pi_tailrun = PTS_running /\
  map (fun i => sr_get (ss_regs (sh_ss (fst pi_tailrun))) (Z_to_bv 5 i)) [8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] =
    [ SOff 8 0; SOff 9 0; SAlu ALU_ADD (SAlu ALU_SRL (SOff 20 40) (SLit 3)) (SOff 26 0); SOff 19 0; SOff 20 0;
      SLit 32; SOff 20 40; SOff 23 0; SOff 20 24; SLit PI_WSMASK; SOff 26 0; SOff 27 0 ] /\
  ss_mem (sh_ss (fst pi_tailrun)) =
    [ YP09.mkRegion (Some 2%nat) 0 PI_FRAME 0 PI_FRAME
        [ YP09.mkChunk 24 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 20 24) (SLit 3)) (SOff 26 0)));
          YP09.mkChunk 32 (CVal 8 (SOff 20 32));
          YP09.mkChunk 16 (CVal 8 (SOff 21 0));
          YP09.mkChunk 8 (CVal 8 (SOff 22 0)) ] ].
Proof. vm_compute. repeat split; reflexivity. Qed.

(* ============================================================================================================== *)
(* THE MODEL SIDE of the segment: what PjGrammar.jr_items does on the three returning arms and on the way into the
   element loop. Machine state free, so outside the Section.                                                      *)
(* ============================================================================================================== *)

(* row 39, the DEPTH REFUSAL: the cursor's depth word is already 32 = MAXD, so the model refuses with no trace *)
Lemma vrd_items_refuse : forall o x ok, jr_items prh_jr_strtod PjGrammar.MAXD o x ok = (None, [], ok).
Proof. intros o x ok. reflexivity. Qed.

(* rows 294..304, the EMPTY CONTAINER: the first non-space byte after the opener is the closer *)
Lemma vrd_items_empty : forall d o x r0 ok, (d < PjGrammar.MAXD)%nat ->
  PjGrammar.skip (tl x) = PjGrammar.closer o :: r0 ->
  jr_items prh_jr_strtod d o x ok = (Some (PjGrammar.mk o [], r0), [], ok).
Proof.
intros d o x r0 ok Hd Hs. unfold jr_items, jr_cont.
replace (Nat.ltb PjGrammar.MAXD (S d)) with false by (symmetry; apply Nat.ltb_ge; lia).
cbv zeta. rewrite Hs, Z.eqb_refl. reflexivity.
Qed.

(* rows 90..107, the way into the element loop: the model enters jrl, whose first step is the grow of row 91 *)
Lemma vrd_items_go : forall d o x ok, (d < PjGrammar.MAXD)%nat ->
  (forall r, PjGrammar.skip (tl x) <> PjGrammar.closer o :: r) ->
  jr_items prh_jr_strtod d o x ok =
  jrl prh_jr_strtod (S (2 * length x + 1)) (S d) o 0 0 [] (PjGrammar.skip (tl x)) ok.
Proof.
intros d o x ok Hd Hs. unfold jr_items, jr_cont.
replace (Nat.ltb PjGrammar.MAXD (S d)) with false by (symmetry; apply Nat.ltb_ge; lia).
replace (2 * length x + 2)%nat with (S (2 * length x + 1)) by lia.
cbv zeta. destruct (PjGrammar.skip (tl x)) as [|c r] eqn:E; [reflexivity|].
destruct (Z.eqb_spec c (PjGrammar.closer o)) as [->|Hc]; [exfalso; exact (Hs r eq_refl)|reflexivity].
Qed.

(* row 92's refusals, on the model side: the first grow's kids realloc refused (ok = false :: _), or for an object the
   kids granted and the keys refused (ok = true :: false :: _); the model refuses with the trace so far *)
Lemma vrd_items_kids_fail : forall d o x okr, (d < PjGrammar.MAXD)%nat ->
  (forall r, PjGrammar.skip (tl x) <> PjGrammar.closer o :: r) ->
  jr_items prh_jr_strtod d o x (false :: okr) = (None, [PjGrammar.EFail 448], okr).
Proof.
intros d o x okr Hd Hs. rewrite (vrd_items_go d o x (false :: okr) Hd Hs). destruct o; reflexivity.
Qed.

Lemma vrd_items_keys_fail : forall d x okr, (d < PjGrammar.MAXD)%nat ->
  (forall r, PjGrammar.skip (tl x) <> PjGrammar.closer true :: r) ->
  jr_items prh_jr_strtod d true x (true :: false :: okr) =
    (None, [PjGrammar.EGrow 0 448; PjGrammar.EFail 64], okr).
Proof.
intros d x okr Hd Hs. rewrite (vrd_items_go d true x (true :: false :: okr) Hd Hs). reflexivity.
Qed.

(* ---- The kit's cut (FREEORD-NONE): the model's FREE LIST of the call, PRH_FnParse.prhPi_frees (PresetReqAt.jf_cont
   over jfl at jr_items' fuel), on the same arms: the depth refusal and the empty container free nothing, the loop
   starts jfl from the empty container, and the first grow's refusals leave nothing or, for an object whose keys
   realloc was refused, the new kids block (PresetReqAt.gheld's first arm) ---- *)
Lemma vrd_frees_refuse : forall o x ok, prhPi_frees PjGrammar.MAXD o x ok = [].
Proof. intros o x ok. reflexivity. Qed.

Lemma vrd_frees_empty : forall d o x r0 ok, (d < PjGrammar.MAXD)%nat ->
  PjGrammar.skip (tl x) = PjGrammar.closer o :: r0 -> prhPi_frees d o x ok = [].
Proof.
intros d o x r0 ok Hd Hs. unfold prhPi_frees, PresetReqAt.jf_cont.
replace (Nat.ltb PjGrammar.MAXD (S d)) with false by (symmetry; apply Nat.ltb_ge; lia).
cbv zeta. rewrite Hs, Z.eqb_refl. reflexivity.
Qed.

Lemma vrd_frees_go : forall d o x ok, (d < PjGrammar.MAXD)%nat ->
  (forall r, PjGrammar.skip (tl x) <> PjGrammar.closer o :: r) ->
  prhPi_frees d o x ok =
  PresetReqAt.jfl ReaderRes.jr_strtod (S (2 * length x + 1)) (S d) o 0 0 [] (PjGrammar.skip (tl x)) ok.
Proof.
intros d o x ok Hd Hs. unfold prhPi_frees, PresetReqAt.jf_cont.
replace (Nat.ltb PjGrammar.MAXD (S d)) with false by (symmetry; apply Nat.ltb_ge; lia).
replace (2 * length x + 2)%nat with (S (2 * length x + 1)) by lia.
cbv zeta. destruct (PjGrammar.skip (tl x)) as [|c r] eqn:E; [reflexivity|].
destruct (Z.eqb_spec c (PjGrammar.closer o)) as [->|Hc]; [exfalso; exact (Hs r eq_refl)|reflexivity].
Qed.

Lemma vrd_frees_kids_fail : forall d o x okr, (d < PjGrammar.MAXD)%nat ->
  (forall r, PjGrammar.skip (tl x) <> PjGrammar.closer o :: r) ->
  prhPi_frees d o x (false :: okr) = [].
Proof.
intros d o x okr Hd Hs. rewrite (vrd_frees_go d o x (false :: okr) Hd Hs). destruct o; reflexivity.
Qed.

Lemma vrd_frees_keys_fail : forall d x okr, (d < PjGrammar.MAXD)%nat ->
  (forall r, PjGrammar.skip (tl x) <> PjGrammar.closer true :: r) ->
  prhPi_frees d true x (true :: false :: okr) = [Z.of_nat 448 + PresetReqAt.HEAD].
Proof.
intros d x okr Hd Hs. rewrite (vrd_frees_go d true x (true :: false :: okr) Hd Hs). reflexivity.
Qed.

(* ---- the unread rest at a cursor (PRH_Reader.rest_atR), as rows 44..74 move it ---- *)
Lemma vrd_rest_cons : forall tb text P, text <= P -> (Z.to_nat (P - text) < length tb)%nat ->
  rest_atR tb text P = nth (Z.to_nat (P - text)) tb 0 :: rest_atR tb text (P + 1).
Proof.
intros tb text P H1 H2. unfold rest_atR.
replace (Z.to_nat (P + 1 - text)) with (S (Z.to_nat (P - text))) by lia.
revert H2. generalize (Z.to_nat (P - text)) as k. clear. induction tb as [|b r IH]; intros [|k] Hk; cbn in *; try lia.
- reflexivity.
- apply IH. lia.
Qed.

Lemma vrd_rest_tl : forall tb text P, text <= P -> tl (rest_atR tb text P) = rest_atR tb text (P + 1).
Proof.
intros tb text P H. unfold rest_atR. replace (Z.to_nat (P + 1 - text)) with (S (Z.to_nat (P - text))) by lia.
generalize (Z.to_nat (P - text)) as k. clear. induction tb as [|b r IH]; intros [|k]; cbn; try reflexivity. apply IH.
Qed.

Lemma vrd_rest_len : forall tb text P, text <= P ->
  Z.of_nat (length (rest_atR tb text P)) = Z.max 0 (Z.of_nat (length tb) - (P - text)).
Proof. intros tb text P H. unfold rest_atR. rewrite length_skipn. lia. Qed.

Lemma vrd_rest_end : forall tb text P, Z.of_nat (length tb) <= P - text -> rest_atR tb text P = [].
Proof. intros tb text P H. unfold rest_atR. apply skipn_all2. lia. Qed.

(* ---- the white space of rows 54..74, against PjGrammar.skip ---- *)
Lemma vrd_skip_ws : forall b r, PjGrammar.ws b = true -> PjGrammar.skip (b :: r) = PjGrammar.skip r.
Proof. intros b r H. cbn [PjGrammar.skip]. rewrite H. reflexivity. Qed.
Lemma vrd_skip_nws : forall b r, PjGrammar.ws b = false -> PjGrammar.skip (b :: r) = b :: r.
Proof. intros b r H. cbn [PjGrammar.skip]. rewrite H. reflexivity. Qed.

(* row 64 leaves the loop when 32 < b, and no white-space byte is above 32 *)
Lemma vrd_ws_32 : forall b, 32 < b -> PjGrammar.ws b = false.
Proof.
intros b H. unfold PjGrammar.ws.
repeat match goal with |- context [Z.eqb ?a ?c] => destruct (Z.eqb_spec a c); [lia|] end. reflexivity.
Qed.
Lemma vrd_closer_32 : forall o, 32 < PjGrammar.closer o.
Proof. intros []; cbn; lia. Qed.
Lemma vrd_closer_ws : forall o, PjGrammar.ws (PjGrammar.closer o) = false.
Proof. intros o. apply vrd_ws_32, vrd_closer_32. Qed.
Lemma vrd_skip_idem : forall x, PjGrammar.skip (PjGrammar.skip x) = PjGrammar.skip x.
Proof.
induction x as [|b r IH]; [reflexivity|]. cbn [PjGrammar.skip].
destruct (PjGrammar.ws b) eqn:E; [exact IH | cbn [PjGrammar.skip]; rewrite E; reflexivity].
Qed.
Lemma vrd_skip_head : forall x c r, PjGrammar.skip x = c :: r -> PjGrammar.ws c = false.
Proof.
induction x as [|b x IH]; intros c r H; cbn [PjGrammar.skip] in H; [discriminate|].
destruct (PjGrammar.ws b) eqn:E; [exact (IH c r H) | injection H as <- _; exact E].
Qed.
(* rows 56..58 build the mask 0x800013 << 9, whose set bits are 9, 10, 13 and 32: that is PjGrammar.ws *)
Lemma vrd_mask_ws : forall b, 0 <= b <= 32 ->
  Z.land (Z.shiftr PI_WSMASK (b mod 64)) 1 = (if PjGrammar.ws b then 1 else 0).
Proof.
intros b Hb.
assert (Hall : forallb (fun x => Z.eqb (Z.land (Z.shiftr PI_WSMASK (x mod 64)) 1)
                                       (if PjGrammar.ws x then 1 else 0))
                       (map Z.of_nat (seq 0 33)) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in Hall.
apply Z.eqb_eq, Hall, in_map_iff. exists (Z.to_nat b).
split; [lia | apply in_seq; lia].
Qed.

(* ============================================================================================================== *)
Section a. Context {rc : YM05.RunCeil} {fx : YK11.FPState} {ci : CfImg} {cp : CfParams} {PIm : PrhImg}
  {RL : PrhRoomLive}.
Local Notation segs := (@pa_segs _ _ PI_prog_A).
Local Notation VAL := (@pa_val _ A_prog_listing PI_prog_A).
Local Notation BASE := (@pa_val _ A_prog_listing PI_prog_A A_TEXT).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx HL.
(* the image binding of B (the kit's PALib: the GOT words, the shadow cell, the use-after-return GOT word) *)
Hypothesis PAL : PALib (L := A_prog_listing) (PI := PI_prog_A) B.
(* the three image numbers this segment needs, true at prh_img_A by vm_compute: parse_items' own frame is the
   144 bytes of row 2, parse_value's frame is non-negative (it enters STK_parse_items), and so is grow's bound *)
Hypothesis H_img : pi_frame F_parse_items = PI_FRAME /\ 0 <= pi_frame F_parse_value /\ 0 <= STK_grow.
(* THE ONE CALLEE of this segment: grow, by the kit's PUBLISHED text, lib/A/PRH_FnReader.v tgrow_specX, at the call
   contexts CTX0 the caller supplies. It takes `room_live_cf S` and gives `room_live_cf S'` in every one of its
   eight arms, so this lane threads the room through and counts nothing: IproA's replaced-premise stand-in is
   GONE. Since the kit 7bd893468c8 (record texts 6bdfe9256bd) tgrow_specX also gives `blocks_bytes S' <=
   blocks_bytes S + prh_held (prhPg_gtrace ..)`, so no blocks_bytes premise is carried for grow. Since the texts'
   call-graph universe closure (a working branch bbf2cf3be57) the texts and grow take the SAME closure
   prh_univ_closure B CTX0, CTX0 the Section's, and vrd_ipre carries the closure premise. Since the kit's cut 7cdbb61b5fa0
   the closure takes no cursor words; the cursor SET CW (the Section's) is the texts' prh_cw_entry / wild_room, which
   vrd_ipre carries in its trailing slot, and grow's text does not name it. *)
Variable CTX0 : list (list Z).
Variable CW : list (list Z).
Hypothesis H_grow : tgrow_specX B ARx SK CTX0.
(* TWO IMAGE / INSTANCE FACTS, positive facts the instance supplies (both carried the same way by VstrC's VrdArm.v):
   - the harness hides a head of at least one WORD: prh_hblock reads the head word at a - cf_head as 8 bytes, and the
     node's stores must miss it (CfParams has only cf_head_nonneg and cf_head_al; CfParams_preset has cf_head = 16);
   - prh_pst (alloc.c's six statics and fuzz_preset.c's g_own_ran_out) are image bytes (S1ImgA.pst_in_img_A at prh_img_A), so the segment's stores into
     its frame, the cursor and the node miss them. *)
Hypothesis H_head8 : 8 <= cf_head.
Hypothesis H_pst_img : forall a, Exists (in_zr a) prh_pst -> in_img segs a.
(* THE HEAD THE MODEL CHARGES IS THE INSTANCE'S (a Theorem Labs lane's ruling, 2026-10-29: ONE name chain-wide, discharged at the
   real instance by reflexivity at CfParams_preset): grow's post states its events with cf_head (PRH_FnReader.prhPg_evs),
   the reader's post with PresetReqAt.HEAD (rd_hevs); this is the bridge (PRH_FnReader.prhPg_evs_model) *)
Hypothesis HI_head : cf_head = PresetReqAt.HEAD.
(* parse_items holds s0 = q at its calls (PRH_Img.v:372, prh_img_A's pi_s0cur, generated from 0x872f0 `addi s0, a0, 0`),
   so prh_cur_entry's word at q - 16 is the one the chain at the call reads *)
Hypothesis H_s0 : pi_s0cur F_parse_items = Some 0.
(* grow holds s0 = v + 48 across its fuzz_realloc calls (PRH_Img.v:373, generated from A 0x86a0c `addi s0, s1, 48`):
   its chain premise at prh_s0 F_grow v is then below alloc_ceiling (achain_low) *)
Hypothesis H_s0g : pi_s0cur F_grow = Some 48.

(* ---- THE LEDGER'S FIELDS, each through ONE named projection (a Theorem Labs lane's rule, 2026-10-29: never destructure the
   shared prh_ledger / prh_glob / prh_hblock positionally). Since the kit text (PRH_Base.v ee2f5cd7ed35) each is a
   citation of PRH_Base.v's Section ledger_proj (prh_ledger_bounds / prh_ledger_nodup) or S1Ledger's
   prh_ledger_hblock, at the text's most / own. ---- *)
Lemma vrd_led_bounds : forall ly S Hp W mem Lam peak cnt fail ran most own,
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  0 <= Ledger.lsum Lam <= peak /\ peak < 2 ^ 64 /\ 0 <= cnt < 2 ^ 64 /\ 0 <= fail < 2 ^ 64 /\ (ran = 0 \/ ran = 1).
Proof.
intros ly S Hp W mem Lam peak cnt fail ran most own HLg.
exact (prh_ledger_bounds B ly S Hp W mem Lam peak cnt fail ran most own HLg).
Qed.

Lemma vrd_led_nodup : forall ly S Hp W mem Lam peak cnt fail ran most own,
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> NoDup (map fst Lam).
Proof.
intros ly S Hp W mem Lam peak cnt fail ran most own HLg.
exact (prh_ledger_nodup B ly S Hp W mem Lam peak cnt fail ran most own HLg).
Qed.

Lemma vrd_led_hblk : forall ly S Hp W mem Lam peak cnt fail ran most own a k,
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> In (a, k) Lam ->
  0 <= k /\ In (a - cf_head, k + cf_head) (ablocks B ly S) /\ a mod 16 = 0.
Proof.
intros ly S Hp W mem Lam peak cnt fail ran most own a k HLg Hin.
destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a k most own HLg Hin) as (H1 & H2 & _ & H4 & _).
split; [exact H1|]. split; [exact H2 | exact H4].
Qed.

(* fpre's fourth conjunct at row 53's `jal grow` (the old-pin kit: raZ regs < YM05.alloc_ceiling, PRH_Base.v blob
   9d555df6e93a): the return pc PI_GROWRET, listing slot 24096, is below the run's allocation ceiling - PRW_StepKit's
   ONE copy (pa_slot_lt_ceil_b) in a CLOSED goal with the instance named, as VrdIStep.v de23eae693b8's
   vi_grow_ret_slot_ceil does (inline, with the listing instance implicit, its vm_compute ran away: the S3 walk,
   2026-10-29) *)
Lemma vrd_growret_ceil : bv_unsigned (Z_to_bv 64 (BASE + (PI_GROWRET - A_prog_base))) < YM05.alloc_ceiling.
Proof.
  change (PI_GROWRET - A_prog_base) with 24096.
  pose proof (PRW_StepKit.pa_slot_lt_ceil_b (PL := PL_prog_A) (PI := PI_prog_A) 24096 ltac:(lia)
    ltac:(vm_compute; reflexivity)) as H.
  rewrite unsigned_lit_small; [exact H|]. change BASE with A_prog_base. unfold A_prog_base. lia.
Qed.

(* the shadow address of a byte, as rows 21-22 / 40-41 / 59-60 / 101-106 compute it *)
Definition shx (a : Z) : Z := SHADOW_OFF + a / 8.

(* ---- the stack budget: parse_items' own 144-byte frame plus grow's bound fit under STK_parse_items d ---- *)
Lemma vrd_stk_ge : forall d, PI_FRAME + STK_grow <= STK_parse_items d.
Proof.
intros d. destruct H_img as (H1 & H2 & H3). unfold STK_parse_items. rewrite H1.
assert (STK_grow <= LEAF_pv_pi) by (unfold LEAF_pv_pi, zmaxl; cbn [fold_right]; lia).
assert (0 <= Z.of_nat (PjGrammar.MAXD - d) * (pi_frame F_parse_value + PI_FRAME))
  by (apply Z.mul_nonneg_nonneg; unfold PI_FRAME; lia).
lia.
Qed.

(* the GOT word (A_OBJ 0) and the shadow-base cell (A_OBJ 12), which rows 17..19 read, are image bytes *)
Lemma vrd_cell_img : forall i x, (i = 0 \/ i = 12)%nat -> VAL (A_OBJ i) <= x < VAL (A_OBJ i) + 8 -> in_img segs x.
Proof.
intros i x Hi Hx.
destruct (find_segment segs (VAL (A_OBJ i)) 8) as [sg|] eqn:Ef;
  [| exfalso; destruct Hi as [-> | ->]; vm_compute in Ef; discriminate].
destruct (find_segment_hit segs _ _ _ Ef) as (Hin & H1 & H2). exists sg. split; [exact Hin | lia].
Qed.

(* the journal at the call's granted window: afn_pre_x at STK and the window fwin e give the EMPTY journal at
   (STK + e) (sp + e), which is the stack the frozen post of tparse_items_specX runs at *)
Lemma vrd_jinit : forall STK e FP ly S Hp W regs mem md ch,
  afn_pre_x segs B ARx STK ly S Hp W regs mem md ch -> fwin ly W regs mem e ->
  ajournal_x (SK := SK) segs B prh_pst ARx (STK + e) (spZ regs + e) FP ly S Hp W mem md [] ly S Hp W mem md 0.
Proof.
intros STK e FP ly S Hp W regs mem md ch (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT)
  (He0 & He16 & Hetop & Hepres).
pose proof Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
split; [exact HAR|]. split; [apply layout_le_refl|]. split; [lia|]. split; [apply wle_refl|].
split; [apply aos_step_refl|].
split; [reflexivity|]. split; [lia|]. split; [lia|].
split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
split; [intros; reflexivity|].
split; [intros pp nn i H1 H2; exfalso; exact (H2 H1)|].
split.
{ intros a Ha. destruct (Z_lt_le_dec a (spZ regs)); [apply Hpres; lia | apply Hepres; lia]. }
(* lia here cannot see `mod`: VrdPro.v turns Zify's euclidean-division flag off for the whole import graph, so the
   16-alignment of the widened window is proved by Z.add_mod, not by lia *)
assert (Hmod : (spZ regs + e) mod 16 = 0) by (rewrite Z.add_mod by lia; rewrite Hal, He16; reflexivity).
split; [unfold astk_ok; split; [exact Hmod|]; repeat split; lia|].
split; [intros; reflexivity|]. split; [exact HQT|]. rewrite app_nil_r. apply incl_refl.
Qed.

(* where the node v lives (prhReader_at's four places): none of its 56 bytes is an image byte, nor a byte of a live
   harness block's hidden head *)
Lemma vrd_v_place : forall ly S Hp W mem md Lam peak cnt fail ran most own regs e v,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  prhReader_at B ly S Lam regs e v 56 -> YM05.alloc_ceiling <= spZ regs ->
  forall a, v <= a < v + 56 ->
    ~ in_img segs a /\ (forall a0 k, In (a0, k) Lam -> ~ (a0 - cf_head <= a < a0)).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own regs e v HAR HL0 Hat Hsp a Ha.
pose proof cf_head_nonneg as Hh0.
assert (HLb : forall a0 k, In (a0, k) Lam -> 0 <= k /\ In (a0 - cf_head, k + cf_head) (ablocks B ly S)).
{ intros a0 k Hin. destruct (vrd_led_hblk ly S Hp W mem Lam peak cnt fail ran _ _ a0 k HL0 Hin) as (Hk & Hab & _).
  auto. }
assert (Hblk : forall b n, In (b, n) (ablocks B ly S) -> b + req_size n <= YM05.alloc_ceiling /\ (0 <= n -> n <= req_size n)).
{ intros b n Hin. destruct (alx_blocks segs B ARx LAWS ly S Hp W mem md b n HAR Hin) as (_ & _ & Hc & _).
  split; [exact Hc | intros Hn; exact (proj2 (req_size_pos n Hn))]. }
pose proof asan_consts as (C1 & _ & _ & _ & C5).
destruct Hat as [(a1 & k1 & Hin1 & Hlo & Hhi) | [(b & m & Hinb & Hnot & Hlo & Hhi) | [(cid & pos & Hf & Hlo & Hhi) | (Hlo & Hhi)]]].
- destruct (HLb a1 k1 Hin1) as (Hk1 & Hab1). destruct (Hblk _ _ Hab1) as (Hc1 & Hr1). specialize (Hr1 ltac:(lia)).
  split.
  + apply (blk_img_x segs B ARx LAWS ly S Hp W mem md (a1 - cf_head) (k1 + cf_head) a HAR Hab1). lia.
  + intros a0 k Hin0 Hr. destruct (Z.eq_dec a0 a1) as [->|Hne]; [lia|].
    destruct (HLb a0 k Hin0) as (Hk0 & Hab0). destruct (Hblk _ _ Hab0) as (Hc0 & Hr0). specialize (Hr0 ltac:(lia)).
    assert (Hd : (a0 - cf_head, k + cf_head) <> (a1 - cf_head, k1 + cf_head)) by (intros E; injection E; lia).
    pose proof (sep_blocks_x segs B ARx LAWS ly S Hp W mem md _ _ _ _ HAR Hab0 Hab1 Hd) as Hz.
    unfold zdisjoint in Hz. cbn [fst snd] in Hz. lia.
- destruct (Hblk _ _ Hinb) as (Hcb & Hrb). specialize (Hrb ltac:(lia)).
  split.
  + apply (blk_img_x segs B ARx LAWS ly S Hp W mem md b m a HAR Hinb). lia.
  + intros a0 k Hin0 Hr.
    destruct (HLb a0 k Hin0) as (Hk0 & Hab0). destruct (Hblk _ _ Hab0) as (Hc0 & Hr0). specialize (Hr0 ltac:(lia)).
    assert (Hd : (a0 - cf_head, k + cf_head) <> (b, m)).
    { intros E. injection E as E1 E2. apply Hnot. replace (b + cf_head) with a0 by lia.
      replace (m - cf_head) with k by lia. exact Hin0. }
    pose proof (sep_blocks_x segs B ARx LAWS ly S Hp W mem md _ _ _ _ HAR Hab0 Hinb Hd) as Hz.
    unfold zdisjoint in Hz. cbn [fst snd] in Hz. lia.
- split.
  + apply (frm_img_x segs B ARx LAWS ly S Hp W mem md cid pos a HAR Hf). lia.
  + intros a0 k Hin0 Hr.
    destruct (HLb a0 k Hin0) as (Hk0 & Hab0). destruct (Hblk _ _ Hab0) as (Hc0 & Hr0). specialize (Hr0 ltac:(lia)).
    pose proof (sep_block_frame_x segs B ARx LAWS ly S Hp W mem md _ _ _ _ HAR Hab0 Hf) as Hz.
    unfold zdisjoint in Hz. cbn [fst snd] in Hz. lia.
- split.
  + intros Hi. pose proof (@pa_segs_low _ _ PI_prog_A a Hi). lia.
  + intros a0 k Hin0 Hr.
    destruct (HLb a0 k Hin0) as (Hk0 & Hab0). destruct (Hblk _ _ Hab0) as (Hc0 & Hr0). specialize (Hr0 ltac:(lia)). lia.
Qed.

(* ---- the environment of the entry state: the registers, then the four extras the symbolic state names -
   SHADOW_OFF (atom 32, the value rows 17-19 load through the GOT), the cursor p (33), the text end (34) and the
   nesting depth d (35) ---- *)
Definition vrd_iE (regs : bvmap 5 word) (pp tl dd : Z) : env :=
  @Eimg _ A_prog_listing PI_prog_A (Ereg regs [w64 PI_SB; w64 pp; w64 tl; w64 dd]).

Lemma vrd_iE_reg : forall regs pp tl dd (r : bv 5) (n : nat), Z.of_nat n = bv_unsigned r ->
  ew (vrd_iE regs pp tl dd) n = getr regs r.
Proof.
intros regs pp tl dd r n Hn. unfold vrd_iE.
pose proof (bv_unsigned_in_range 5 r) as Hr. unfold bv_modulus in Hr. cbn in Hr.
rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ n r Hn).
Qed.

Lemma vrd_iE_img : forall regs pp tl dd n, (A_TEXT <= n < A_LIM)%nat ->
  ew (vrd_iE regs pp tl dd) n = Z_to_bv 64 (VAL n).
Proof. intros regs pp tl dd n Hn. unfold vrd_iE. apply Eimg_img. exact Hn. Qed.

Lemma vrd_sb : PI_SB = SHADOW_OFF.
Proof. reflexivity. Qed.

(* parse_items' entry pc, as the listing's own symbol address *)
Lemma vrd_ipc : A_prog_sigma AS_parse_items = PI_ENTRY.
Proof. vm_compute. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* vrd_ipost: the post of PRH_FnParse.tparse_items_specX (the kit's cut 7cdbb61b5fa0, PRH_FnParse.v blob f0d92dcec7e9), as a
   predicate on (W', c'): fpostWFb at the text's budget wbudget CW 0 (the cut's fpostWFbm without its m-keep) and at the
   text's post body VERBATIM, VrdIElem.vrd_items_q, the ONE copy the epilogue's conclusion states too. The memory keep
   of fpostWFbm is the generic invariant's (vrd_ipro_stmt_P's Pm), assembled at the function's top. There are NO
   room-position binders: the post-implication form quantifies the model run and position itself. *)
Definition vrd_ipost (d : nat) (o : bool) (q v text len p e : Z) (tb : list Z) (regs : bvmap 5 word)
  (ly : alayout) (Sa : astate) (Hp : list Z) (W : world segs) (mem : word -> option byte) (md : Model)
  (Lam : list (Z * Z)) (peak cnt fail ran most own : Z) : world segs -> config -> Prop :=
  fpostWFb B ARx SK (YCbqGwild.wbudget CW 0) (STK_parse_items d) e (rd_fp q v) regs ly Sa Hp W mem md
    (vrd_items_q B d o q v text len p tb ly Sa Lam peak cnt fail ran most own).

(* vrd_ipre: the premises of PRH_FnParse.tparse_items_specX d CTX CTX0 CW (the kit's cut 7cdbb61b5fa0, PRH_FnParse.v blob
   f0d92dcec7e9), verbatim and in the text's order, for one call, except the two premises the cut added for the cursor
   set CW (prh_cw_entry after prh_cur_entry, the wild room after rd_room): they are ONE trailing slot, so that every
   positional destruct of vrd_ipre gains exactly one name (VrdIElem.vrd_ient_ok carries them the same way). The text
   has no entry room position (post-implication form). The text's threaded hull premise (`hull_budget S` over the
   call's all-granted events, after the two live counts) is the slot's third component, so no positional destruct of
   vrd_ipre moves. *)
Definition vrd_ipre (d : nat) (CTX : list (list Z)) (o : bool)
  (ly : alayout) (Sa : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z))
  (Lam : list (Z * Z)) (peak cnt fail ran most own e q text len p : Z) (tb : list Z) (v : Z) : Prop :=
  fpre B ARx (STK_parse_items d) ly Sa Hp W regs mem md ch /\
  YAkMemnorm.memnorm segs mem /\
  In (raZ regs :: spine ch) CTX /\
  prh_univ_closure B CTX0 /\
  prh_cur_entry W mem regs q /\
  (exists ch', achain ly (aview segs (w_H W) mem) (spZ regs) (s0Z regs) ch' /\ spine ch' = spine ch) /\
  ((spZ regs <= q < spZ regs + 16) \/
   (spZ regs + 16 <= q /\ exists ch', achain ly (aview segs (w_H W) mem) (spZ regs) (prh_s0 F_parse_string q) ch')) /\
  getr regs 10 = w64 q /\ getr regs 11 = w64 v /\ getr regs 12 = w64 (if o then 1 else 0) /\
  rd_pre B (STK_parse_items d) ly Sa Hp W regs mem Lam peak cnt fail ran most own e q text len p d tb v /\
  p < text + len /\ nth_error tb (Z.to_nat (p - text)) = Some (if o then 123 else 91) /\
  rd_room Sa (prhPi_gtrace d o (rest_atR tb text p)) /\
  Z.of_nat (PresetRun.pkR YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf Sa))
    (PresetReqAt.rd_hevs (prhPi_gtrace d o (rest_atR tb text p)))) <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV /\
  Z.of_nat (PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf Sa))
    (PresetReqAt.rd_hevs (prhPi_gtrace d o (rest_atR tb text p)))) <= PresetLiveBounds.L24 + PresetLiveBounds.DRV /\
  (exists ch, achain ly (aview segs (w_H W) mem) (spZ regs - pi_frame F_parse_items) (prh_s0 F_parse_items q) ch) /\
  Z.of_nat (length (frames Sa)) + Z.of_nat (PjGrammar.MAXD - d) <= fs_frames 0 /\
  (prh_cw_entry B CW W mem regs q /\ YCbqGwild.wild_room (as_universe B) CW 0 (st_depot Sa) /\
   PresetHullBudget.hull_budget Sa (PresetReqAt.rd_hevs (prhPi_gtrace d o (rest_atR tb text p)))).

Lemma vrd_inv_true : srr_inv_laws segs (fun _ => True).
Proof. split; intros; exact I. Qed.

Lemma vrd_inv_call_true : srr_inv_call segs (fun _ => True).
Proof. intros m m' _ _. exact I. Qed.

Lemma vrd_fpostWF_inv : forall (Pm : (word -> option byte) -> Prop) STK e FP regs ly S Hp W mem md
    (Qb : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop) W' c',
  fpostWF (fx := fx) B ARx SK STK e FP regs ly S Hp W mem md
    (fun ly' S' Hp' W'' regs' mem' md' => Qb ly' S' Hp' W'' regs' mem' md' /\ Pm mem') W' c' ->
  fpostWF (fx := fx) B ARx SK STK e FP regs ly S Hp W mem md Qb W' c' /\ Pm (ms_mem (cfg_ms c')).
Proof.
intros Pm STK e FP regs ly S Hp W mem md Qb W' c' (fx' & ly' & S' & Hp' & regs' & mem' & md' & k & -> & H1 & H2 & H3 & H4 & H5 & HQ & HP).
split; [|exact HP].
exists fx', ly', S', Hp', regs', mem', md', k. split; [reflexivity|]. repeat (split; [eassumption|]). exact HQ.
Qed.

(* the re-hiding move: fpostWFb is at wle' segs RZ_cf (PRH_Base.v), so an unbudgeted post over a world relation R
   inside wle' (fpostWFR; fpostWF is it at wle) is the budgeted one at any budget predicate that admits [] *)
Lemma vrd_fpostWFb_ofR : forall (R : world segs -> world segs -> Prop),
  (forall W1 W2, R W1 W2 -> wle' segs YGcfRehidePost.RZ_cf W1 W2) ->
  forall (Pb : list (list Z) -> Prop) STK e FP regs ly S Hp W mem md
    (Qb : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop) W' c',
  Pb [] -> fpostWFR (fx := fx) B ARx SK R STK e FP regs ly S Hp W mem md Qb W' c' ->
  fpostWFb (fx := fx) B ARx SK Pb STK e FP regs ly S Hp W mem md Qb W' c'.
Proof.
intros R HR Pb STK e FP regs ly S Hp W mem md Qb W' c' HPb
  (fx' & ly' & S' & Hp' & regs' & mem' & md' & k & -> & H1 & H2 & H3 & H4 & H5 & HQ).
exists fx', ly', S', Hp', regs', mem', md', k, []. split; [reflexivity|]. split; [exact H1|]. split; [exact H2|].
split; [exact HPb|].
split; [exact (ajournal_xwR_mono segs B prh_pst ARx R (wle' segs YGcfRehidePost.RZ_cf) HR
                 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H3)|].
split; [exact H4|]. split; [exact H5 | exact HQ].
Qed.

(* a post at the empty budget is the budgeted one at any budget predicate that admits [] (the prologue's returning
   arms make no cursor free; YCbqGwild.fpostWF_xb_of_x over this file's spelling); its journal at wle lifts to wle' *)
Lemma vrd_fpostWFb_of : forall (Pb : list (list Z) -> Prop) STK e FP regs ly S Hp W mem md
    (Qb : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop) W' c',
  Pb [] -> fpostWF (fx := fx) B ARx SK STK e FP regs ly S Hp W mem md Qb W' c' ->
  fpostWFb (fx := fx) B ARx SK Pb STK e FP regs ly S Hp W mem md Qb W' c'.
Proof.
intros Pb STK e FP regs ly S Hp W mem md Qb W' c' HPb HQ.
exact (vrd_fpostWFb_ofR (@wle segs) (wle_wle' segs YGcfRehidePost.RZ_cf) Pb STK e FP regs ly S Hp W mem md Qb W' c'
  HPb HQ).
Qed.

(* vrd_fpostWF_inv over a world relation R *)
Lemma vrd_fpostWFR_inv : forall (R : world segs -> world segs -> Prop) (Pm : (word -> option byte) -> Prop) STK e FP
    regs ly S Hp W mem md
    (Qb : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop) W' c',
  fpostWFR (fx := fx) B ARx SK R STK e FP regs ly S Hp W mem md
    (fun ly' S' Hp' W'' regs' mem' md' => Qb ly' S' Hp' W'' regs' mem' md' /\ Pm mem') W' c' ->
  fpostWFR (fx := fx) B ARx SK R STK e FP regs ly S Hp W mem md Qb W' c' /\ Pm (ms_mem (cfg_ms c')).
Proof.
intros R Pm STK e FP regs ly S Hp W mem md Qb W' c'
  (fx' & ly' & S' & Hp' & regs' & mem' & md' & k & -> & H1 & H2 & H3 & H4 & H5 & HQ & HP).
split; [|exact HP].
exists fx', ly', S', Hp', regs', mem', md', k. split; [reflexivity|]. repeat (split; [eassumption|]). exact HQ.
Qed.

(* THE LIFT of a stretch at wle that ends in a segment at a wider relation R (R contains wle and is transitive): the
   runner stretches of this file run at wle, and the grow step after them is at wle' *)
Lemma vrd_srrG_lift : forall (R : world segs -> world segs -> Prop), (forall W1 W2, wle W1 W2 -> R W1 W2) ->
  (forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
  forall W c (Q : world segs -> config -> Prop), SRr segs W c (fun W' c' => SRrG segs R W' c' Q) -> SRrG segs R W c Q.
Proof.
intros R Hsub Htr W c Q H.
eapply (SRrG_bind segs R Htr); [exact (SRr_SRrG segs R Hsub W c _ H)|].
intros W' c' _ HQ. exact HQ.
Qed.

(* the empty budget is within every cursor set *)
Lemma vrd_wbudget_nil : forall CWx : list (list Z), YCbqGwild.wbudget CWx 0 [].
Proof. intros CWx. unfold YCbqGwild.wbudget, YCbqGwild.wfresh, YCbqGwild.wild_fresh. cbn. lia. Qed.

(* vrd_ipost's body (the inner Q of fpostWFb), as a name: vrd_ipost is fpostWFb at it, by reflexivity *)
Definition vrd_ipost_body (d : nat) (o : bool) (q v text len p : Z) (tb : list Z) (ly : alayout) (Sa : astate)
  (Lam : list (Z * Z)) (peak cnt fail ran most own : Z)
  : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  vrd_items_q B d o q v text len p tb ly Sa Lam peak cnt fail ran most own.

Lemma vrd_ipost_eq : forall d o q v text len p e tb regs ly Sa Hp W mem md Lam peak cnt fail ran most own,
  vrd_ipost d o q v text len p e tb regs ly Sa Hp W mem md Lam peak cnt fail ran most own =
  fpostWFb B ARx SK (YCbqGwild.wbudget CW 0) (STK_parse_items d) e (rd_fp q v) regs ly Sa Hp W mem md
    (vrd_ipost_body d o q v text len p tb ly Sa Lam peak cnt fail ran most own).
Proof. reflexivity. Qed.

(* the returning arms of the prologue make no cursor free: their journal is at the empty budget, so a stretch that
   ends in fpostWF at vrd_ipost's body ends in vrd_ipost (the kit's cut's budgeted post) *)
Lemma vrd_ipost_of_WF : forall (Pm : (word -> option byte) -> Prop) d o q v text len p e tb regs ly Sa Hp W mem md
    Lam peak cnt fail ran most own (W0 : world segs) c0,
  SRr segs W0 c0 (fun W' c' =>
    fpostWF B ARx SK (STK_parse_items d) e (rd_fp q v) regs ly Sa Hp W mem md
      (vrd_ipost_body d o q v text len p tb ly Sa Lam peak cnt fail ran most own) W' c' /\ Pm (ms_mem (cfg_ms c'))) ->
  SRr segs W0 c0 (fun W' c' =>
    vrd_ipost d o q v text len p e tb regs ly Sa Hp W mem md Lam peak cnt fail ran most own W' c' /\
    Pm (ms_mem (cfg_ms c'))).
Proof.
intros Pm d o q v text len p e tb regs ly Sa Hp W mem md Lam peak cnt fail ran most own W0 c0 H.
eapply SRr_mono; [exact H|]. intros W' c' _ (HQ & HP). split; [|exact HP].
apply vrd_fpostWFb_of; [exact (vrd_wbudget_nil CW) | exact HQ].
Qed.

Lemma vrd_ipre_prj : forall d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v,
  vrd_ipre d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v ->
  afn_pre_x segs B ARx (STK_parse_items d) ly Sa Hp W regs mem md ch /\
  arodata_okP segs pa_relro_lo pa_relro_hi B (aview segs (w_H W) mem) /\
  spZ regs + 64 <= ly_stk_hi ly /\
  frm_zero (@YK11.fp_csr fx) /\
  ARx ly Sa Hp W mem md /\
  spZ regs mod 16 = 0 /\ YM05.alloc_ceiling <= ly_stk_lo ly /\ ly_stk_lo ly + STK_parse_items d <= spZ regs /\
  spZ regs <= ly_stk_hi ly /\ ly_stk_hi ly <= 2 ^ 47 /\ spZ regs <= ly_top ly /\ ly_top ly <= ly_stk_hi ly /\
  (forall a, spZ regs - STK_parse_items d <= a < spZ regs -> apresent (w_H W) mem a) /\
  0 <= e /\ e mod 16 = 0 /\ spZ regs + e <= ly_top ly /\
  (forall a, spZ regs <= a < spZ regs + e -> apresent (w_H W) mem a) /\
  spZ regs <= q /\ q + 24 <= spZ regs + e /\ q mod 8 = 0 /\
  0 < text /\ text + len < 2 ^ 62 /\ text <= p <= text + len /\ Z.of_nat (length tb) = len /\
  (q + 24 <= text \/ text + len <= q) /\ (Z.of_nat d <= 32) /\
  4096 <= v /\ v mod 8 = 0 /\ amem_range v 56 /\
  (forall a, v <= a < v + 56 -> ~ aowned B ly Sa a /\ ~ (spZ regs - STK_parse_items d <= a < spZ regs)) /\
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF v 56 /\
  pj_zeroR segs (mrestrict (w_H W) mem) v /\ pj_rwR segs (mrestrict (w_H W) mem) v /\
  prhReader_at B ly Sa Lam regs e v 56 /\
  (q + 24 <= v \/ v + 56 <= q) /\ (text + len <= v \/ v + 56 <= text) /\ (v + 56 <= spZ regs \/ spZ regs + e <= v) /\
  prh_ledger B ly Sa Hp W mem Lam peak cnt fail ran most own /\
  (d <= PjGrammar.MAXD)%nat /\ cnt + 2 * Z.of_nat (length (rest_atR tb text p)) + 2 < 2 ^ 64 - 1 /\
  src_rd W mem text tb /\ prhReader_home B ly Sa Hp Lam text len /\
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF q 24 /\
  prh_cur_entry W mem regs q /\
  getr regs 10 = w64 q /\ getr regs 11 = w64 v /\ getr regs 12 = w64 (if o then 1 else 0) /\
  p < text + len /\ nth_error tb (Z.to_nat (p - text)) = Some (if o then 123 else 91) /\
  rd_room Sa (prhPi_gtrace d o (rest_atR tb text p)) /\
  Z.of_nat (length (frames Sa)) + Z.of_nat (PjGrammar.MAXD - d) <= fs_frames 0.
Proof.
intros d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v
  ((HPRE0 & HROD & Hshi64 & _) & HMN & HCTX & HUC & HCE & HCHI & HQCH & H10 & H11 & H12 & HRD & Hpe & Hop & HROOM & _ & _
   & HFU & HFR & HCWR).
destruct HRD as (Hfrm & Hmu & Hu1 & Hu2 & HIN & HWIN & Hspq & Hqe & HRAq & HSRC & HHOME & HMAX & HNODE & Hqv &
  Htv & Hvw & HLED & HdM & Hcnt).
destruct HIN as (Vp & Ve & Vd & RWq & Hq8 & Ht0 & Ht62 & Htp & Hlen & Hgt & Hqt & Hd32).
destruct HNODE as (Hv4096 & Hv8 & Hrwv & HZv & HATv & HAMv & HNv & HRAv).
pose proof HPRE0 as (HAR & Hra & Hra4 & Hgp & Htp' & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2).
pose proof HWIN as (He0 & He16 & Hetop & Hepres).
(* rd_pre's text / node conjunct is guarded by 0 < len; the opener at p < text + len gives it *)
specialize (Htv ltac:(lia)).
repeat (split; [first [eassumption | lia]|]). exact HFR.
Qed.

(* ============================================================================================================== *)
(* THE ENTRY STATE IS SOUND: ss_ipro abstracts parse_items' entry machine state under vrd_ipre, and the two shadow
   entries pi_SH are EXACTLY rd_pre's two range_addressable conjuncts (the cursor's 24 bytes and the node's 56).
   Every ASan check of the segment is discharged from these two alone - that is what makes every vrd_irun_* run
   end with sh_obls = [] and never reach an errpath_* slot.                                                       *)
(* ============================================================================================================== *)
Lemma vrd_ientry : forall d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v,
  vrd_ipre d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v ->
  st_ok_pi segs VAL (vrd_iE regs p (text + len) (Z.of_nat d)) ss_ipro
    (restrict (w_H W) (YK11.mkst regs (Z_to_bv 64 (BASE + (PI_ENTRY - A_prog_base))) mem (YK11.seg_rom segs)))
  /\ sh_ok segs pi_Bx pi_SH (vrd_iE regs p (text + len) (Z.of_nat d)) (mrestrict (w_H W) mem).
Proof.
intros d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v
  ((HPRE & HROD) & HMN & HCTX & HUC & HCE & HCHI & HQCH & H10 & H11 & H12 & HRD & Hpe & Hop & HROOM & HPKS & HPKL & HFU & HFR & HCWR).
destruct HRD as (Hfrm & Hmu & Hu1 & Hu2 & HIN & HWIN & Hspq & Hqe & HRAq & HSRC & HHOME & HMAX & HNODE & Hqv &
  Htv & Hvw & HLED & HdM & Hcnt).
destruct HIN as (Vp & Ve & Vd & RWq & Hq8 & Ht0 & Ht62 & Htp & Hlen & Hgt & Hqt & Hd32).
destruct HNODE as (Hv4096 & Hv8 & (Hvmod & RWv) & HZv & HATv & HAMv & HNv & HRAv).
destruct HSRC as (Hbt & Ht4096 & Htceil & Htamr & HRAt & Hhull).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp' & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof HWIN as (He0 & He16 & Hetop & Hepres).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (vrd_stk_ge d) as HSTK.
pose proof H_img as (Himg1 & Himg2 & Himg3).
unfold amem_range in HAMv.
rewrite Hlen in Htceil, Htamr.
assert (Rsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
assert (Rq : 4096 <= q /\ q + 24 <= 2 ^ 47) by lia.
assert (Rv : 4096 <= v /\ v + 56 <= 2 ^ 47) by (unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
assert (Rp : 4096 <= p /\ p <= 2 ^ 47) by lia.
assert (Rt : 4096 <= text + len /\ text + len <= 2 ^ 47) by lia.
set (E := vrd_iE regs p (text + len) (Z.of_nat d)) in *.
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (vrd_iE_reg regs _ _ _ 2%bv 2%nat eq_refl)).
assert (U2 : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (E10 : ew E 10 = w64 q)
  by (subst E; rewrite (vrd_iE_reg regs _ _ _ 10%bv 10%nat eq_refl); exact H10).
assert (U10 : bv_unsigned (ew E 10) = q) by (rewrite E10; apply unsigned_lit_small; lia).
assert (E11 : ew E 11 = w64 v)
  by (subst E; rewrite (vrd_iE_reg regs _ _ _ 11%bv 11%nat eq_refl); exact H11).
assert (U11 : bv_unsigned (ew E 11) = v) by (rewrite E11; apply unsigned_lit_small; lia).
assert (E12 : ew E 12 = w64 (if o then 1 else 0))
  by (subst E; rewrite (vrd_iE_reg regs _ _ _ 12%bv 12%nat eq_refl); exact H12).
assert (U12 : bv_unsigned (ew E 12) = (if o then 1 else 0))
  by (rewrite E12; apply unsigned_lit_small; destruct o; lia).
assert (E32 : ew E 32 = w64 PI_SB)
  by (subst E; unfold vrd_iE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 p)
  by (subst E; unfold vrd_iE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = w64 (text + len))
  by (subst E; unfold vrd_iE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = w64 (Z.of_nat d))
  by (subst E; unfold vrd_iE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (U32 : bv_unsigned (ew E 32) = SHADOW_OFF)
  by (rewrite E32; rewrite vrd_sb; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U33 : bv_unsigned (ew E 33) = p) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = text + len) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = Z.of_nat d) by (rewrite E35; apply unsigned_lit_small; lia).
pose proof (@pa_obj_img _ A_prog_listing PI_prog_A 0%nat ltac:(lia)) as Hg0.
pose proof (@pa_obj_img _ A_prog_listing PI_prog_A 12%nat ltac:(lia)) as Hg12.
change (@pa_lo _ A_prog_listing PI_prog_A) with IMG_LO in Hg0, Hg12.
change (@pa_hi _ A_prog_listing PI_prog_A) with IMG_TOP in Hg0, Hg12.
unfold IMG_LO, IMG_TOP in Hg0, Hg12.
pose proof (pal_got_cell B PAL) as Hgc.
destruct (alx_const segs B ARx LAWS ly Sa Hp W mem md HAR) as (Kcell & Kuar & Kgot & Kgotu).
rewrite (pal_got_shadow B PAL), (pal_cell B PAL) in Kgot. rewrite (pal_cell B PAL) in Kcell.
assert (VB : forall n w, ew E n = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some n) = w)
  by (intros n w Hn Hw; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hw).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by (subst E; apply vrd_iE_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (subst E; apply vrd_iE_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
(* the node is apart from parse_items' own frame window, and from the two image cells: no byte of it is an image
   byte (vrd_v_place), and both cells are image bytes (vrd_cell_img) *)
assert (Hvstk : v + 56 <= spZ regs - PI_FRAME \/ spZ regs <= v).
{ destruct (Z_le_gt_dec (v + 56) (spZ regs - PI_FRAME)) as [h|h]; [left; exact h|].
  destruct (Z_le_gt_dec (spZ regs) v) as [h2|h2]; [right; exact h2|].
  exfalso. destruct (HNv (Z.max v (spZ regs - PI_FRAME)) ltac:(unfold PI_FRAME in *; lia)) as (_ & Hw).
  apply Hw. unfold PI_FRAME in *. lia. }
assert (Hvimg : forall a, v <= a < v + 56 -> ~ in_img segs a).
{ intros a Ha.
  exact (proj1 (vrd_v_place ly Sa Hp W mem md Lam peak cnt fail ran most own regs e v HAR HLED HATv ltac:(lia) a Ha)). }
assert (Hvobj : forall i, (i = 0 \/ i = 12)%nat -> v + 56 <= VAL (A_OBJ i) \/ VAL (A_OBJ i) + 8 <= v).
{ intros i Hi. destruct (Z_le_gt_dec (v + 56) (VAL (A_OBJ i))) as [h|h]; [left; exact h|].
  destruct (Z_le_gt_dec (VAL (A_OBJ i) + 8) v) as [h2|h2]; [right; exact h2|].
  exfalso. apply (Hvimg (Z.max v (VAL (A_OBJ i)))); [lia|]. apply (vrd_cell_img i _ Hi). lia. }
pose proof (Hvobj 0%nat (or_introl eq_refl)) as Hv0.
pose proof (Hvobj 12%nat (or_intror eq_refl)) as Hv12.
rewrite restrict_mkst_fx.
split.
- unfold ss_ipro. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold pi_regions, stack_region, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite U2. split; [unfold PI_FRAME; lia|]. split; [lia|]. split; [|constructor].
      intros oo Hoo. apply (apresent_writable segs). apply Hpres. unfold PI_FRAME in *. lia.
    * rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by lia.
      split; [lia|]. split; [lia|]. split; [intros oo Hoo; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
        [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kgot).
    * rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by lia.
      split; [lia|]. split; [lia|]. split; [intros oo Hoo; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs E _ (VAL (A_OBJ 12)) 0 8 pi_Bx SHADOW_OFF);
        [cbn [sv_denot pi_Bx]; rewrite E32, Z.add_0_r, vrd_sb, Z_to_bv_bv_unsigned; reflexivity
        | unfold SHADOW_OFF; cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kcell).
    * cbn [base_val]. rewrite U10. split; [lia|]. split; [lia|]. split.
      { intros oo Hoo. apply RWq. lia. }
      constructor; [|constructor].
      apply (chunk_ok_val segs E _ q 0 8 (SOff 33%nat 0) p);
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact Vp.
    * cbn [base_val]. rewrite U10. split; [lia|]. split; [lia|]. split; [intros oo Hoo; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs E _ q 8 8 (SOff 34%nat 0) (text + len));
        [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      exact Ve.
    * cbn [base_val]. rewrite U10. split; [lia|]. split; [lia|]. split.
      { intros oo Hoo. apply RWq. lia. }
      constructor; [|constructor].
      apply (chunk_ok_val segs E _ q 16 4 (SOff 35%nat 0) (Z.of_nat d));
        [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      exact Vd.
    * cbn [base_val]. rewrite U11. split; [lia|]. split; [lia|]. split; [|constructor].
      intros oo Hoo. apply RWv. lia.
  + apply pairwise_disjoint_of_extents.
    unfold pi_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by lia.
    rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by lia.
    cbn [base_val]. rewrite U2, U10, U11.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold PI_FRAME in *. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [pi_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U10, U11, U12, U32, U33, U34, U35.
    unfold PI_SB, SHADOW_OFF.
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1.
    repeat split; try (rewrite Z.mod_1_r; reflexivity); try exact Hal16; try exact Hq8; try exact Hv8;
      try (destruct o; lia); try lia.
- assert (UB : U E pi_Bx = SHADOW_OFF)
    by (unfold pi_Bx; rewrite U_SOff, U32, Z.add_0_r; apply zcanon_id; unfold M64, SHADOW_OFF; lia).
  assert (UQ : U E (SOff 10%nat 0) = q)
    by (rewrite U_SOff, U10, Z.add_0_r; apply zcanon_id; unfold M64; lia).
  assert (UV : U E (SOff 11%nat 0) = v)
    by (rewrite U_SOff, U11, Z.add_0_r; apply zcanon_id; unfold M64; lia).
  unfold sh_ok, pi_SH. constructor; [|constructor; [|apply Forall_nil]].
  + unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite UB, UQ, Z.add_0_r, Z.sub_0_r.
    split; [exact HRAq|].
    intros a Ha. cbn [Z.min Z.max] in Ha. unfold SHADOW_OFF in *. lia.
  + unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite UB, UV, Z.add_0_r, Z.sub_0_r.
    split; [exact HRAv|].
    intros a Ha. cbn [Z.min Z.max] in Ha. unfold SHADOW_OFF in *. lia.
Qed.

(* the call's data, as one vrd_ient record: EXACTLY vrd_ipre's binders in MkIEnt's field order (most / own after
   ran), plus ie_ch2, the chain the LOOP's own calls run at (s0 = q inside parse_items, so the entry chain does not
   serve), and ie_CW, the text's cursor set CW (the kit's cut: the Section's CW, which vrd_ipre's trailing slot is about).
   This segment produces ch2, so vrd_ipro_stmt quantifies it existentially. *)
Definition vrd_ient_of (d : nat) (o : bool)
  (ly : alayout) (Sa : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z))
  (Lam : list (Z * Z)) (peak cnt fail ran most own e q text len p : Z) (tb : list Z) (v : Z)
  (ch2 : list (Z * Z * Z)) : vrd_ient :=
  MkIEnt ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p d tb v o ch2 CW.

(* vrd_ipro_stmt d CTX: THE SEGMENT LEMMA of this lane. From parse_items' entry, the segment either reaches the
   head of the element loop in the state vrd_ielem_a, or it returns, and then the call's own post holds: the three
   returning arms of the segment are the depth refusal (row 39), the empty container (rows 294..304) and the
   refusal of the first grow (row 92). The premises are tparse_items_specX's (the kit's cut 7cdbb61b5fa0, PRH_FnParse.v
   blob f0d92dcec7e9), vrd_ipre, with
   the text's binders `.. Lam peak cnt fail ran most own`; the POST-IMPLICATION form has no room-position binders
   and no entry position premise (a Theorem Labs lane's approval of this restatement, 2026-10-29). The segment crosses the first
   grow, whose text concludes SRr' segs RZ_cf, so the segment concludes SRr' (the re-hiding move). *)
Definition vrd_ipro_stmt (d : nat) (CTX : list (list Z)) : Prop :=
  forall ly Sa Hp W regs mem md ch e q text len p tb v (o : bool) Lam peak cnt fail ran most own,
  vrd_ipre d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v ->
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (pa_sigma AS_parse_items) regs mem md)
    (fun W' c' =>
       (exists ch2 P, W' = ip_W P /\ c' = vrd_cfg A_IELEM_SLOT P /\
          vrd_ielem_a B ARx SK
            (vrd_ient_of d o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v ch2) P)
       \/ vrd_ipost d o q v text len p e tb regs ly Sa Hp W mem md Lam peak cnt fail ran most own W' c').

(* the segment master and the empty container in the generic form *)
Definition vrd_ipro_stmt_P (Pm : (word -> option byte) -> Prop) (d : nat) (CTX : list (list Z)) : Prop :=
  forall ly Sa Hp W regs mem md ch e q text len p tb v (o : bool) Lam peak cnt fail ran most own,
  vrd_ipre d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v ->
  Pm mem ->
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (pa_sigma AS_parse_items) regs mem md)
    (fun W' c' =>
       ((exists ch2 P, W' = ip_W P /\ c' = vrd_cfg A_IELEM_SLOT P /\
          vrd_ielem_a B ARx SK
            (vrd_ient_of d o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v ch2) P)
       \/ vrd_ipost d o q v text len p e tb regs ly Sa Hp W mem md Lam peak cnt fail ran most own W' c') /\
       Pm (ms_mem (cfg_ms c'))).

(* vrd_iempty_stmt d CTX: THE EMPTY CONTAINER of the same segment. When the depth test passes and the first
   non-space byte after the opener is the container's closer, parse_items returns 0 at rows 294..325 with the node
   left as the zeroed JArr [] / JObj [], and the call's own post holds with res = Some (mk o [], r0). *)
Definition vrd_iempty_stmt (d : nat) (CTX : list (list Z)) : Prop :=
  forall ly Sa Hp W regs mem md ch e q text len p tb v (o : bool) Lam peak cnt fail ran most own r0,
  vrd_ipre d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v ->
  (d < PjGrammar.MAXD)%nat ->
  PjGrammar.skip (tl (rest_atR tb text p)) = PjGrammar.closer o :: r0 ->
  SRr segs W (cfg_at segs (pa_sigma AS_parse_items) regs mem md)
    (vrd_ipost d o q v text len p e tb regs ly Sa Hp W mem md Lam peak cnt fail ran most own).

Definition vrd_iempty_stmt_P (Pm : (word -> option byte) -> Prop) (d : nat) (CTX : list (list Z)) : Prop :=
  forall ly Sa Hp W regs mem md ch e q text len p tb v (o : bool) Lam peak cnt fail ran most own r0,
  vrd_ipre d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v ->
  (d < PjGrammar.MAXD)%nat ->
  PjGrammar.skip (tl (rest_atR tb text p)) = PjGrammar.closer o :: r0 ->
  Pm mem ->
  SRr segs W (cfg_at segs (pa_sigma AS_parse_items) regs mem md)
    (fun W' c' => vrd_ipost d o q v text len p e tb regs ly Sa Hp W mem md Lam peak cnt fail ran most own W' c' /\
       Pm (ms_mem (cfg_ms c'))).

(* ============================================================================================================== *)
(* THE WRITE PERMISSION of the segment's first stretch (rows 1..39): the thirteen register saves into the frame,
   the node's type word at row 30 and the cursor's depth word at row 37. Every byte of every write window of
   ss_ipro is admitted by the journal, in the form YC80xf's paj_run_xf takes (awr_ok_fr: awr_byte, or a byte the
   footprint names inside a frame of the journal's entry state). The node is the only case that needs the frame
   disjunct, and it needs it on exactly one of prhReader_at's four places - a CALLER's live fake frame.          *)
(* ============================================================================================================== *)
Lemma vrd_iawr : forall d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v,
  vrd_ipre d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v ->
  awr_ok_fr (vrd_iE regs p (text + len) (Z.of_nat d)) pi_regions
    (STK_parse_items d + e) (spZ regs + e) (rd_fp q v)
    (ablocks B ly Sa) (ablocks B ly Sa) Sa ly [].
Proof.
intros d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v
  ((HPRE & HROD) & HMN & HCTX & HUC & HCE & HCHI & HQCH & H10 & H11 & H12 & HRD & Hpe & Hop & HROOM & HPKS & HPKL & HFU & HFR & HCWR).
destruct HRD as (Hfrm & Hmu & Hu1 & Hu2 & HIN & HWIN & Hspq & Hqe & HRAq & HSRC & HHOME & HMAX & HNODE & Hqv &
  Htv & Hvw & HLED & HdM & Hcnt).
destruct HIN as (Vp & Ve & Vd & RWq & Hq8 & Ht0 & Ht62 & Htp & Hlen & Hgt & Hqt & Hd32).
destruct HNODE as (Hv4096 & Hv8 & (Hvmod & RWv) & HZv & HATv & HAMv & HNv & HRAv).
destruct HSRC as (Hbt & Ht4096 & Htceil & Htamr & HRAt & Hhull).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp' & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof HWIN as (He0 & He16 & Hetop & Hepres).
pose proof (vrd_stk_ge d) as HSTK.
pose proof H_img as (Himg1 & Himg2 & Himg3).
pose proof (@cf_head_nonneg cp) as Hh0.
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAMv.
set (E := vrd_iE regs p (text + len) (Z.of_nat d)) in *.
assert (U2 : bv_unsigned (ew E 2) = spZ regs)
  by (subst E; rewrite (vrd_iE_reg regs _ _ _ 2%bv 2%nat eq_refl); reflexivity).
assert (U10 : bv_unsigned (ew E 10) = q)
  by (subst E; rewrite (vrd_iE_reg regs _ _ _ 10%bv 10%nat eq_refl), H10; apply unsigned_lit_small; lia).
assert (U11 : bv_unsigned (ew E 11) = v)
  by (subst E; rewrite (vrd_iE_reg regs _ _ _ 11%bv 11%nat eq_refl), H11; apply unsigned_lit_small; lia).
intros a (r & Hin & Ha).
cbn [pi_regions In] in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]];
  cbn [stack_region got_regionP bcell_regionP YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Ha.
- (* the frame: the thirteen saves, inside parse_items' own window below the entry sp *)
  rewrite U2 in Ha. left. left. unfold PI_FRAME in *. lia.
- (* the GOT word: read-only *) exfalso. lia.
- (* the shadow-base cell: read-only *) exfalso. lia.
- (* the cursor's p word (rows 48, 71): in the caller's granted window *)
  rewrite U10 in Ha. left. left. lia.
- (* the cursor's end field: read-only *) exfalso. lia.
- (* the cursor's depth word (row 37): in the caller's granted window *)
  rewrite U10 in Ha. left. left. lia.
- (* the node's type word (row 30): prhReader_at's four places *)
  rewrite U11 in Ha.
  assert (HFPv : inFP (rd_fp q v) a)
    by (unfold rd_fp; exists (v, v + 56); split; [right; right; left; reflexivity | cbn [fst snd]; lia]).
  destruct HATv as [(a1 & k1 & Hin1 & Hlo & Hhi) | [(b & m & Hinb & Hnot & Hlo & Hhi) |
                   [(cid & pos & Hf & Hlo & Hhi) | (Hlo & Hhi)]]].
  + (* a live harness block: its hidden head is the allocator block *)
    destruct (vrd_led_hblk ly Sa Hp W mem Lam peak cnt fail ran _ _ a1 k1 HLED Hin1) as (Hk1 & Hab1 & _).
    assert (Hrq : k1 + cf_head <= req_size (k1 + cf_head))
      by (unfold req_size; destruct (Z.eqb_spec (k1 + cf_head) 0); lia).
    left. right. left. split; [exact HFPv|]. exists (a1 - cf_head), (k1 + cf_head). split; [exact Hab1 | lia].
  + (* a live allocator block that is not a harness block *)
    destruct (alx_blocks segs B ARx LAWS ly Sa Hp W mem md b m HAR Hinb) as (_ & Hb4096 & _ & _).
    assert (Hrq : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
    left. right. left. split; [exact HFPv|]. exists b, m. split; [exact Hinb | lia].
  + (* a CALLER's live fake frame: the case awr_byte alone cannot cover, and awr_ok_fr's second disjunct is it *)
    right. split; [exact HFPv|]. exists cid, pos. split; [exact Hf|].
    unfold frame_rng, in_zr. cbn [fst snd]. lia.
  + (* the granted extension of the caller's window *)
    left. left. lia.
Qed.

(* ============================================================================================================== *)
(* THE TRANSPORT TOOLKIT of the segment's straight-line stretches: which bytes a run over pi_regions' windows may
   write (pi_wr), what it keeps, and the facts its final symbolic state names.                                    *)
(* ============================================================================================================== *)

(* the bytes the stretches over pi_regions' windows may write: parse_items' own frame, the cursor's p word and depth
   word, the node's type word *)
Definition pi_wr (sp q v a : Z) : Prop :=
  sp - PI_FRAME <= a < sp \/ q <= a < q + 8 \/ q + 16 <= a < q + 20 \/ v <= a < v + 4.

Lemma vrd_iwr : forall regs pp tl dd q v a,
  bv_unsigned (getr regs 10) = q -> bv_unsigned (getr regs 11) = v ->
  in_wrange (vrd_iE regs pp tl dd) pi_regions a -> pi_wr (spZ regs) q v a.
Proof.
intros regs pp tl dd q v a H10 H11 (r & Hin & Ha).
assert (U2 : bv_unsigned (ew (vrd_iE regs pp tl dd) 2) = spZ regs)
  by (rewrite (vrd_iE_reg regs pp tl dd 2%bv 2%nat eq_refl); reflexivity).
assert (U10 : bv_unsigned (ew (vrd_iE regs pp tl dd) 10) = q)
  by (rewrite (vrd_iE_reg regs pp tl dd 10%bv 10%nat eq_refl); exact H10).
assert (U11 : bv_unsigned (ew (vrd_iE regs pp tl dd) 11) = v)
  by (rewrite (vrd_iE_reg regs pp tl dd 11%bv 11%nat eq_refl); exact H11).
cbn [pi_regions In] in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]];
  cbn [stack_region got_regionP bcell_regionP YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Ha;
  rewrite ?U2, ?U10, ?U11 in Ha; unfold pi_wr, PI_FRAME in *; lia.
Qed.

(* a run over a state with pi_regions' windows keeps every byte off pi_wr *)
Lemma vrd_ikeep : forall regs pp tl dd q v rs (m m' : word -> option byte),
  bv_unsigned (getr regs 10) = q -> bv_unsigned (getr regs 11) = v ->
  frame_of (vrd_iE regs pp tl dd) rs m m' -> skeleton rs = skeleton pi_regions ->
  forall x : word, ~ pi_wr (spZ regs) q v (bv_unsigned x) -> m' x = m x.
Proof.
intros regs pp tl dd q v rs m m' H10 H11 HF Hsk x Hx. apply HF. intros Hin. apply Hx.
apply (vrd_iwr regs pp tl dd q v _ H10 H11). eapply in_wrange_skeleton; [exact Hsk | exact Hin].
Qed.

(* the write permission of every later stretch over pi_regions' windows *)
Lemma vrd_iawr_sk : forall d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v rs,
  vrd_ipre d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v ->
  skeleton rs = skeleton pi_regions ->
  awr_ok_fr (vrd_iE regs p (text + len) (Z.of_nat d)) rs
    (STK_parse_items d + e) (spZ regs + e) (rd_fp q v)
    (ablocks B ly Sa) (ablocks B ly Sa) Sa ly [].
Proof.
intros d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v rs H Hsk a Ha.
apply (vrd_iawr d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v H).
eapply in_wrange_skeleton; [exact Hsk | exact Ha].
Qed.

(* bytes that keep their raw value keep every byte-level fact (VrdFrame.rd_keep) *)
Lemma vrd_rdkeep : forall (m m' : word -> option byte) (P : Z -> Prop),
  (forall a, P a -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) -> rd_keep segs m m' P.
Proof.
intros m m' P H. split; intros a Ha.
- unfold mbyte. rewrite (H a Ha). reflexivity.
- unfold writable_at, wview. rewrite (H a Ha). exact (fun h => h).
Qed.

(* a chunk of a region of a symbolic state names its value *)
Lemma vrd_chunk_val : forall E ss ms (H : word -> bool) r0 i o (w : N) sv vl,
  st_ok_pi segs VAL E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r0 ->
  In (YP09.mkChunk o (CVal w sv)) (YP09.r_chunks r0) ->
  sv_denot E sv = Z_to_bv 64 vl -> 0 <= vl < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
  val_mem segs (mrestrict H (ms_mem ms)) (base_val E (YP09.r_base r0) + o) (N.to_nat w) vl.
Proof.
intros E ss ms H r0 i o w sv vl HS Hi Hin Hv Hr Hw.
pose proof (st_ok_chunk segs E _ (restrict H ms) i r0 _ HS Hi Hin) as Hc.
exact (val_of_chunk_ok segs E _ _ o w sv vl Hc Hv Hr Hw).
Qed.
(* vrd_chunk_val at region i of a CONCRETE symbolic state: the region is found by eq_refl and the chunk's
   membership by computation, before the three value premises are left in VQ *)
Ltac vrd_chunk HS E MS H i o w sv vl VQ :=
  pose proof (vrd_chunk_val E _ MS H _ i o w sv vl HS eq_refl) as VQ;
  lazymatch type of VQ with ?A -> _ =>
    let HA := fresh "HA" in assert (HA : A) by (cbn; tauto); specialize (VQ HA); clear HA end.


(* the zeroed bytes of the node that a stretch keeps are still zero *)
Lemma vrd_zero_kept : forall (m m' : word -> option byte) v a (w : nat),
  pj_zeroR segs m v -> rd_keep segs m m' (fun x => a <= x < a + Z.of_nat w) ->
  v <= a -> a + Z.of_nat w <= v + 56 -> val_mem segs m' a w 0.
Proof.
intros m m' v a w Hz HK H1 H2.
exact (val_mem_keep segs m m' a w 0 (vrd_zero_val segs m v a w Hz H1 H2) HK).
Qed.

(* a node with only its type word set is a refused tree with no blocks, at every depth *)
Lemma vrd_hdr_fd : forall m lblk v ty (n : nat),
  pj_hdrR segs m v ty 0 0 0 0 0 0 -> pj_fdR segs m lblk n v [].
Proof.
intros m lblk v ty n HD.
assert (HS : forall (Pi : bool -> Z -> Z -> Z -> list (Z * Z) -> Prop), Pi false 0 0 0 [] ->
   pj_fshapeR segs m lblk Pi v []).
{ intros Pi HPi. split; [constructor|]. split; [intros bb x Hb; destruct Hb|].
  exists ty, 0, 0, 0, 0, 0, 0, false, [], [], [], [].
  split; [exact HD|].
  split; [left; split; reflexivity|].
  split; [left; split; [reflexivity | split; reflexivity]|].
  split; [left; split; [reflexivity | split; reflexivity]|].
  split; [apply Permutation_refl | exact HPi]. }
destruct n as [|n']; cbn [pj_fdR]; apply HS; [split; reflexivity | cbn [Z.to_nat pf_itemsR]; reflexivity].
Qed.

(* The kit's cut (FREEORD-NONE): the same node with its ORDER LIST (PRH_PjOrder.pj_foR, pj_fdR's twin), empty, at every
   depth *)
Lemma vrd_hdr_fo : forall m lblk v ty (n : nat),
  pj_hdrR segs m v ty 0 0 0 0 0 0 -> PRH_PjOrder.pj_foR segs m lblk n v [] [].
Proof.
intros m lblk v ty n HD.
assert (HS : forall (Pi : bool -> Z -> Z -> Z -> list (Z * Z) -> list (Z * Z) -> Prop), Pi false 0 0 0 [] [] ->
   PRH_PjOrder.pj_oshapeR segs m lblk Pi v [] []).
{ intros Pi HPi. split; [constructor|]. split; [intros bb x Hb; destruct Hb|].
  exists ty, 0, 0, 0, 0, 0, 0, false, [], [], [], [], [].
  split; [exact HD|].
  split; [left; split; reflexivity|].
  split; [left; split; [reflexivity | split; reflexivity]|].
  split; [left; split; [reflexivity | split; reflexivity]|].
  split; [apply Permutation_refl|]. split; [exact HPi | reflexivity]. }
destruct n as [|n']; cbn [PRH_PjOrder.pj_foR]; apply HS;
  [split; [reflexivity | split; reflexivity] | cbn [Z.to_nat PRH_PjOrder.pf_oitemsR]; split; reflexivity].
Qed.

(* ... and a node whose only block is its kids array (an object whose first grow moved kids and was refused the keys:
   PresetReqAt.gheld's first arm), its order list that one block, at every depth *)
Lemma vrd_hdr_fo_kids : forall m lblk v ty kids k cap (n : nat),
  pj_hdrR segs m v ty 0 0 kids 0 0 cap -> lblk kids k -> 0 <= k -> pj_apartR [(kids, k)] v ->
  PRH_PjOrder.pj_foR segs m lblk n v [(kids, k)] [(kids, k)].
Proof.
intros m lblk v ty kids k cap n HD Hk Hk0 HAP.
assert (HS : forall (Pi : bool -> Z -> Z -> Z -> list (Z * Z) -> list (Z * Z) -> Prop), Pi false kids 0 0 [] [] ->
   PRH_PjOrder.pj_oshapeR segs m lblk Pi v [(kids, k)] [(kids, k)]).
{ intros Pi HPi. unfold PRH_PjOrder.pj_oshapeR. refine (conj _ (conj HAP _)).
  { apply NoDup_ListNoDup. constructor; [intros [] | constructor]. }
  exists ty, 0, 0, kids, 0, 0, cap, false, [], [(kids, k)], [], [], [].
  split; [exact HD|].
  split; [left; split; reflexivity|].
  split; [right; exists k; split; [exact Hk | split; [lia | reflexivity]]|].
  split; [left; split; [reflexivity | split; reflexivity]|].
  split; [apply Permutation_refl|]. split; [exact HPi | reflexivity]. }
destruct n as [|n']; cbn [PRH_PjOrder.pj_foR]; apply HS;
  [split; [reflexivity | split; reflexivity] | cbn [Z.to_nat PRH_PjOrder.pf_oitemsR]; split; reflexivity].
Qed.

(* The kit's cut (CAP, PRH_Reader.pj_ncapR): the empty container's capacity word is 0 = ncap 0, and it has no kid
   (a Theorem Labs lane's B' twin PItems_head.v hd_ncap_empty, a working branch 34d46afa0965) *)
Lemma vrd_ncap_empty : forall m (o : bool) v ty,
  pj_hdrR segs m v ty 0 0 0 0 0 0 -> pj_ncapR segs m v (PjGrammar.mk o []).
Proof.
intros m o v ty (_ & _ & _ & _ & K & _ & _ & C).
destruct o; cbn [PjGrammar.mk pj_ncapR length PresetReqAt.ncap Z.of_nat];
  (split; [exact C | exists 0; split; [exact K | exact I]]).
Qed.

(* VrdIStep's vi_reg / vi_saved_reg, restated under the same names: they are Section-local there *)
Ltac vi_reg HS r Hr :=
  lazymatch type of HS with st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [sv_denot] in Hr; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Hr end.
Ltac vi_saved_reg HS j :=
  lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
    let Hr := fresh "Hr" in vi_reg HS r Hr; rewrite Hr;
    lazymatch goal with |- ew (vi_EI ?a ?b) _ = _ => exact (vi_ew_extra a b j ltac:(lia)) end end.

(* ============================================================================================================== *)
(* THE RETURN: rows 310..325 (`mv a0, s2`, the thirteen reloads, `addi sp, sp, 0x90`, `ret`) from ANY state at row
   310 whose frame holds the entry registers (VrdIStep.vi_saved) and whose s2 holds the result, to the record text's
   post fpostWF with any body Qb that holds of a0 = the result. The segment's two returning arms after the depth
   test (the empty container, the refused first grow) end here. A restatement of IelemD's VrdIStep.vi_iexit_ok
   without vrd_iframe's four spill slots, which these arms never write; its symbolic entry is VrdIStep's vi_st_ok
   at slot A_IEPI_SLOT, used as it stands.
   THE RE-HIDING MOVE: vrd_iretR is the return over a world relation R that contains wle (the journal at R, the post
   fpostWFR at R, SRrG at R; the runner's R form paj_run_xR). The empty container takes it at wle (fpostWFR at wle IS
   fpostWF); vrd_iret is it at wle', the refused arms after the first grow. *)
(* ============================================================================================================== *)
Lemma vrd_iretR : forall (R : world segs -> world segs -> Prop), (forall W1 W2, wle W1 W2 -> R W1 W2) ->
  (forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
  forall (fxP : YK11.FPState) d ly Sa Hp W regs0 mem md ch e q v
    (regs : bvmap 5 word) (W' : world segs) ly' S' Hp' mem' md' (k : Z) (res : Z)
    (Qb : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  afn_pre_x segs B ARx (STK_parse_items d) ly Sa Hp W regs0 mem md ch ->
  spZ regs = spZ regs0 - 144 -> vi_saved W' mem' regs0 ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 18 = w64 res ->
  ajournal_xR (SK := SK) segs B prh_pst ARx R (STK_parse_items d + e) (spZ regs0 + e) (rd_fp q v)
    ly Sa Hp W mem md [] ly' S' Hp' W' mem' md' k ->
  (forall a, spZ regs0 <= a < spZ regs0 + e -> ~ inFP (rd_fp q v) a ->
     aview segs (w_H W') mem' a = aview segs (w_H W) mem a) ->
  frm_zero (@YK11.fp_csr fxP) -> fregs_kept_x fx fxP ->
  (forall regs' md'', getr regs' 10 = w64 res -> aregs_preserved regs0 regs' -> Qb ly' S' Hp' W' regs' mem' md'') ->
  SRrG segs R W' (mkCfg (@YK11.mkst fxP regs (w64 (A_IPC A_IEPI_SLOT)) mem' (YK11.seg_rom segs)) md')
    (fpostWFR (fx := fx) B ARx SK R (STK_parse_items d) e (rd_fp q v) regs0 ly Sa Hp W mem md Qb).
Proof.
intros R Hsub Htr fxP d ly Sa Hp W regs0 mem md ch e q v regs W' ly' S' Hp' mem' md' k res Qb
  HPRE Hsp HSV Hgp Htp Hs2 HJ HWIN HFZ HFK HQ.
assert (Rr : forall W1, R W1 W1) by (intros W1; apply Hsub; apply wle_refl).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (vi_st_ok A_IEPI_SLOT fxP W' regs0 regs mem' Hsp ltac:(lia) ltac:(lia) HSV) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (vi_EI regs regs0)) by (unfold vi_EI; apply Eimg_env).
pose (RUN := paj_run_xR (fx := fxP) (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B prh_pst ARx LAWS R Rr Htr).
pose (RET := paj_ret_at (fx := fxP) (PL := PL_prog_A) (PI := PI_prog_A)).
paj_run_tok_x RUN HS HJ SHOK vi_Bspan;
  [eapply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]|].
match goal with ms0 : machine_state |- _ => rename ms0 into ms2 end.
assert (Hmeq : ms_mem ms2 = mem') by (apply functional_extensionality; exact (vi_frame_all _ _ _ HF)).
vi_reg HS (Z_to_bv 5 1) R1. vi_reg HS (Z_to_bv 5 10) R10.
assert (E1 : getr (ms_regs ms2) 1 = getr regs0 1).
{ transitivity (getr (ms_regs ms2) (Z_to_bv 5 1)); [reflexivity|]. rewrite R1.
  exact (vi_ew_extra regs regs0 0 ltac:(lia)). }
assert (A10 : getr (ms_regs ms2) 10 = w64 res).
{ transitivity (getr (ms_regs ms2) (Z_to_bv 5 10)); [reflexivity|].
  rewrite R10, (vi_ew_low regs regs0 18 (Z_to_bv 5 18) eq_refl). exact Hs2. }
assert (HPR : aregs_preserved regs0 (ms_regs ms2)).
{ intros r Hr. unfold acallee_saved in Hr.
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
               r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]].
  - vi_reg HS (Z_to_bv 5 2) R2. rewrite R2.
    rewrite (vi_ew_low regs regs0 2 (Z_to_bv 5 2) eq_refl).
    change (bv_unsigned (getr regs (Z_to_bv 5 2))) with (spZ regs). rewrite Hsp.
    replace (spZ regs0 - 144 + 144) with (spZ regs0) by lia.
    unfold spZ. apply Z_to_bv_bv_unsigned.
  - vi_reg HS (Z_to_bv 5 3) R3. rewrite R3, (vi_ew_low regs regs0 3 (Z_to_bv 5 3) eq_refl).
    etransitivity; [exact Hgp|]. symmetry. exact Hgp0.
  - vi_reg HS (Z_to_bv 5 4) R4. rewrite R4, (vi_ew_low regs regs0 4 (Z_to_bv 5 4) eq_refl).
    etransitivity; [exact Htp|]. symmetry. exact Htp0.
  - vi_saved_reg HS 1%nat.
  - vi_saved_reg HS 2%nat.
  - vi_saved_reg HS 3%nat.
  - vi_saved_reg HS 4%nat.
  - vi_saved_reg HS 5%nat.
  - vi_saved_reg HS 6%nat.
  - vi_saved_reg HS 7%nat.
  - vi_saved_reg HS 8%nat.
  - vi_saved_reg HS 9%nat.
  - vi_saved_reg HS 10%nat.
  - vi_saved_reg HS 11%nat.
  - vi_saved_reg HS 12%nat. }
apply (SRr_SRrG segs R Hsub).
eapply (RET W' _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat2. unfold fpostWFR. rewrite Hmeq. rewrite Hmeq in HJ.
lazymatch goal with |- exists _ _ _ _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?dd = _ /\ _ =>
  exists fxP, ly', S', Hp', r, m, dd, k end.
split; [unfold YK0s.ret_ok in Hra; rewrite E1, Hra; reflexivity|].
split; [exact HFZ|]. split; [exact HFK|].
split; [apply (ajournal_x_materializeR (SK := SK) segs B prh_pst ARx LAWS (@pa_segs_low _ _ PI_prog_A) R); exact HJ|].
split; [exact HWIN|]. split; [exact HPR|].
exact (HQ _ _ A10 HPR).
Qed.

(* the refused arms' return after the first grow: vrd_iretR at wle' *)
Lemma vrd_iret : forall (fxP : YK11.FPState) d ly Sa Hp W regs0 mem md ch e q v
    (regs : bvmap 5 word) (W' : world segs) ly' S' Hp' mem' md' (k : Z) (res : Z)
    (Qb : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  afn_pre_x segs B ARx (STK_parse_items d) ly Sa Hp W regs0 mem md ch ->
  spZ regs = spZ regs0 - 144 -> vi_saved W' mem' regs0 ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 18 = w64 res ->
  ajournal_xR (SK := SK) segs B prh_pst ARx (wle' segs YGcfRehidePost.RZ_cf) (STK_parse_items d + e) (spZ regs0 + e)
    (rd_fp q v) ly Sa Hp W mem md [] ly' S' Hp' W' mem' md' k ->
  (forall a, spZ regs0 <= a < spZ regs0 + e -> ~ inFP (rd_fp q v) a ->
     aview segs (w_H W') mem' a = aview segs (w_H W) mem a) ->
  frm_zero (@YK11.fp_csr fxP) -> fregs_kept_x fx fxP ->
  (forall regs' md'', getr regs' 10 = w64 res -> aregs_preserved regs0 regs' -> Qb ly' S' Hp' W' regs' mem' md'') ->
  SRr' segs YGcfRehidePost.RZ_cf W' (mkCfg (@YK11.mkst fxP regs (w64 (A_IPC A_IEPI_SLOT)) mem' (YK11.seg_rom segs)) md')
    (fpostWFR (fx := fx) B ARx SK (wle' segs YGcfRehidePost.RZ_cf) (STK_parse_items d) e (rd_fp q v) regs0 ly Sa Hp W
       mem md Qb).
Proof.
exact (vrd_iretR (wle' segs YGcfRehidePost.RZ_cf) (wle_wle' segs YGcfRehidePost.RZ_cf)
  (wle'_trans segs YGcfRehidePost.RZ_cf)).
Qed.

(* the return (rows 310..325) and the refusal tail of row 92 in the generic form: vrd_iretR / vrd_iref92 at a body
   that carries Pm of its memory (their Qb is arbitrary, so P rides in it), over the world relation R *)
Lemma vrd_iret_invR : forall (R : world segs -> world segs -> Prop), (forall W1 W2, wle W1 W2 -> R W1 W2) ->
  (forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
  forall (Pm : (word -> option byte) -> Prop), srr_inv_laws segs Pm ->
  forall (fxP : YK11.FPState) d ly Sa Hp W regs0 mem md ch e q v
    (regs : bvmap 5 word) (W' : world segs) ly' S' Hp' mem' md' (k : Z) (res : Z)
    (Qb : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  afn_pre_x segs B ARx (STK_parse_items d) ly Sa Hp W regs0 mem md ch ->
  spZ regs = spZ regs0 - 144 -> vi_saved W' mem' regs0 ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 18 = w64 res ->
  ajournal_xR (SK := SK) segs B prh_pst ARx R (STK_parse_items d + e) (spZ regs0 + e) (rd_fp q v)
    ly Sa Hp W mem md [] ly' S' Hp' W' mem' md' k ->
  (forall a, spZ regs0 <= a < spZ regs0 + e -> ~ inFP (rd_fp q v) a ->
     aview segs (w_H W') mem' a = aview segs (w_H W) mem a) ->
  frm_zero (@YK11.fp_csr fxP) -> fregs_kept_x fx fxP ->
  (forall regs' md'', getr regs' 10 = w64 res -> aregs_preserved regs0 regs' -> Qb ly' S' Hp' W' regs' mem' md'') ->
  Pm mem' ->
  SRrG segs R W' (mkCfg (@YK11.mkst fxP regs (w64 (A_IPC A_IEPI_SLOT)) mem' (YK11.seg_rom segs)) md')
    (fun W'' c' => fpostWFR (fx := fx) B ARx SK R (STK_parse_items d) e (rd_fp q v) regs0 ly Sa Hp W mem md Qb W'' c' /\
       Pm (ms_mem (cfg_ms c'))).
Proof.
intros R Hsub Htr Pm _ fxP d ly Sa Hp W regs0 mem md ch e q v regs W' ly' S' Hp' mem' md' k res Qb HPRE Hsp HSV Hgp
  Htp Hs2 HJ HWIN HFZ HFK HQ HPM.
eapply (SRrG_mono segs R).
- apply (vrd_iretR R Hsub Htr fxP d ly Sa Hp W regs0 mem md ch e q v regs W' ly' S' Hp' mem' md' k res
    (fun ly1 S1 Hp1 W1 regs1 mem1 md1 => Qb ly1 S1 Hp1 W1 regs1 mem1 md1 /\ Pm mem1) HPRE Hsp HSV Hgp Htp Hs2 HJ HWIN
    HFZ HFK).
  intros regs' md'' H10 HPR. exact (conj (HQ regs' md'' H10 HPR) HPM).
- intros W'' c' _ H. exact (vrd_fpostWFR_inv R _ _ _ _ _ _ _ _ _ _ _ _ _ _ H).
Qed.

(* vrd_iret_invR at wle' *)
Lemma vrd_iret_inv : forall (Pm : (word -> option byte) -> Prop), srr_inv_laws segs Pm ->
  forall (fxP : YK11.FPState) d ly Sa Hp W regs0 mem md ch e q v
    (regs : bvmap 5 word) (W' : world segs) ly' S' Hp' mem' md' (k : Z) (res : Z)
    (Qb : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  afn_pre_x segs B ARx (STK_parse_items d) ly Sa Hp W regs0 mem md ch ->
  spZ regs = spZ regs0 - 144 -> vi_saved W' mem' regs0 ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 18 = w64 res ->
  ajournal_xR (SK := SK) segs B prh_pst ARx (wle' segs YGcfRehidePost.RZ_cf) (STK_parse_items d + e) (spZ regs0 + e)
    (rd_fp q v) ly Sa Hp W mem md [] ly' S' Hp' W' mem' md' k ->
  (forall a, spZ regs0 <= a < spZ regs0 + e -> ~ inFP (rd_fp q v) a ->
     aview segs (w_H W') mem' a = aview segs (w_H W) mem a) ->
  frm_zero (@YK11.fp_csr fxP) -> fregs_kept_x fx fxP ->
  (forall regs' md'', getr regs' 10 = w64 res -> aregs_preserved regs0 regs' -> Qb ly' S' Hp' W' regs' mem' md'') ->
  Pm mem' ->
  SRr' segs YGcfRehidePost.RZ_cf W' (mkCfg (@YK11.mkst fxP regs (w64 (A_IPC A_IEPI_SLOT)) mem' (YK11.seg_rom segs)) md')
    (fun W'' c' => fpostWFR (fx := fx) B ARx SK (wle' segs YGcfRehidePost.RZ_cf) (STK_parse_items d) e (rd_fp q v)
       regs0 ly Sa Hp W mem md Qb W'' c' /\ Pm (ms_mem (cfg_ms c'))).
Proof.
exact (vrd_iret_invR (wle' segs YGcfRehidePost.RZ_cf) (wle_wle' segs YGcfRehidePost.RZ_cf)
  (wle'_trans segs YGcfRehidePost.RZ_cf)).
Qed.

(* ============================================================================================================== *)
(* MID-SEGMENT RE-ENTRY. The loop head (row 59) and the loop's exit (row 78) are entered by a symbolic state built
   from scratch out of facts about the CURRENT machine state, as VrdIStep.vi_st_ok builds the epilogue's: every
   register is an atom bound to the current register, except the five whose shadow arithmetic the engine must see
   (s1 = q + 16, s5 = shadow (q + 16), s6 = q + 8, s7 = shadow (q + 8), s11 = shadow q) and, at the loop head, a0 and
   a3 (the cursor); the thirteen saved words are atoms 32..44 (VrdIStep.vi_extras), the byte at the cursor is atom
   45 and the cursor atom 46. Measured by symbolic execution: from ss_iL every run leaves sh_obls = []; from ss_iX1
   the run stops at `beqz s3` and then at the closer test, whose match runs to `ret` and whose mismatch reaches
   `jal grow`; from ss_iX0 the run reaches `jal grow`. *)
(* ============================================================================================================== *)
Definition PI_X : Z := 0x873c8.   (* row 78, where every exit of the inlined skip_ws loop lands *)
Definition shxE (x : sv) : sv := SAlu ALU_ADD (SAlu ALU_SRL x (SLit 3)) (SOff 26 0).
Definition vrd_rX : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 9%bv (SOff 8 16)) 21%bv (shxE (SOff 8 16)))
    22%bv (SOff 8 8)) 23%bv (shxE (SOff 8 8))) 27%bv (shxE (SOff 8 0)).
Definition vrd_rL : list sv := sr_set (sr_set vrd_rX 10%bv (SOff 46 0)) 13%bv (SOff 46 0).
Definition vrd_rsQ : smem :=
  [ vi_frame_region;
    YP09.mkRegion (Some 8%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 46 0))];
    YP09.mkRegion (Some 8%nat) 8 16 8 8 [YP09.mkChunk 8 (CVal 8 (SOff 12 0))];
    YP09.mkRegion (Some 8%nat) 16 24 16 20 [YP09.mkChunk 16 (CVal 4 (SOff 11 1))] ].
Definition vrd_rgB : YP09.region := YP09.mkRegion (Some 46%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 45 0))].
Definition vrd_rsB : smem := vrd_rgB :: vrd_rsQ.
Definition vrd_fA : list (nat * afact) :=
  [ (2%nat, mkAF (2^46) (2^47) 4); (8%nat, mkAF 4096 (2^47 - 24) 3); (46%nat, mkAF 4096 (2^47 - 2) 0);
    (12%nat, mkAF 4096 (2^47 - 1) 0); (11%nat, mkAF 0 31 0); (19%nat, mkAF 0 1 0);
    (26%nat, mkAF PI_SB PI_SB 0); (45%nat, mkAF 0 255 0) ].
Definition vrd_fB : facts := mkFacts vrd_fA [mkAC BC_LTU (SOff 46 0) (SOff 12 0)] [].
Definition vrd_fE : facts := mkFacts vrd_fA [mkAC BC_GEU (SOff 46 0) (SOff 12 0)] [].
Definition ss_iL : sstate := mkSS (PI_SKIPHD - A_prog_base) vrd_rL vrd_rsB None vrd_fB.
Definition ss_iX1 : sstate := mkSS (PI_X - A_prog_base) vrd_rX vrd_rsB None vrd_fB.
Definition ss_iX0 : sstate := mkSS (PI_X - A_prog_base) vrd_rX vrd_rsQ None vrd_fE.
Definition vrd_iSH1 : list shent := [mkSHE 46 0 1; mkSHE 8 0 24].
Definition vrd_iSH0 : list shent := [mkSHE 8 0 24].
Definition vrd_iBx : sv := SOff 26 0.
Definition vrd_iEX (regs regs0 : bvmap 5 word) (c P : Z) : env :=
  @Eimg _ A_prog_listing PI_prog_A (Ereg regs (vi_extras regs0 ++ [w64 c; w64 P])).

Lemma vrd_iEX_reg : forall regs regs0 c P (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (vrd_iEX regs regs0 c P) n = getr regs r.
Proof.
intros regs regs0 c P n r Hn. unfold vrd_iEX.
assert (Hlt : (n < 32)%nat) by (pose proof (u5_range r); lia).
rewrite (Eimg_low (PI := PI_prog_A) _ n) by (unfold A_TEXT; lia).
exact (ew_Ereg_nat regs _ n r Hn).
Qed.
Lemma vrd_iEX_saved : forall regs regs0 c P j, (j < 13)%nat ->
  ew (vrd_iEX regs regs0 c P) (32 + j) = nth j (vi_extras regs0) (Z_to_bv 64 0).
Proof.
intros regs regs0 c P j Hj. unfold vrd_iEX.
rewrite (Eimg_low (PI := PI_prog_A) _ (32 + j)%nat) by (unfold A_TEXT; lia).
rewrite ew_Ereg_extra. apply app_nth1. unfold vi_extras. cbn [length]. exact Hj.
Qed.
Lemma vrd_iEX_c : forall regs regs0 c P, ew (vrd_iEX regs regs0 c P) 45 = w64 c.
Proof.
intros regs regs0 c P. unfold vrd_iEX.
rewrite (Eimg_low (PI := PI_prog_A) _ 45%nat) by (unfold A_TEXT; lia).
exact (ew_Ereg_extra regs _ 13).
Qed.
Lemma vrd_iEX_P : forall regs regs0 c P, ew (vrd_iEX regs regs0 c P) 46 = w64 P.
Proof.
intros regs regs0 c P. unfold vrd_iEX.
rewrite (Eimg_low (PI := PI_prog_A) _ 46%nat) by (unfold A_TEXT; lia).
exact (ew_Ereg_extra regs _ 14).
Qed.

(* the shadow address the engine computes, (x >> 3) + SHADOW_OFF *)
Lemma vrd_U_shx : forall E (n : nat) k x, ew E n = w64 x -> ew E 26 = w64 SHADOW_OFF ->
  0 <= x < 2 ^ 64 -> 0 <= x + k <= 2 ^ 47 -> U E (shxE (SOff n k)) = shx (x + k).
Proof.
intros E n k x Hn H26 Hx Hxk. unfold shxE, shx.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite U_SOff, U_SLit, U_SOff, Hn, H26. unfold w64.
rewrite (unsigned_lit_small x) by lia. rewrite (unsigned_lit_small SHADOW_OFF) by (unfold SHADOW_OFF; lia).
rewrite (zcanon_id (x + k)) by (unfold M64; lia). rewrite (zcanon_id 3) by (unfold M64; lia).
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (H8 : 0 <= (x + k) / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
rewrite (zcanon_id ((x + k) / 8)) by (unfold M64; lia).
rewrite (zcanon_id (SHADOW_OFF + 0)) by (unfold M64, SHADOW_OFF; lia).
rewrite Z.add_0_r, Z.add_comm. apply zcanon_id. unfold M64, SHADOW_OFF. lia.
Qed.

(* the registers of the exit state and of the loop head *)
Lemma vrd_iregs_X : forall regs regs0 c P q,
  getr regs 8 = w64 q -> getr regs 26 = w64 SHADOW_OFF -> 4096 <= q -> q + 24 <= 2 ^ 47 ->
  getr regs 9 = w64 (q + 16) -> getr regs 21 = w64 (shx (q + 16)) -> getr regs 22 = w64 (q + 8) ->
  getr regs 23 = w64 (shx (q + 8)) -> getr regs 27 = w64 (shx q) ->
  regs_ok (vrd_iEX regs regs0 c P) vrd_rX regs.
Proof.
intros regs regs0 c P q H8 H26 Hq1 Hq2 H9 H21 H22 H23 H27.
set (E := vrd_iEX regs regs0 c P).
assert (E8 : ew E 8 = w64 q) by (subst E; rewrite (vrd_iEX_reg regs regs0 c P 8 8%bv eq_refl); exact H8).
assert (E26 : ew E 26 = w64 SHADOW_OFF)
  by (subst E; rewrite (vrd_iEX_reg regs regs0 c P 26 26%bv eq_refl); exact H26).
assert (SH : forall k, 0 <= q + k <= 2 ^ 47 -> sv_denot E (shxE (SOff 8 k)) = w64 (shx (q + k))).
{ intros k Hk. rewrite denot_lit_U, (vrd_U_shx E 8 k q E8 E26 ltac:(lia) Hk). reflexivity. }
assert (OF : forall k, 0 <= q + k < 2 ^ 64 -> sv_denot E (SOff 8 k) = w64 (q + k)).
{ intros k Hk. rewrite denot_lit_U, U_SOff, E8. unfold w64. rewrite unsigned_lit_small by lia.
  rewrite zcanon_id by (unfold M64; lia).
  reflexivity. }
unfold vrd_rX.
apply regs_ok_rereg; [| reflexivity | rewrite (SH 0) by lia; rewrite Z.add_0_r; exact H27].
apply regs_ok_rereg; [| reflexivity | rewrite (SH 8) by lia; exact H23].
apply regs_ok_rereg; [| reflexivity | rewrite (OF 8) by lia; exact H22].
apply regs_ok_rereg; [| reflexivity | rewrite (SH 16) by lia; exact H21].
apply regs_ok_rereg; [| reflexivity | rewrite (OF 16) by lia; exact H9].
subst E. unfold vrd_iEX. apply regs_ok_Eimg_Ereg.
Qed.

Lemma vrd_iregs_L : forall regs regs0 c P q,
  getr regs 8 = w64 q -> getr regs 26 = w64 SHADOW_OFF -> 4096 <= q -> q + 24 <= 2 ^ 47 ->
  getr regs 9 = w64 (q + 16) -> getr regs 21 = w64 (shx (q + 16)) -> getr regs 22 = w64 (q + 8) ->
  getr regs 23 = w64 (shx (q + 8)) -> getr regs 27 = w64 (shx q) ->
  getr regs 10 = w64 P -> getr regs 13 = w64 P -> 0 <= P < 2 ^ 64 ->
  regs_ok (vrd_iEX regs regs0 c P) vrd_rL regs.
Proof.
intros regs regs0 c P q H8 H26 Hq1 Hq2 H9 H21 H22 H23 H27 H10 H13 HP.
assert (OP : sv_denot (vrd_iEX regs regs0 c P) (SOff 46 0) = w64 P).
{ rewrite denot_lit_U, U_SOff, vrd_iEX_P. unfold w64. rewrite unsigned_lit_small by lia.
  rewrite Z.add_0_r, zcanon_id by (unfold M64; lia).
  reflexivity. }
unfold vrd_rL.
apply regs_ok_rereg; [| reflexivity | rewrite OP; exact H13].
apply regs_ok_rereg; [| reflexivity | rewrite OP; exact H10].
exact (vrd_iregs_X regs regs0 c P q H8 H26 Hq1 Hq2 H9 H21 H22 H23 H27).
Qed.

(* what a re-entry at row 59 or row 78 needs of the machine state *)
Definition vrd_iat (regs regs0 : bvmap 5 word) (W : world segs) (M : word -> option byte) (o : bool)
  (q d text len P : Z) : Prop :=
  spZ regs = spZ regs0 - 144 /\ 2 ^ 46 <= spZ regs0 - 144 /\ spZ regs0 <= 2 ^ 47 /\ spZ regs0 mod 16 = 0 /\
  getr regs 8 = w64 q /\ getr regs 26 = w64 SHADOW_OFF /\ 4096 <= q /\ q + 24 <= 2 ^ 47 /\ spZ regs0 <= q /\
  q mod 8 = 0 /\
  getr regs 9 = w64 (q + 16) /\ getr regs 21 = w64 (shx (q + 16)) /\ getr regs 22 = w64 (q + 8) /\
  getr regs 23 = w64 (shx (q + 8)) /\ getr regs 27 = w64 (shx q) /\
  getr regs 11 = w64 d /\ 0 <= d <= 31 /\ getr regs 19 = w64 (if o then 1 else 0) /\
  getr regs 12 = w64 (text + len) /\ 4096 <= text + len <= 2 ^ 47 - 1 /\
  4096 <= P <= 2 ^ 47 - 2 /\ P + 1 <= spZ regs0 - 144 /\
  vi_saved W M regs0 /\
  val_mem segs (mrestrict (w_H W) M) q 8 P /\ val_mem segs (mrestrict (w_H W) M) (q + 8) 8 (text + len) /\
  val_mem segs (mrestrict (w_H W) M) (q + 16) 4 (d + 1) /\ rd_rw segs (mrestrict (w_H W) M) q 24 /\
  range_addressable (aview segs (w_H W) M) SHADOW_OFF q 24.

Lemma vrd_iframe_chunk : forall regs regs0 c P (W : world segs) M j, (j < 13)%nat -> vi_saved W M regs0 ->
  YP09.chunk_ok segs (vrd_iEX regs regs0 c P) (mrestrict (w_H W) M) (spZ regs0 - 144)
    (YP09.mkChunk (136 - 8 * Z.of_nat j) (CVal 8 (SOff (32 + j) 0))).
Proof.
intros regs regs0 c P W M j Hj HV.
apply (vi_chunk8 _ _ _ _ _ (nth j (vi_extras regs0) (Z_to_bv 64 0))).
- exact (vrd_iEX_saved regs regs0 c P j Hj).
- replace (spZ regs0 - 144 + (136 - 8 * Z.of_nat j)) with (spZ regs0 - 8 - 8 * Z.of_nat j) by lia.
  exact (HV j Hj).
Qed.

Lemma vrd_ist_Q : forall regs regs0 (W : world segs) M o q d text len P c,
  vrd_iat regs regs0 W M o q d text len P -> 0 <= c <= 255 ->
  Forall (region_ok segs (vrd_iEX regs regs0 c P) (mrestrict (w_H W) M)) vrd_rsQ /\
  zpairwise_disjoint (map (extent_of_region (vrd_iEX regs regs0 c P)) vrd_rsQ) /\
  zpairwise_disjoint (map (extent_of_region (vrd_iEX regs regs0 c P)) vrd_rsB) /\
  atoms_ok (vrd_iEX regs regs0 c P) vrd_fA.
Proof.
intros regs regs0 W M o q d text len P c
  (Hsp & Hs1 & Hs2 & Hs16 & H8 & H26 & Hq1 & Hq2 & Hq3 & Hq8 & H9 & H21 & H22 & H23 & H27 & H11 & Hd & H19 & H12 &
   He & HP1 & HP2 & HSV & Vp & Ve & Vd & RWq & HRAq) Hc.
set (E := vrd_iEX regs regs0 c P).
assert (U2 : bv_unsigned (ew E 2) = spZ regs0 - 144)
  by (subst E; rewrite (vrd_iEX_reg regs regs0 c P 2 2%bv eq_refl); exact Hsp).
assert (U8 : bv_unsigned (ew E 8) = q)
  by (subst E; rewrite (vrd_iEX_reg regs regs0 c P 8 8%bv eq_refl), H8; unfold w64; apply unsigned_lit_small; lia).
assert (U11 : bv_unsigned (ew E 11) = d)
  by (subst E; rewrite (vrd_iEX_reg regs regs0 c P 11 11%bv eq_refl), H11; unfold w64; apply unsigned_lit_small; lia).
assert (U12 : bv_unsigned (ew E 12) = text + len)
  by (subst E; rewrite (vrd_iEX_reg regs regs0 c P 12 12%bv eq_refl), H12; unfold w64; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = (if o then 1 else 0))
  by (subst E; rewrite (vrd_iEX_reg regs regs0 c P 19 19%bv eq_refl), H19; unfold w64; apply unsigned_lit_small;
      destruct o; lia).
assert (U26 : bv_unsigned (ew E 26) = SHADOW_OFF)
  by (subst E; rewrite (vrd_iEX_reg regs regs0 c P 26 26%bv eq_refl), H26; unfold w64; apply unsigned_lit_small;
      unfold SHADOW_OFF; lia).
assert (U46 : bv_unsigned (ew E 46) = P)
  by (subst E; rewrite vrd_iEX_P; unfold w64; apply unsigned_lit_small; lia).
assert (U45 : bv_unsigned (ew E 45) = c)
  by (subst E; rewrite vrd_iEX_c; unfold w64; apply unsigned_lit_small; lia).
split; [|split; [|split]].
- unfold vrd_rsQ. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, vi_frame_region;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U2. split; [lia|]. split; [lia|]. split; [intros oo Hoo; lia|].
    unfold vi_frame_chunks. repeat apply Forall_cons; try apply Forall_nil.
    * exact (vrd_iframe_chunk regs regs0 c P W M 0 ltac:(lia) HSV).
    * exact (vrd_iframe_chunk regs regs0 c P W M 1 ltac:(lia) HSV).
    * exact (vrd_iframe_chunk regs regs0 c P W M 2 ltac:(lia) HSV).
    * exact (vrd_iframe_chunk regs regs0 c P W M 3 ltac:(lia) HSV).
    * exact (vrd_iframe_chunk regs regs0 c P W M 4 ltac:(lia) HSV).
    * exact (vrd_iframe_chunk regs regs0 c P W M 5 ltac:(lia) HSV).
    * exact (vrd_iframe_chunk regs regs0 c P W M 6 ltac:(lia) HSV).
    * exact (vrd_iframe_chunk regs regs0 c P W M 7 ltac:(lia) HSV).
    * exact (vrd_iframe_chunk regs regs0 c P W M 8 ltac:(lia) HSV).
    * exact (vrd_iframe_chunk regs regs0 c P W M 9 ltac:(lia) HSV).
    * exact (vrd_iframe_chunk regs regs0 c P W M 10 ltac:(lia) HSV).
    * exact (vrd_iframe_chunk regs regs0 c P W M 11 ltac:(lia) HSV).
    * exact (vrd_iframe_chunk regs regs0 c P W M 12 ltac:(lia) HSV).
  + rewrite U8. split; [lia|]. split; [lia|]. split; [intros oo Hoo; apply RWq; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ q 0 8 (SOff 46%nat 0) P);
      [cbn [sv_denot]; rewrite U46, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact Vp.
  + rewrite U8. split; [lia|]. split; [lia|]. split; [intros oo Hoo; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ q 8 8 (SOff 12%nat 0) (text + len));
      [cbn [sv_denot]; rewrite U12, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
    exact Ve.
  + rewrite U8. split; [lia|]. split; [lia|]. split; [intros oo Hoo; apply RWq; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ q 16 4 (SOff 11%nat 1) (d + 1));
      [cbn [sv_denot]; rewrite U11; reflexivity | cbn; lia | cbn; lia |].
    exact Vd.
- unfold vrd_rsQ, vi_frame_region, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U8.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- unfold vrd_rsB, vrd_rgB, vrd_rsQ, vi_frame_region, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U8, U46.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- cbn [vrd_fA atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U2, U8, U46, U12, U11, U19, U26, U45.
  change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1.
  assert (Hsp16 : (spZ regs0 - 144) mod 16 = 0) by (rewrite Zminus_mod, Hs16; reflexivity).
  unfold PI_SB, SHADOW_OFF.
  repeat split; try (rewrite Z.mod_1_r; reflexivity); try exact Hsp16; try exact Hq8; try (destruct o; lia); try lia.
Qed.

(* the shadow entry of the cursor struct, at every re-entry *)
Lemma vrd_ish_q : forall regs regs0 (W : world segs) M o q d text len P c,
  vrd_iat regs regs0 W M o q d text len P ->
  shent_ok segs vrd_iBx (vrd_iEX regs regs0 c P) (mrestrict (w_H W) M) (mkSHE 8 0 24).
Proof.
intros regs regs0 W M o q d text len P c HAT.
pose proof HAT as (Hsp & Hs1 & Hs2 & Hs16 & H8 & H26 & Hq1 & Hq2 & Hq3 & _).
pose proof HAT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & HRAq).
assert (UB : U (vrd_iEX regs regs0 c P) vrd_iBx = SHADOW_OFF).
{ unfold vrd_iBx. rewrite U_SOff, (vrd_iEX_reg regs regs0 c P 26 26%bv eq_refl), H26. unfold w64.
  rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). rewrite Z.add_0_r. apply zcanon_id. unfold M64, SHADOW_OFF; lia. }
assert (UQ : U (vrd_iEX regs regs0 c P) (SOff 8%nat 0) = q).
{ rewrite U_SOff, (vrd_iEX_reg regs regs0 c P 8 8%bv eq_refl), H8. unfold w64.
  rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. apply zcanon_id. unfold M64; lia. }
unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite UB, UQ, Z.add_0_r, Z.sub_0_r.
split; [exact HRAq|].
intros a Ha. cbn [Z.min Z.max] in Ha. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). unfold SHADOW_OFF in *. lia.
Qed.

(* the exit state when the cursor reached the end (row 78, P = text + len) *)
Lemma vrd_ist_X0 : forall regs regs0 (W : world segs) M o q d text len P,
  vrd_iat regs regs0 W M o q d text len P -> text + len <= P ->
  st_ok_pi segs VAL (vrd_iEX regs regs0 0 P) ss_iX0
    (restrict (w_H W) (YK11.mkst regs (Z_to_bv 64 (BASE + (PI_X - A_prog_base))) M (YK11.seg_rom segs))) /\
  sh_ok segs vrd_iBx vrd_iSH0 (vrd_iEX regs regs0 0 P) (mrestrict (w_H W) M).
Proof.
intros regs regs0 W M o q d text len P HAT HP.
pose proof HAT as (Hsp & Hs1 & Hs2 & Hs16 & H8 & H26 & Hq1 & Hq2 & Hq3 & Hq8 & H9 & H21 & H22 & H23 & H27 & H11 & Hd &
  H19 & H12 & He & HP1 & HP2 & _).
destruct (vrd_ist_Q regs regs0 W M o q d text len P 0 HAT ltac:(lia)) as (HRS & HDQ & _ & HAF).
split; [|constructor; [exact (vrd_ish_q regs regs0 W M o q d text len P 0 HAT) | apply Forall_nil]].
rewrite restrict_mkst_fx. unfold ss_iX0. apply pa_entry_st_ok_full.
- exact (vrd_iregs_X regs regs0 0 P q H8 H26 Hq1 Hq2 H9 H21 H22 H23 H27).
- vm_compute. reflexivity.
- exact HRS.
- apply pairwise_disjoint_of_extents. exact HDQ.
- split; [exact HAF|]. split; [|exact I].
  cbn [vrd_fE f_conds conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b].
  rewrite branch_geu_U, !U_SOff, vrd_iEX_P, (vrd_iEX_reg regs regs0 0 P 12 12%bv eq_refl), H12. unfold w64.
  rewrite !unsigned_lit_small by lia. rewrite !Z.add_0_r, !zcanon_id by (unfold M64; lia).
  apply negb_true_iff, Z.ltb_ge. exact HP.
Qed.

(* the byte at the cursor, for the two states that hold it *)
Lemma vrd_ist_B : forall regs regs0 (W : world segs) M o q d text len P c,
  vrd_iat regs regs0 W M o q d text len P -> 0 <= c <= 255 ->
  val_mem segs (mrestrict (w_H W) M) P 1 c ->
  region_ok segs (vrd_iEX regs regs0 c P) (mrestrict (w_H W) M) vrd_rgB.
Proof.
intros regs regs0 W M o q d text len P c HAT Hc Vc.
pose proof HAT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP1 & HP2 & _).
unfold region_ok, vrd_rgB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite vrd_iEX_P. unfold w64. rewrite unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros oo Hoo; lia|].
constructor; [|constructor].
apply (chunk_ok_val segs _ _ P 0 1 (SOff 45%nat 0) c);
  [cbn [sv_denot]; rewrite vrd_iEX_c; unfold w64; rewrite unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity
  | cbn; lia | cbn; lia |].
rewrite Z.add_0_r. exact Vc.
Qed.

Lemma vrd_ish_P : forall regs regs0 (W : world segs) M o q d text len P c,
  vrd_iat regs regs0 W M o q d text len P ->
  range_addressable (aview segs (w_H W) M) SHADOW_OFF P 1 ->
  (P < SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= P) ->
  shent_ok segs vrd_iBx (vrd_iEX regs regs0 c P) (mrestrict (w_H W) M) (mkSHE 46 0 1).
Proof.
intros regs regs0 W M o q d text len P c HAT HRA HAP.
pose proof HAT as (_ & _ & _ & _ & _ & H26 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP1 & HP2 & _).
assert (UB : U (vrd_iEX regs regs0 c P) vrd_iBx = SHADOW_OFF).
{ unfold vrd_iBx. rewrite U_SOff, (vrd_iEX_reg regs regs0 c P 26 26%bv eq_refl), H26. unfold w64.
  rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). rewrite Z.add_0_r. apply zcanon_id. unfold M64, SHADOW_OFF; lia. }
assert (UP : U (vrd_iEX regs regs0 c P) (SOff 46%nat 0) = P).
{ rewrite U_SOff, vrd_iEX_P. unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. apply zcanon_id.
  unfold M64; lia. }
unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite UB, UP, Z.add_0_r, Z.sub_0_r.
split; [exact HRA|].
intros a Ha. cbn [Z.min Z.max] in Ha. lia.
Qed.

(* the exit state with a byte at the cursor (row 78, P < text + len) *)
Lemma vrd_ist_X1 : forall regs regs0 (W : world segs) M o q d text len P c,
  vrd_iat regs regs0 W M o q d text len P -> P < text + len -> 0 <= c <= 255 ->
  val_mem segs (mrestrict (w_H W) M) P 1 c ->
  range_addressable (aview segs (w_H W) M) SHADOW_OFF P 1 -> (P < SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= P) ->
  st_ok_pi segs VAL (vrd_iEX regs regs0 c P) ss_iX1
    (restrict (w_H W) (YK11.mkst regs (Z_to_bv 64 (BASE + (PI_X - A_prog_base))) M (YK11.seg_rom segs))) /\
  sh_ok segs vrd_iBx vrd_iSH1 (vrd_iEX regs regs0 c P) (mrestrict (w_H W) M).
Proof.
intros regs regs0 W M o q d text len P c HAT HP Hc Vc HRA HAP.
pose proof HAT as (Hsp & Hs1 & Hs2 & Hs16 & H8 & H26 & Hq1 & Hq2 & Hq3 & Hq8 & H9 & H21 & H22 & H23 & H27 & H11 & Hd &
  H19 & H12 & He & HP1 & HP2 & _).
destruct (vrd_ist_Q regs regs0 W M o q d text len P c HAT Hc) as (HRS & _ & HDB & HAF).
split.
2:{ constructor; [exact (vrd_ish_P regs regs0 W M o q d text len P c HAT HRA HAP)|].
    constructor; [exact (vrd_ish_q regs regs0 W M o q d text len P c HAT) | apply Forall_nil]. }
rewrite restrict_mkst_fx. unfold ss_iX1. apply pa_entry_st_ok_full.
- exact (vrd_iregs_X regs regs0 c P q H8 H26 Hq1 Hq2 H9 H21 H22 H23 H27).
- vm_compute. reflexivity.
- constructor; [exact (vrd_ist_B regs regs0 W M o q d text len P c HAT Hc Vc) | exact HRS].
- apply pairwise_disjoint_of_extents. exact HDB.
- split; [exact HAF|]. split; [|exact I].
  cbn [vrd_fB f_conds conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b].
  rewrite branch_ltu_U, !U_SOff, vrd_iEX_P, (vrd_iEX_reg regs regs0 c P 12 12%bv eq_refl), H12. unfold w64.
  rewrite !unsigned_lit_small by lia. rewrite !Z.add_0_r, !zcanon_id by (unfold M64; lia).
  apply Z.ltb_lt. exact HP.
Qed.

(* the loop head (row 59): the exit state's pieces with a0 = a3 = the cursor *)
Lemma vrd_ist_L : forall regs regs0 (W : world segs) M o q d text len P c,
  vrd_iat regs regs0 W M o q d text len P -> P < text + len -> 0 <= c <= 255 ->
  val_mem segs (mrestrict (w_H W) M) P 1 c ->
  range_addressable (aview segs (w_H W) M) SHADOW_OFF P 1 -> (P < SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= P) ->
  getr regs 10 = w64 P -> getr regs 13 = w64 P ->
  st_ok_pi segs VAL (vrd_iEX regs regs0 c P) ss_iL
    (restrict (w_H W) (YK11.mkst regs (Z_to_bv 64 (BASE + (PI_SKIPHD - A_prog_base))) M (YK11.seg_rom segs))) /\
  sh_ok segs vrd_iBx vrd_iSH1 (vrd_iEX regs regs0 c P) (mrestrict (w_H W) M).
Proof.
intros regs regs0 W M o q d text len P c HAT HP Hc Vc HRA HAP H10 H13.
pose proof HAT as (Hsp & Hs1 & Hs2 & Hs16 & H8 & H26 & Hq1 & Hq2 & Hq3 & Hq8 & H9 & H21 & H22 & H23 & H27 & H11 & Hd &
  H19 & H12 & He & HP1 & HP2 & _).
destruct (vrd_ist_Q regs regs0 W M o q d text len P c HAT Hc) as (HRS & _ & HDB & HAF).
split.
2:{ constructor; [exact (vrd_ish_P regs regs0 W M o q d text len P c HAT HRA HAP)|].
    constructor; [exact (vrd_ish_q regs regs0 W M o q d text len P c HAT) | apply Forall_nil]. }
rewrite restrict_mkst_fx. unfold ss_iL. apply pa_entry_st_ok_full.
- exact (vrd_iregs_L regs regs0 c P q H8 H26 Hq1 Hq2 H9 H21 H22 H23 H27 H10 H13 ltac:(lia)).
- vm_compute. reflexivity.
- constructor; [exact (vrd_ist_B regs regs0 W M o q d text len P c HAT Hc Vc) | exact HRS].
- apply pairwise_disjoint_of_extents. exact HDB.
- split; [exact HAF|]. split; [|exact I].
  cbn [vrd_fB f_conds conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b].
  rewrite branch_ltu_U, !U_SOff, vrd_iEX_P, (vrd_iEX_reg regs regs0 c P 12 12%bv eq_refl), H12. unfold w64.
  rewrite !unsigned_lit_small by lia. rewrite !Z.add_0_r, !zcanon_id by (unfold M64; lia).
  apply Z.ltb_lt. exact HP.
Qed.

(* the write windows of the re-entry states are the cursor's p word and depth word, under any environment that
   binds atom 8 to the cursor struct (a run's fresh atoms leave it alone) *)
Lemma vrd_iwrB : forall (E : env) q a,
  ew E 8 = w64 q -> 0 <= q < 2 ^ 64 ->
  in_wrange E vrd_rsB a -> q <= a < q + 8 \/ q + 16 <= a < q + 20.
Proof.
intros E q a H8 Hq (r & Hin & Ha).
assert (U8 : bv_unsigned (ew E 8) = q) by (rewrite H8; unfold w64; apply unsigned_lit_small; lia).
cbn [vrd_rsB vrd_rsQ In] in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]];
  cbn [vrd_rgB vi_frame_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?U8 in Ha; lia.
Qed.

Lemma vrd_ikeepB : forall (E : env) q rs (m m' : word -> option byte),
  ew E 8 = w64 q -> 0 <= q < 2 ^ 64 ->
  frame_of E rs m m' -> (skeleton rs = skeleton vrd_rsB \/ skeleton rs = skeleton vrd_rsQ) ->
  forall x : word, ~ (q <= bv_unsigned x < q + 8 \/ q + 16 <= bv_unsigned x < q + 20) -> m' x = m x.
Proof.
intros E q rs m m' H8 Hq HF Hsk x Hx. apply HF. intros Hin. apply Hx.
apply (vrd_iwrB E q _ H8 Hq).
destruct Hsk as [Hsk|Hsk]; [eapply in_wrange_skeleton; [exact Hsk | exact Hin]|].
destruct (in_wrange_skeleton _ rs vrd_rsQ _ Hsk Hin) as (r & Hr & Ha). exists r. split; [right; exact Hr | exact Ha].
Qed.

Lemma vrd_iawrB : forall (E : env) q rs STK sp0 FP bl0 blc S ly (own : list (Z * Z)),
  ew E 8 = w64 q -> 0 <= q < 2 ^ 64 -> sp0 - STK <= q -> q + 24 <= sp0 ->
  (skeleton rs = skeleton vrd_rsB \/ skeleton rs = skeleton vrd_rsQ) ->
  awr_ok_fr E rs STK sp0 FP bl0 blc S ly own.
Proof.
intros E q rs STK sp0 FP bl0 blc S ly own H8 Hq H1 H2 Hsk a Ha.
left. left.
assert (Hb : in_wrange E vrd_rsB a).
{ destruct Hsk as [Hsk|Hsk]; [eapply in_wrange_skeleton; [exact Hsk | exact Ha]|].
  destruct (in_wrange_skeleton _ rs vrd_rsQ _ Hsk Ha) as (r & Hr & Hra). exists r. split; [right; exact Hr | exact Hra]. }
destruct (vrd_iwrB E q a H8 Hq Hb); lia.
Qed.

(* vrd_ikeepB with the run's frame fact first, so that the environment is fixed before the side conditions *)
Lemma vrd_ikeepF : forall (E : env) q rs (m m' : word -> option byte),
  frame_of E rs m m' -> ew E 8 = w64 q -> 0 <= q < 2 ^ 64 ->
  (skeleton rs = skeleton vrd_rsB \/ skeleton rs = skeleton vrd_rsQ) ->
  forall x : word, ~ (q <= bv_unsigned x < q + 8 \/ q + 16 <= bv_unsigned x < q + 20) -> m' x = m x.
Proof. intros E q rs m m' HF H8 Hq Hsk. exact (vrd_ikeepB E q rs m m' H8 Hq HF Hsk). Qed.

(* the keep fact of one run over a re-entry state; E8X binds atom 8 under the entry environment *)
Ltac vrd_kq HFr E8X q K :=
  pose proof (vrd_ikeepF _ q _ _ _ HFr) as K;
  specialize (K ltac:(rewrite ?ew_ewset_other by lia; exact E8X) ltac:(lia));
  lazymatch type of K with ?A -> _ =>
    let HA := fresh "HA" in assert (HA : A) by (left; vm_compute; reflexivity); specialize (K HA); clear HA end.

(* a run's fresh atoms are at or above 512: they leave the re-entry atoms alone *)
Lemma vrd_regs_ok_ext : forall E E' sr regs,
  regs_ok E sr regs -> (forall n, (n < 512)%nat -> ew E' n = ew E n) -> ed E' = ed E ->
  regs_atoms_lt 512 sr = true -> regs_ok E' sr regs.
Proof.
intros E E' sr regs HR H1 H2 Ha. apply (regs_ok_agree 512 E E' sr regs); [split; assumption | exact Ha | exact HR].
Qed.
(* the registers a run carried, at the run's final environment *)
Ltac vrd_rk HS HRK RK :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?E' _ _ => pose proof (vrd_regs_ok_ext _ E' _ _ HRK) as RK
  | st_ok _ ?E' _ _ => pose proof (vrd_regs_ok_ext _ E' _ _ HRK) as RK
  end;
  specialize (RK ltac:(let n0 := fresh "n" in let Hn0 := fresh "Hn" in intros n0 Hn0;
                       rewrite ?ew_ewset_other by lia; reflexivity) ltac:(reflexivity)
    ltac:(vm_compute; reflexivity)).


(* ---- the facts every re-entry state carries, relative to the call's entry ---- *)
Definition vrd_imid (d : nat) (o : bool) (e q text len v : Z) (regs0 : bvmap 5 word) (ly : alayout) (Sa : astate)
  (Hp : list Z) (W : world segs) (mem0 : word -> option byte) (md0 : Model)
  (P : Z) (regs : bvmap 5 word) (M : word -> option byte) (mdc : Model) : Prop :=
  vrd_iat regs regs0 W M o q (Z.of_nat d) text len P /\
  getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\ getr regs 18 = w64 (-1) /\ getr regs 20 = w64 v /\
  val_mem segs (mrestrict (w_H W) M) v 4 (if o then 6 else 5) /\
  (forall x : word, ~ pi_wr (spZ regs0) q v (bv_unsigned x) -> mrestrict (w_H W) M x = mrestrict (w_H W) mem0 x) /\
  mem_grows (mrestrict (w_H W) mem0) (mrestrict (w_H W) M) /\
  ajournal_x (SK := SK) segs B prh_pst ARx (STK_parse_items d + e) (spZ regs0 + e) (rd_fp q v)
    ly Sa Hp W mem0 md0 [] ly Sa Hp W M mdc 0.

(* ---- the segment's post: the loop head (with the non-empty fact the empty case refutes), or the call's post ---- *)
Definition vrd_iQall (d : nat) (o : bool)
  (ly : alayout) (Sa : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z))
  (Lam : list (Z * Z)) (peak cnt fail ran most own e q text len p : Z) (tb : list Z) (v : Z)
  : world segs -> config -> Prop :=
  fun W' c' =>
    (exists ch2 P, W' = ip_W P /\ c' = vrd_cfg A_IELEM_SLOT P /\
       vrd_ielem_a B ARx SK
         (vrd_ient_of d o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v ch2) P
       /\ (forall r, PjGrammar.skip (tl (rest_atR tb text p)) <> PjGrammar.closer o :: r))
    \/ vrd_ipost d o q v text len p e tb regs ly Sa Hp W mem md Lam peak cnt fail ran most own W' c'.

(* ---- the grow step (rows 90..107 and the refusal of row 92), as the exits use it. It crosses grow, whose text
   concludes SRr' segs RZ_cf, so it concludes SRr' (the re-hiding move) ---- *)
Definition vrd_iDstep (d : nat) (CTX : list (list Z)) (o : bool)
  (ly : alayout) (Sa : astate) (Hp : list Z) (W : world segs) (regs0 : bvmap 5 word)
  (mem0 : word -> option byte) (md0 : Model) (ch : list (Z * Z * Z))
  (Lam : list (Z * Z)) (peak cnt fail ran most own e q text len p : Z) (tb : list Z) (v : Z) : Prop :=
  forall P E ss ms mdc,
  st_ok segs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = pa_sigma AS_grow ->
  vrd_imid d o e q text len v regs0 ly Sa Hp W mem0 md0 P (regupd (ms_regs ms) 12%bv (w64 (text + len))) (ms_mem ms)
    mdc ->
  getr (ms_regs ms) 10 = w64 v -> getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (PI_GROWRET - A_prog_base)) ->
  p + 1 <= P <= text + len ->
  PjGrammar.skip (tl (rest_atR tb text p)) = rest_atR tb text P ->
  (forall r, PjGrammar.skip (tl (rest_atR tb text p)) <> PjGrammar.closer o :: r) ->
  SRr' segs YGcfRehidePost.RZ_cf W (mkCfg ms mdc)
    (vrd_iQall d o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v).

(* the grow step in the generic form (vrd_iDstep with P of the call memory and of the end memory), over a world
   relation R: the segment lemmas that end in it (vrd_iX0_invR .. vrd_ipro_go_invR) are generic in R, so that the
   empty container, which never reaches the grow, keeps its SRr statement (R := wle); the segment master takes them
   at R := wle' *)
Definition vrd_iDstep_PR (R : world segs -> world segs -> Prop) (Pm : (word -> option byte) -> Prop) (d : nat)
  (CTX : list (list Z)) (o : bool)
  (ly : alayout) (Sa : astate) (Hp : list Z) (W : world segs) (regs0 : bvmap 5 word)
  (mem0 : word -> option byte) (md0 : Model) (ch : list (Z * Z * Z))
  (Lam : list (Z * Z)) (peak cnt fail ran most own e q text len p : Z) (tb : list Z) (v : Z) : Prop :=
  forall P E ss ms mdc,
  st_ok segs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = pa_sigma AS_grow ->
  vrd_imid d o e q text len v regs0 ly Sa Hp W mem0 md0 P (regupd (ms_regs ms) 12%bv (w64 (text + len))) (ms_mem ms)
    mdc ->
  getr (ms_regs ms) 10 = w64 v -> getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (PI_GROWRET - A_prog_base)) ->
  p + 1 <= P <= text + len ->
  PjGrammar.skip (tl (rest_atR tb text p)) = rest_atR tb text P ->
  (forall r, PjGrammar.skip (tl (rest_atR tb text p)) <> PjGrammar.closer o :: r) ->
  Pm (ms_mem ms) ->
  SRrG segs R W (mkCfg ms mdc)
    (fun W' c' => vrd_iQall d o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v W' c' /\
       Pm (ms_mem (cfg_ms c'))).

Definition vrd_iDstep_P (Pm : (word -> option byte) -> Prop) (d : nat) (CTX : list (list Z)) (o : bool)
  (ly : alayout) (Sa : astate) (Hp : list Z) (W : world segs) (regs0 : bvmap 5 word)
  (mem0 : word -> option byte) (md0 : Model) (ch : list (Z * Z * Z))
  (Lam : list (Z * Z)) (peak cnt fail ran most own e q text len p : Z) (tb : list Z) (v : Z) : Prop :=
  vrd_iDstep_PR (wle' segs YGcfRehidePost.RZ_cf) Pm d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own
    e q text len p tb v.

Lemma vrd_iDstep_of_P : forall d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v,
  vrd_iDstep_P (fun _ => True) d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v ->
  vrd_iDstep d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v.
Proof.
intros d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v HD
  P E ss ms mdc HS Hrv Hpc HMID H10 H1 HP Hsk Hnc.
eapply (SRrG_mono segs (wle' segs YGcfRehidePost.RZ_cf)); [exact (HD P E ss ms mdc HS Hrv Hpc HMID H10 H1 HP Hsk Hnc I)|].
intros W' c' _ (H & _). exact H.
Qed.

Lemma vrd_iDstep_to_P : forall d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v,
  vrd_iDstep d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v ->
  vrd_iDstep_P (fun _ => True) d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v.
Proof.
intros d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v HD
  P E ss ms mdc HS Hrv Hpc HMID H10 H1 HP Hsk Hnc _.
eapply (SRrG_mono segs (wle' segs YGcfRehidePost.RZ_cf)); [exact (HD P E ss ms mdc HS Hrv Hpc HMID H10 H1 HP Hsk Hnc)|].
intros W' c' _ H. exact (conj H I).
Qed.

(* a2 is caller-saved and the closer test loads the byte into it: the grow step reads the re-entry facts at the
   register file with a2 restored to the end of the text, which no instruction after the call reads *)
Lemma vrd_getr_upd_other : forall regs (r r' : bv 5) v, bv_unsigned r' <> bv_unsigned r ->
  getr (regupd regs r v) r' = getr regs r'.
Proof.
intros regs r r' v H. unfold getr. destruct (bv_eqb r' 0); [reflexivity|]. apply regupd_other. intros ->. apply H.
reflexivity.
Qed.
Lemma vrd_getr_upd_12 : forall regs v, getr (regupd regs 12%bv v) 12%bv = v.
Proof.
intros regs v. unfold getr. replace (bv_eqb _ _) with false by (vm_compute; reflexivity). apply regupd_same.
Qed.

(* a register a run left as it found it *)
Lemma vrd_carry : forall E ss ms (H : word -> bool) sr regs (r : bv 5),
  st_ok segs E ss (restrict H ms) -> regs_ok E sr regs -> sr_get (ss_regs ss) r = sr_get sr r ->
  getr (ms_regs ms) r = getr regs r.
Proof.
intros E ss ms H sr regs r HS HR Heq.
rewrite (st_ok_restrict_reg segs H E ss ms r HS), Heq. symmetry. exact (HR r).
Qed.
(* a re-entry register at the grow call, read at the register file with a2 restored *)
Ltac vrd_gstep HS RK MS Hh rg H12 :=
  first
  [ rewrite vrd_getr_upd_12; symmetry; exact H12
  | rewrite vrd_getr_upd_other by (let Hc := fresh "Hc" in intros Hc; vm_compute in Hc; discriminate Hc);
    apply (vrd_carry _ _ MS Hh vrd_rX rg _ HS RK); vm_compute; reflexivity ].

(* bytes a run keeps keep every byte fact *)
Lemma vrd_rdkeep_w : forall (Hh : word -> bool) (M M' : word -> option byte) (X : Z -> Prop) (Pz : Z -> Prop),
  (forall x : word, ~ X (bv_unsigned x) -> mrestrict Hh M' x = mrestrict Hh M x) ->
  (forall a, Pz a -> 0 <= a < 2 ^ 64 /\ ~ X a) ->
  rd_keep segs (mrestrict Hh M) (mrestrict Hh M') Pz.
Proof.
intros Hh M M' X Pz HK HP. apply vrd_rdkeep. intros a Ha. destruct (HP a Ha) as [Hr Hn].
apply HK. rewrite unsigned_lit_small by lia. exact Hn.
Qed.

(* the re-entry facts move along a stretch that writes only the cursor's p word and depth word *)
Lemma vrd_imid_step : forall d o e q text len v regs0 ly Sa Hp W mem0 md0 P regs M mdc P' regs' M' mdc',
  vrd_imid d o e q text len v regs0 ly Sa Hp W mem0 md0 P regs M mdc ->
  (q + 24 <= v \/ v + 56 <= q) -> 4096 <= v /\ v + 56 <= 2 ^ 47 ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 11 = getr regs 11 ->
  getr regs' 12 = getr regs 12 -> getr regs' 18 = getr regs 18 -> getr regs' 19 = getr regs 19 ->
  getr regs' 20 = getr regs 20 -> getr regs' 21 = getr regs 21 -> getr regs' 22 = getr regs 22 ->
  getr regs' 23 = getr regs 23 -> getr regs' 26 = getr regs 26 -> getr regs' 27 = getr regs 27 ->
  (forall x : word, ~ (q <= bv_unsigned x < q + 8 \/ q + 16 <= bv_unsigned x < q + 20) ->
     mrestrict (w_H W) M' x = mrestrict (w_H W) M x) ->
  mem_grows (mrestrict (w_H W) M) (mrestrict (w_H W) M') ->
  val_mem segs (mrestrict (w_H W) M') q 8 P' ->
  val_mem segs (mrestrict (w_H W) M') (q + 16) 4 (Z.of_nat d + 1) ->
  4096 <= P' <= 2 ^ 47 - 2 -> P' + 1 <= spZ regs0 - 144 ->
  ajournal_x (SK := SK) segs B prh_pst ARx (STK_parse_items d + e) (spZ regs0 + e) (rd_fp q v)
    ly Sa Hp W mem0 md0 [] ly Sa Hp W M' mdc' 0 ->
  vrd_imid d o e q text len v regs0 ly Sa Hp W mem0 md0 P' regs' M' mdc'.
Proof.
intros d o e q text len v regs0 ly Sa Hp W mem0 md0 P regs M mdc P' regs' M' mdc'
  ((Hsp & Hs1 & Hs2 & Hs16 & H8 & H26 & Hq1 & Hq2 & Hq3 & Hq8 & H9 & H21 & H22 & H23 & H27 & H11 & Hd & H19 & H12 &
    He & HP1 & HP2 & HSV & Vp & Ve & Vd & RWq & HRAq) & Hgp & Htp & H18 & H20 & Vty & KM & KG & HJ)
  Hqv Hvr g2 g3 g4 g8 g9 g11 g12 g18 g19 g20 g21 g22 g23 g26 g27 KQ KG' Vp' Vd' HP1' HP2' HJ'.
assert (KF : forall Pz : Z -> Prop, (forall a, Pz a -> 0 <= a < 2 ^ 64 /\ ~ (q <= a < q + 8 \/ q + 16 <= a < q + 20)) ->
  rd_keep segs (mrestrict (w_H W) M) (mrestrict (w_H W) M') Pz)
  by (intros Pz HPz; exact (vrd_rdkeep_w (w_H W) M M' _ Pz KQ HPz)).
split; [|split; [rewrite g3; exact Hgp|split; [rewrite g4; exact Htp|split; [rewrite g18; exact H18|
  split; [rewrite g20; exact H20|]]]]].
- split; [unfold spZ; rewrite g2; exact Hsp|]. do 3 (split; [assumption|]).
  split; [rewrite g8; exact H8|]. split; [rewrite g26; exact H26|]. do 4 (split; [assumption|]).
  split; [rewrite g9; exact H9|]. split; [rewrite g21; exact H21|]. split; [rewrite g22; exact H22|].
  split; [rewrite g23; exact H23|]. split; [rewrite g27; exact H27|]. split; [rewrite g11; exact H11|].
  split; [exact Hd|]. split; [rewrite g19; exact H19|]. split; [rewrite g12; exact H12|].
  split; [exact He|]. split; [exact HP1'|]. split; [exact HP2'|].
  split.
  { intros j Hj. apply (val_mem_keep segs _ _ _ _ _ (HSV j Hj)). apply KF. intros a Ha. lia. }
  split; [exact Vp'|].
  split; [apply (val_mem_keep segs _ _ _ _ _ Ve); apply KF; intros a Ha; cbn in Ha; lia|].
  split; [exact Vd'|].
  split; [intros x Hx; apply (writable_at_grows segs _ _ x KG'); exact (RWq x Hx)|].
  eapply range_addressable_agree; [|exact HRAq]. intros x Hx.
  unfold aview, mbyte. rewrite KQ; [reflexivity|].
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). unfold shadow_of_addr.
  assert (Hsx : 0 <= x / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  rewrite unsigned_lit_small; unfold SHADOW_OFF in *; lia.
- split; [apply (val_mem_keep segs _ _ _ _ _ Vty); apply KF; intros a Ha; cbn in Ha; lia|].
  split.
  { intros x Hx. rewrite KQ; [exact (KM x Hx)|]. intros Hq. apply Hx. unfold pi_wr. right. lia. }
  split; [exact (mem_grows_trans _ _ _ KG KG')|].
  exact HJ'.
Qed.

(* vrd_chunk_val for a plain st_ok (the state a run leaves at a call) *)
Lemma vrd_chunk_val_st : forall E ss ms (H : word -> bool) r0 i o (w : N) sv vl,
  st_ok segs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r0 ->
  In (YP09.mkChunk o (CVal w sv)) (YP09.r_chunks r0) ->
  sv_denot E sv = Z_to_bv 64 vl -> 0 <= vl < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
  val_mem segs (mrestrict H (ms_mem ms)) (base_val E (YP09.r_base r0) + o) (N.to_nat w) vl.
Proof.
intros E ss ms H r0 i o w sv vl HS Hi Hin Hv Hr Hw.
pose proof (st_ok_chunk segs E ss (restrict H ms) i r0 _ HS Hi Hin) as Hc.
exact (val_of_chunk_ok segs E _ _ o w sv vl Hc Hv Hr Hw).
Qed.
Ltac vrd_chunk_st HS E MS H i o w sv vl VQ :=
  pose proof (vrd_chunk_val_st E _ MS H _ i o w sv vl HS eq_refl) as VQ;
  lazymatch type of VQ with ?A -> _ =>
    let HA := fresh "HA" in assert (HA : A) by (cbn; tauto); specialize (VQ HA); clear HA end.
(* the same two, with the environment read off HS (a `_` would be elaborated before HS is seen) *)
Ltac vrd_chunkH HS MS H i o w sv vl VQ :=
  lazymatch type of HS with st_ok_pi _ _ ?E0 _ _ => vrd_chunk HS E0 MS H i o w sv vl VQ end.
Ltac vrd_chunk_stH HS MS H i o w sv vl VQ :=
  lazymatch type of HS with st_ok _ ?E0 _ _ => vrd_chunk_st HS E0 MS H i o w sv vl VQ end.

(* the ledger and block moves of a call that allocated nothing (the text's rd_ledger_move at most and the whole
   call's granted trace: with no call the refusal peak is over no index, 0) *)
Lemma vrd_imove_nil : forall d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v,
  vrd_ipre d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v ->
  rd_ledger_move Lam peak cnt fail ran most [] (prhPi_gtrace d o (rest_atR tb text p)) [] [] Lam peak cnt fail ran /\
  rd_blocks_move B ly Sa ly Sa [] [] (rest_atR tb text p) d /\
  blocks_bytes Sa <= blocks_bytes Sa + prh_held [] /\ Ledger.lsum [] = PjGrammar.held [].
Proof.
intros d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v HPRE.
pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRD & _).
pose proof HRD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLED & _).
pose proof (vrd_led_bounds _ _ _ _ _ _ _ _ _ _ _ _ HLED) as (Hlive & Hpk & Hcnt64 & Hfl64 & Hran).
split; [|split; [|split; [unfold prh_held; cbn [PjGrammar.held PjGrammar.calls Z.of_nat]; lia | reflexivity]]].
- unfold rd_ledger_move. cbn [PjGrammar.calls lszR fold_left hpeakR nliveR length map app Z.of_nat].
  split; [split; [intros i Hi; lia | split; [left; reflexivity | intros i Hi; lia]]|].
  split; [rewrite Z.add_0_r, Z.mod_small by lia; reflexivity|].
  split; [split; intros H; [lia | reflexivity]|].
  split; [apply Permutation_refl|]. split; [apply Permutation_refl|]. split; [reflexivity|].
  unfold prh_refused_peak. cbn [List.seq map fold_right]. lia.
- split; [intros a k Hin; destruct Hin|]. split; [apply Permutation_refl|]. split; [apply Permutation_refl|].
  cbn [hpeakR]. lia.
Qed.

(* THE OUTCOME of an arm that makes no allocator call and whose ALL-GRANTED run makes none either (the depth
   refusal, the empty container): the granted trace is [], so the run hypothesis says nothing, g_ran_out is kept,
   the instance's (res, []) IS the granted run's, and the position stays *)
Lemma vrd_outcome_nil : forall d o x res (S : astate) (ran cnt fail : Z),
  fst (PjGrammar.jr_items prh_jr_strtod d o x []) = (res, []) ->
  forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
    (H0 : list Z) (hist : list YG00.chunk),
  PresetRoomPos.iface_room_pos sm x0 os i H0 hist S ->
  PRH_Base.prh_run_at sm x0 os i (PresetReqAt.rd_hevs (prhPi_gtrace d o x)) ->
  PRH_Base.prh_cons_from sm x0 os i (length (PresetReqAt.rd_hevs (prhPi_gtrace d o x))) ->
  (fail < cnt \/ cnt + Z.of_nat (PjGrammar.calls (prhPi_gtrace d o x)) <= fail) ->
  ran = ran /\ fst (PjGrammar.jr_items ReaderRes.jr_strtod d o x []) = (res, []) /\
  exists hist', PresetRoomPos.iface_room_pos sm x0 os (i + length (PresetReqAt.rd_hevs (prhPi_gtrace d o x)))%nat
    H0 hist' S.
Proof.
intros d o x res S ran cnt fail Hf sm x0 os i H0 hist HP _ _ _.
assert (Hg : prhPi_gtrace d o x = []) by (unfold prhPi_gtrace; rewrite Hf; reflexivity).
split; [reflexivity|]. split; [rewrite vrd_strtod_same; exact Hf|].
exists hist. rewrite Hg. replace (i + length (PresetReqAt.rd_hevs []))%nat with i by (cbn; lia). exact HP.
Qed.

(* ============================================================================================================== *)
(* A. THE DEPTH REFUSAL (d = MAXD): rows 1..39, the taken branch of row 39, rows 310..325 and the `ret`.          *)
(* ============================================================================================================== *)
Lemma vrd_ipro_depth_inv : forall (Pm : (word -> option byte) -> Prop), srr_inv_laws segs Pm ->
  forall d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v,
  vrd_ipre d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v ->
  d = PjGrammar.MAXD -> Pm mem ->
  SRr segs W (cfg_at segs (pa_sigma AS_parse_items) regs mem md)
    (fun W' c' => vrd_ipost d o q v text len p e tb regs ly Sa Hp W mem md Lam peak cnt fail ran most own W' c' /\
       Pm (ms_mem (cfg_ms c'))).
Proof.
intros Pm PLAW d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v HPRE Hd HPM.
pose proof (vrd_iawr d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v HPRE) as HAWR.
destruct (vrd_ientry d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v HPRE)
  as [HS SHOK].
pose proof HPRE as ((HPRE0 & HROD & _) & HMN & HCTX & HUC & HCE & HCHI & HQCH & H10 & H11 & H12 & HRD & Hpe & Hop & HROOM & HPKS & HPKL & HFU
  & HFR & HCWR).
pose proof HRD as (Hfrm & Hmu & Hu1 & Hu2 & HIN & HWIN & Hspq & Hqe & HRAq & HSRC & HHOME & HMAX & HNODE & Hqv &
  Htv & Hvw & HLED & HdM & Hcnt).
pose proof HIN as (Vp & Ve & Vd & RWq & Hq8 & Ht0 & Ht62 & Htp & Hlen & Hgt & Hqt & Hd32).
pose proof HNODE as (Hv4096 & Hv8 & (Hvmod & RWv) & HZv & HATv & HAMv & HNv & HRAv).
pose proof HPRE0 as (HAR & Hra & Hra4 & Hgp & Htp' & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof HWIN as (He0 & He16 & Hetop & Hepres).
pose proof (vrd_stk_ge d) as HSTK.
pose proof H_img as (Himg1 & Himg2 & Himg3).
pose proof (vrd_led_bounds _ _ _ _ _ _ _ _ _ _ _ _ HLED) as (Hlive & Hpk & Hcnt64 & Hfl64 & Hran).
unfold amem_range in HAMv.
pose proof HSRC as (Hbt & Ht4096 & Htceil & Htamr & HRAt & Hhull).
rewrite Hlen in Htceil, Htamr.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Rsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
assert (Rq : 4096 <= q /\ q + 24 <= 2 ^ 47) by lia.
assert (Rv : 4096 <= v /\ v + 56 <= 2 ^ 47) by (unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
assert (Rp : 4096 <= p /\ p <= 2 ^ 47) by lia.
pose proof (vrd_jinit (STK_parse_items d) e (rd_fp q v) ly Sa Hp W regs mem md ch HPRE0 HWIN) as HJ.
assert (U10 : bv_unsigned (getr regs 10) = q) by (rewrite H10; apply unsigned_lit_small; lia).
assert (U11 : bv_unsigned (getr regs 11) = v) by (rewrite H11; apply unsigned_lit_small; lia).
set (E := vrd_iE regs p (text + len) (Z.of_nat d)) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold vrd_iE; apply Eimg_env).
assert (E12 : ew E 12 = w64 (if o then 1 else 0))
  by (subst E; rewrite (vrd_iE_reg regs _ _ _ 12%bv 12%nat eq_refl); exact H12).
assert (E33 : ew E 33 = w64 p)
  by (subst E; unfold vrd_iE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = w64 (text + len))
  by (subst E; unfold vrd_iE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = w64 (Z.of_nat d))
  by (subst E; unfold vrd_iE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (U10E : bv_unsigned (ew E 10) = q)
  by (subst E; rewrite (vrd_iE_reg regs _ _ _ 10%bv 10%nat eq_refl); exact U10).
assert (U11E : bv_unsigned (ew E 11) = v)
  by (subst E; rewrite (vrd_iE_reg regs _ _ _ 11%bv 11%nat eq_refl); exact U11).
assert (HD32 : Z.of_nat d = 32) by (rewrite Hd; reflexivity).
pose (RUNF := paj_run_xf_inv (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B prh_pst ARx LAWS Pm PLAW).
pose (BR := paj_branch (PI := PI_prog_A)).
pose (RET := paj_ret_at (PL := PL_prog_A) (PI := PI_prog_A)).
unfold cfg_at. change (w64 (pa_sigma AS_parse_items)) with (Z_to_bv 64 (BASE + (PI_ENTRY - A_prog_base))).
(* ---- rows 1..39 ---- *)
paj_run_tok_x_inv RUNF HS HJ SHOK HPM pi_Bspan; [exact HAWR|].
rename HFr into HFr1, HG into HG1. clear HF.
lazymatch type of HFr1 with frame_of _ _ _ (mrestrict _ (ms_mem ?m)) => set (MS1 := m) in * end.
psrr_branch_tok RUNF BR HS SHOK pi_Bspan.
2:{ exfalso. cbn [sv_denot] in Hc. rewrite E35, HD32 in Hc. vm_compute in Hc. discriminate Hc. }
(* ---- the taken branch: rows 310..325 ---- *)
paj_run_tok_x_inv RUNF HS HJ SHOK HPM pi_Bspan;
  [apply (vrd_iawr_sk d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v _ HPRE);
   vm_compute; reflexivity|].
rename HFr into HFr2, HG into HG2. clear HF.
lazymatch type of HFr2 with frame_of _ _ _ (mrestrict _ (ms_mem ?m)) => set (MS2 := m) in * end.
(* what the two runs kept, and what they left writable *)
pose proof (vrd_ikeep regs p (text + len) (Z.of_nat d) q v _ _ _ U10 U11 HFr2) as K2.
lazymatch type of K2 with ?A -> _ => assert (SK2 : A) by (vm_compute; reflexivity) end.
specialize (K2 SK2). clear SK2.
pose proof (vrd_ikeep regs p (text + len) (Z.of_nat d) q v _ _ _ U10 U11 HFr1 eq_refl) as K1.
assert (KM : forall x : word, ~ pi_wr (spZ regs) q v (bv_unsigned x) ->
  mrestrict (w_H W) (ms_mem MS2) x = mrestrict (w_H W) mem x)
  by (intros x Hx; rewrite (K2 x Hx); exact (K1 x Hx)).
assert (KZ : forall a, 0 <= a < 2 ^ 64 -> ~ pi_wr (spZ regs) q v a ->
  mrestrict (w_H W) (ms_mem MS2) (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a))
  by (intros a Ha Hn; apply KM; rewrite unsigned_lit_small by lia; exact Hn).
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ pi_wr (spZ regs) q v a ->
  aview segs (w_H W) (ms_mem MS2) a = aview segs (w_H W) mem a)
  by (intros a Ha Hn; unfold aview, mbyte; rewrite (KZ a Ha Hn); reflexivity).
assert (KG : mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem MS2)))
  by exact (mem_grows_trans _ _ _ HG1 HG2).
assert (KW : forall a, writable_at segs (mrestrict (w_H W) mem) a ->
  writable_at segs (mrestrict (w_H W) (ms_mem MS2)) a)
  by (intros a; apply writable_at_grows; exact KG).
(* the bytes off pi_wr the post reads: the node past its type word, the statics, the harness heads *)
assert (Hvimg : forall a, v <= a < v + 56 -> ~ in_img segs a).
{ intros a Ha.
  exact (proj1 (vrd_v_place ly Sa Hp W mem md Lam peak cnt fail ran most own regs e v HAR HLED HATv ltac:(lia) a Ha)). }
assert (Hvhd : forall a0 k a, In (a0, k) Lam -> v <= a < v + 56 -> ~ (a0 - cf_head <= a < a0)).
{ intros a0 k a Hin Ha.
  exact (proj2 (vrd_v_place ly Sa Hp W mem md Lam peak cnt fail ran most own regs e v HAR HLED HATv ltac:(lia) a Ha) a0 k Hin). }
assert (Hvfr : forall a, v <= a < v + 56 -> ~ (spZ regs - PI_FRAME <= a < spZ regs)).
{ intros a Ha Hf. apply (proj2 (HNv a Ha)). unfold PI_FRAME in *. lia. }
assert (KN : rd_keep segs (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem MS2)) (fun x => v + 4 <= x < v + 56)).
{ apply vrd_rdkeep. intros a Ha. apply KZ; [lia|].
  unfold pi_wr. intros [H|[H|[H|H]]]; [exact (Hvfr a ltac:(lia) H) | lia | lia | lia]. }
(* ---- the return ---- *)
prreg HS (Z_to_bv 5 1) R1. prreg HS (Z_to_bv 5 10) R10.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat2. cbv beta. split; [|exact HPM]. unfold vrd_ipost.
(* the prologue stores no cursor trace: the empty budget, within every CW (the kit's cut's fpostWFbm) *)
apply vrd_fpostWFb_of; [exact (vrd_wbudget_nil CW)|]. unfold fpostWF.
lazymatch goal with |- exists _ _ _ _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?dd = _ /\ _ =>
  exists fx, ly, Sa, Hp, r, m, dd, 0 end.
split.
{ assert (EQ1 : getr (ms_regs MS2) 1 = getr regs 1).
  { transitivity (getr (ms_regs MS2) (Z_to_bv 5 1)); [reflexivity|]. rewrite R1.
    subst E. exact (vrd_iE_reg regs _ _ _ 1%bv 1%nat eq_refl). }
  unfold YK0s.ret_ok in Hra. rewrite EQ1, Hra. reflexivity. }
split; [exact Hfrm|]. split; [intros r _; reflexivity|].
split; [apply (ajournal_x_materialize (SK := SK) segs B prh_pst ARx LAWS (@pa_segs_low _ _ PI_prog_A)); exact HJ|].
split.
{ intros a Ha Hn. apply KA; [lia|]. unfold pi_wr, PI_FRAME. intros [H|[H|[H|H]]]; [lia| |  |];
  apply Hn; unfold rd_fp, inFP.
  - exists (q, q + 8). split; [left; reflexivity | cbn [fst snd]; lia].
  - exists (q + 16, q + 20). split; [right; left; reflexivity | cbn [fst snd]; lia].
  - exists (v, v + 56). split; [right; right; left; reflexivity | cbn [fst snd]; lia]. }
split.
{ eapply (aregs_preserved_of_st_ok segs _ _ _ _ regs [w64 PI_SB; w64 p; w64 (text + len); w64 (Z.of_nat d)] HS).
  - split; [intros n Hn; subst E; unfold vrd_iE; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
  - vm_compute. reflexivity. }
(* the node: its type word set, the rest zero - a refused tree with no blocks, its order list empty *)
assert (HHDR : pj_hdrR segs (mrestrict (w_H W) (ms_mem MS2)) v (if o then 6 else 5) 0 0 0 0 0 0).
{ split; [split; [exact Hvmod | intros x Hx; apply KW; exact (RWv x Hx)]|].
  split.
  { split; [destruct o; lia|].
    vrd_chunk HS E MS2 (w_H W) 6%nat 0 4%N (SAlu ALU_ADD (SAlu ALU_SLTU (SLit 0) (SOff 12 0)) (SLit 5))
      (if o then 6 else 5) VT.
    specialize (VT ltac:(cbn [sv_denot]; rewrite E12; destruct o; vm_compute; reflexivity)
      ltac:(cbn; destruct o; lia) ltac:(lia)).
    cbn [base_val YP09.r_base] in VT. rewrite U11E, Z.add_0_r in VT. exact VT. }
  repeat split; try lia;
  lazymatch goal with |- val_mem _ _ (v + ?k) 8 0 =>
    apply (vrd_zero_kept (mrestrict (w_H W) mem) _ v (v + k) 8 HZv); [|lia|lia];
    eapply rd_keep_mono; [exact KN|]; intros z Hz; cbn in Hz; lia end. }
try unfold vrd_ipost_body, vrd_items_q, tpiP_Q.
exists [], None, [], [], [], Lam, peak, cnt, fail, ran.
split; [rewrite vrd_strtod_same, Hd; apply vrd_items_refuse|].
split.
{ apply (prh_ledger_kept_aview (L := A_prog_listing) (PA := PI_prog_A) B ly Sa Hp W mem ly Sa Hp W (ms_mem MS2)
    Lam peak cnt fail ran most own HLED); [ | | intros a0 k _ Hab; exact Hab | apply Permutation_refl].
  - intros a Ha. pose proof (H_pst_img a Ha) as Hi. pose proof (@pa_segs_low _ _ PI_prog_A a Hi) as Hlow.
    apply KA; [unfold kLowMemEnd in Hlow; lia|].
    unfold pi_wr, PI_FRAME. intros [H|[H|[H|H]]]; [unfold kLowMemEnd in Hlow; lia | unfold kLowMemEnd in Hlow; lia
      | unfold kLowMemEnd in Hlow; lia | exact (Hvimg a ltac:(lia) Hi)].
  - intros a0 k i Hin Hi.
    destruct (vrd_led_hblk ly Sa Hp W mem Lam peak cnt fail ran _ _ a0 k HLED Hin) as (Hk0 & Hab & _).
    destruct (alx_blocks segs B ARx LAWS ly Sa Hp W mem md _ _ HAR Hab) as (_ & Hb4096 & Hbc & _).
    assert (Hrq : k + cf_head <= req_size (k + cf_head))
      by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
    apply KA; [lia|].
    unfold pi_wr, PI_FRAME in *. intros [H|[H|[H|H]]]; [lia | lia | lia |].
    assert (Hx : v <= a0 - cf_head + i < v + 56) by lia.
    assert (Hy : a0 - cf_head <= a0 - cf_head + i < a0) by lia.
    exact (Hvhd a0 k (a0 - cf_head + i) Hin Hx Hy). }
split; [exact (proj1 HROOM)|].
(* the hull: no allocator call, the state kept *)
split; [exact (PresetHullBudget.hull_used_refl Sa _)|].
split; [exact (vrd_live_nil Sa)|].
split; [exact (vrd_xfer_nil Sa)|].
split; [exact (vrd_outcome_nil d o (rest_atR tb text p) None Sa ran cnt fail
                 ltac:(rewrite Hd, vrd_items_refuse; reflexivity))|].
(* the outcome of an injected reading: no call, so no refusal *)
split; [intros sm x0 os i H0 hist _ _ _ _; exact (vrd_granted_rep 0 cnt fail _)|].
split; [exact (proj1 (vrd_imove_nil d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v
                 HPRE))|].
split.
{ split; [intros a k Hin; destruct Hin|]. split; [apply Permutation_refl|]. split; [apply Permutation_refl|].
  cbn [hpeakR]. lia. }
split; [unfold prh_held; cbn [PjGrammar.held PjGrammar.calls Z.of_nat]; lia|].
split; [reflexivity|].
split.
{ transitivity (getr (ms_regs MS2) (Z_to_bv 5 10)); [reflexivity|]. rewrite R10.
  apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity. }
(* The kit's cut: the refused tree's order list (FREEORD-NONE) - empty, as the model's (jf_cont's depth arm) *)
split; [intros _ n _; exists []; split; [exact (vrd_hdr_fo _ _ v (if o then 6 else 5) n HHDR)
                                       | rewrite Hd, vrd_frees_refuse; reflexivity]|].
split.
- exists p, (Z.of_nat d + 1). split; [lia|]. split; [lia|].
  split.
  { vrd_chunk HS E MS2 (w_H W) 3%nat 0 8%N (SOff 33 0) p VQ.
    specialize (VQ ltac:(cbn [sv_denot]; rewrite E33, Z.add_0_r, unsigned_lit_small by lia; reflexivity)
      ltac:(lia) ltac:(lia)).
    cbn [base_val YP09.r_base] in VQ. rewrite U10E, Z.add_0_r in VQ. exact VQ. }
  split.
  { vrd_chunk HS E MS2 (w_H W) 4%nat 8 8%N (SOff 34 0) (text + len) VQ.
    specialize (VQ ltac:(cbn [sv_denot]; rewrite E34, Z.add_0_r, unsigned_lit_small by lia; reflexivity)
      ltac:(lia) ltac:(lia)).
    cbn [base_val YP09.r_base] in VQ. rewrite U10E in VQ. exact VQ. }
  split.
  { vrd_chunk HS E MS2 (w_H W) 5%nat 16 4%N (SOff 35 1) (Z.of_nat d + 1) VQ.
    specialize (VQ ltac:(cbn [sv_denot]; rewrite E35, unsigned_lit_small by lia; reflexivity)
      ltac:(cbn; lia) ltac:(lia)).
    cbn [base_val YP09.r_base] in VQ. rewrite U10E in VQ. exact VQ. }
  intros x Hx. apply KW. exact (RWq x Hx).
- rewrite Hd, Nat.sub_diag. exact (vrd_hdr_fd _ _ v (if o then 6 else 5) _ HHDR).
Qed.

Lemma vrd_ipro_depth : forall d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v,
  vrd_ipre d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v ->
  d = PjGrammar.MAXD ->
  SRr segs W (cfg_at segs (pa_sigma AS_parse_items) regs mem md)
    (vrd_ipost d o q v text len p e tb regs ly Sa Hp W mem md Lam peak cnt fail ran most own).
Proof.
intros d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v HPRE Hd.
eapply SRr_mono; [exact (vrd_ipro_depth_inv (fun _ => True) vrd_inv_true d CTX o ly Sa Hp W regs mem md ch Lam peak cnt
  fail ran most own e q text len p tb v HPRE Hd I)|].
intros W' c' _ (H & _). exact H.
Qed.

(* ============================================================================================================== *)
(* THE POST PIECES every returning arm without an allocation shares.                                            *)
(* ============================================================================================================== *)
(* the ledger survives a stretch that keeps every byte off pi_wr *)
Lemma vrd_iledger : forall d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v M,
  vrd_ipre d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v ->
  (forall x : word, ~ pi_wr (spZ regs0) q v (bv_unsigned x) -> mrestrict (w_H W) M x = mrestrict (w_H W) mem0 x) ->
  prh_ledger B ly Sa Hp W M Lam peak cnt fail ran most own.
Proof.
intros d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v M HPRE KM.
pose proof HPRE as ((HPRE0 & HROD & _) & HMN & HCTX & HUC & HCE & HCHI & HQCH & H10 & H11 & H12 & HRD & Hpe & Hop & HROOM & HPKS & HPKL &
  HFU & HFR & HCWR).
pose proof HRD as (Hfrm & Hmu & Hu1 & Hu2 & HIN & HWIN & Hspq & Hqe & HRAq & HSRC & HHOME & HMAX & HNODE & Hqv &
  Htv & Hvw & HLED & HdM & Hcnt).
pose proof HNODE as (Hv4096 & Hv8 & _ & _ & HATv & HAMv & HNv & _).
pose proof HPRE0 as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof HWIN as (He0 & He16 & Hetop & Hepres).
pose proof (vrd_stk_ge d) as HSTK. pose proof H_img as (Himg1 & Himg2 & Himg3).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAMv.
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ pi_wr (spZ regs0) q v a ->
  aview segs (w_H W) M a = aview segs (w_H W) mem0 a)
  by (intros a Ha Hn; unfold aview, mbyte; rewrite KM; [reflexivity | rewrite unsigned_lit_small by lia; exact Hn]).
assert (Hvimg : forall a, v <= a < v + 56 -> ~ in_img segs a).
{ intros a Ha.
  exact (proj1 (vrd_v_place ly Sa Hp W mem0 md0 Lam peak cnt fail ran most own regs0 e v HAR HLED HATv ltac:(lia) a Ha)). }
assert (Hvhd : forall a0 k a, In (a0, k) Lam -> v <= a < v + 56 -> ~ (a0 - cf_head <= a < a0)).
{ intros a0 k a Hin Ha.
  exact (proj2 (vrd_v_place ly Sa Hp W mem0 md0 Lam peak cnt fail ran most own regs0 e v HAR HLED HATv ltac:(lia) a Ha) a0 k Hin). }
apply (prh_ledger_kept_aview (L := A_prog_listing) (PA := PI_prog_A) B ly Sa Hp W mem0 ly Sa Hp W M
  Lam peak cnt fail ran most own HLED); [ | | intros a0 k _ Hab; exact Hab | apply Permutation_refl].
- intros a Ha. pose proof (H_pst_img a Ha) as Hi. pose proof (@pa_segs_low _ _ PI_prog_A a Hi) as Hlow.
  apply KA; [unfold kLowMemEnd in Hlow; lia|].
  unfold pi_wr, PI_FRAME. intros [H|[H|[H|H]]]; [unfold kLowMemEnd in Hlow; lia | unfold kLowMemEnd in Hlow; lia
    | unfold kLowMemEnd in Hlow; lia | exact (Hvimg a ltac:(lia) Hi)].
- intros a0 k i Hin Hi.
  destruct (vrd_led_hblk ly Sa Hp W mem0 Lam peak cnt fail ran _ _ a0 k HLED Hin) as (Hk0 & Hab & _).
  destruct (alx_blocks segs B ARx LAWS ly Sa Hp W mem0 md0 _ _ HAR Hab) as (_ & Hb4096 & Hbc & _).
  assert (Hrq : k + cf_head <= req_size (k + cf_head))
    by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
  apply KA; [lia|].
  unfold pi_wr, PI_FRAME in *. intros [H|[H|[H|H]]]; [lia | lia | lia |].
  assert (Hx : v <= a0 - cf_head + i < v + 56) by lia.
  assert (Hy : a0 - cf_head <= a0 - cf_head + i < a0) by lia.
  exact (Hvhd a0 k (a0 - cf_head + i) Hin Hx Hy).
Qed.

(* a node with its type word written over the zeroed node *)
Lemma vrd_hdr_typed : forall (m0 m : word -> option byte) v ty,
  pj_zeroR segs m0 v -> rd_keep segs m0 m (fun x => v + 4 <= x < v + 56) -> pj_rwR segs m v ->
  0 <= ty < 2 ^ 32 -> val_mem segs m v 4 ty -> pj_hdrR segs m v ty 0 0 0 0 0 0.
Proof.
intros m0 m v ty HZ KN Hrw Hty Vty.
split; [exact Hrw|]. split; [split; [exact Hty | exact Vty]|].
repeat split; try lia;
lazymatch goal with |- val_mem _ _ (v + ?k) 8 0 =>
  apply (vrd_zero_kept m0 m v (v + k) 8 HZ); [|lia|lia];
  eapply rd_keep_mono; [exact KN|]; intros z Hz; cbv beta in Hz |- *; cbn [Z.of_nat Pos.of_succ_nat] in Hz; lia end.
Qed.

(* ============================================================================================================== *)
(* C. THE EMPTY CONTAINER: from row 310 after rows 294..304 (the closer consumed, the depth word lowered back to
   d, s2 = 0) to the record post with res = Some (mk o [], r0), tr = D = [].                                      *)
(* ============================================================================================================== *)
Lemma vrd_iempty_ret_inv : forall (Pm : (word -> option byte) -> Prop), srr_inv_laws segs Pm ->
  forall d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v
    P r0 regs M mdc,
  vrd_ipre d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v ->
  (d < PjGrammar.MAXD)%nat ->
  PjGrammar.skip (tl (rest_atR tb text p)) = PjGrammar.closer o :: r0 ->
  rest_atR tb text (P + 1) = r0 -> p + 1 <= P < text + len ->
  spZ regs = spZ regs0 - 144 -> vi_saved W M regs0 ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 18 = w64 0 ->
  val_mem segs (mrestrict (w_H W) M) q 8 (P + 1) ->
  val_mem segs (mrestrict (w_H W) M) (q + 16) 4 (Z.of_nat d) ->
  val_mem segs (mrestrict (w_H W) M) v 4 (if o then 6 else 5) ->
  (forall x : word, ~ pi_wr (spZ regs0) q v (bv_unsigned x) -> mrestrict (w_H W) M x = mrestrict (w_H W) mem0 x) ->
  mem_grows (mrestrict (w_H W) mem0) (mrestrict (w_H W) M) ->
  ajournal_x (SK := SK) segs B prh_pst ARx (STK_parse_items d + e) (spZ regs0 + e) (rd_fp q v)
    ly Sa Hp W mem0 md0 [] ly Sa Hp W M mdc 0 ->
  Pm M ->
  SRr segs W (mkCfg (YK11.mkst regs (w64 (A_IPC A_IEPI_SLOT)) M (YK11.seg_rom segs)) mdc)
    (fun W' c' => vrd_ipost d o q v text len p e tb regs0 ly Sa Hp W mem0 md0 Lam peak cnt fail ran most own W' c' /\
       Pm (ms_mem (cfg_ms c'))).
Proof.
intros Pm PLAW d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v P r0 regs M mdc
  HPRE Hd Hsk Hr0 HP Hsp HSV Hgp Htp Hs2 Vp Vd Vty KM KG HJ HPM.
pose proof HPRE as ((HPRE0 & HROD & _) & HMN & HCTX & HUC & HCE & HCHI & HQCH & H10 & H11 & H12 & HRD & Hpe & Hop & HROOM & HPKS & HPKL &
  HFU & HFR & HCWR).
pose proof HRD as (Hfrm & Hmu & Hu1 & Hu2 & HIN & HWIN & Hspq & Hqe & HRAq & HSRC & HHOME & HMAX & HNODE & Hqv &
  Htv & Hvw & HLED & HdM & Hcnt).
pose proof HIN as (Vp0 & Ve0 & Vd0 & RWq0 & Hq8 & Ht0 & Ht62 & Htp0 & Hlen & Hgt & Hqt & Hd32).
pose proof HNODE as (Hv4096 & Hv8 & (Hvmod & RWv) & HZv & HATv & HAMv & HNv & HRAv).
pose proof HSRC as (Hbt & Ht4096 & Htceil & Htamr & HRAt & Hhull).
pose proof HPRE0 as (HAR & Hra & Hra4 & Hgp0 & Htp' & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof HWIN as (He0 & He16 & Hetop & Hepres).
pose proof (vrd_stk_ge d) as HSTK. pose proof H_img as (Himg1 & Himg2 & Himg3).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAMv.
rewrite Hlen in Htceil, Htamr.
assert (Hvfr : forall a, v <= a < v + 56 -> ~ (spZ regs0 - PI_FRAME <= a < spZ regs0)).
{ intros a Ha Hf. apply (proj2 (HNv a Ha)). unfold PI_FRAME in *. lia. }
assert (KF : forall Pz : Z -> Prop, (forall a, Pz a -> 0 <= a < 2 ^ 64 /\ ~ pi_wr (spZ regs0) q v a) ->
  rd_keep segs (mrestrict (w_H W) mem0) (mrestrict (w_H W) M) Pz)
  by (intros Pz HPz; exact (vrd_rdkeep_w (w_H W) mem0 M _ Pz KM HPz)).
assert (KW : forall a, writable_at segs (mrestrict (w_H W) mem0) a -> writable_at segs (mrestrict (w_H W) M) a)
  by (intros a; apply writable_at_grows; exact KG).
assert (Hlr : Z.of_nat (length r0) = text + len - (P + 1))
  by (rewrite <- Hr0, vrd_rest_len by lia; lia).
assert (Hlp : Z.of_nat (length (rest_atR tb text p)) = text + len - p) by (rewrite vrd_rest_len by lia; lia).
destruct (vrd_imove_nil d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v HPRE)
  as (HLM & HBM & HBB & HLS).
apply vrd_ipost_of_WF.
apply (vrd_iret_invR (@wle segs) (fun _ _ H => H) (wle_trans segs) Pm PLAW fx d ly Sa Hp W regs0 mem0 md0 ch e q v regs W
  ly Sa Hp M mdc 0 0
  (vrd_ipost_body d o q v text len p tb ly Sa Lam peak cnt fail ran most own) HPRE0 Hsp HSV Hgp Htp Hs2 HJ);
  [ | | | | exact HPM].
- intros a Ha Hn. unfold aview, mbyte. rewrite KM; [reflexivity|]. rewrite unsigned_lit_small by lia.
  unfold pi_wr, PI_FRAME. intros [H|[H|[H|H]]]; [lia| | |]; apply Hn; unfold rd_fp, inFP.
  + exists (q, q + 8). split; [left; reflexivity | cbn [fst snd]; lia].
  + exists (q + 16, q + 20). split; [right; left; reflexivity | cbn [fst snd]; lia].
  + exists (v, v + 56). split; [right; right; left; reflexivity | cbn [fst snd]; lia].
- exact Hfrm.
- intros r _. reflexivity.
- intros regs' md'' H10' HPR.
  try unfold vrd_ipost_body, vrd_items_q, tpiP_Q.
  exists [], (Some (PjGrammar.mk o [], r0)), [], [], [], Lam, peak, cnt, fail, ran.
  split; [rewrite vrd_strtod_same; exact (vrd_items_empty d o (rest_atR tb text p) r0 [] Hd Hsk)|].
  split; [exact (vrd_iledger d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v M HPRE KM)|].
  split; [exact (proj1 HROOM)|].
  split; [exact (PresetHullBudget.hull_used_refl Sa _)|].
  split; [exact (vrd_live_nil Sa)|].
  split; [exact (vrd_xfer_nil Sa)|].
  split; [exact (vrd_outcome_nil d o (rest_atR tb text p) (Some (PjGrammar.mk o [], r0)) Sa ran cnt fail
                   ltac:(rewrite (vrd_items_empty d o (rest_atR tb text p) r0 [] Hd Hsk); reflexivity))|].
  (* the outcome of an injected reading: no call, so no refusal *)
  split; [intros sm x0 os i H0 hist _ _ _ _; exact (vrd_granted_rep 0 cnt fail _)|].
  split; [exact HLM|]. split; [exact HBM|]. split; [exact HBB|]. split; [exact HLS|].
  split; [exact H10'|].
  (* the zeroed node, typed: the empty container *)
  assert (HD : pj_hdrR segs (mrestrict (w_H W) M) v (if o then 6 else 5) 0 0 0 0 0 0).
  { apply (vrd_hdr_typed (mrestrict (w_H W) mem0) _ v); [exact HZv | | | destruct o; lia | exact Vty].
    - apply KF. intros a Ha. split; [lia|]. unfold pi_wr.
      intros [H|[H|[H|H]]]; [exact (Hvfr a ltac:(lia) H) | lia | lia | lia].
    - split; [exact Hvmod | intros x Hx; apply KW; exact (RWv x Hx)]. }
  (* The kit's cut: the empty container's order list is empty, as the model's (jf_cont's closer arm) *)
  split; [intros _ n _; exists []; split; [exact (vrd_hdr_fo _ _ v (if o then 6 else 5) n HD)
                                         | exact (eq_sym (vrd_frees_empty d o (rest_atR tb text p) r0 [] Hd Hsk))]|].
  split; [|split; [|split]].
  + (* the cursor past the closer, at the entry depth *)
    replace (text + len - Z.of_nat (length r0)) with (P + 1) by lia.
    split; [exact Vp|].
    split; [apply (val_mem_keep segs _ _ _ _ _ Ve0); apply KF; intros a Ha; cbn in Ha; split; [lia|];
            unfold pi_wr, PI_FRAME; lia|].
    split; [exact Vd|]. split; [intros x Hx; apply KW; exact (RWq0 x Hx)|].
    do 3 (split; [assumption|]). split; [lia|]. split; [exact Hlen|].
    split; [apply (garr8_keep segs _ _ _ _ Hgt); apply KF; intros a Ha; rewrite Hlen in Ha; split; [lia|];
            unfold pi_wr, PI_FRAME in *; lia|].
    split; [exact Hqt|]. lia.
  + destruct o; cbn [PjGrammar.mk map pj_nodeR tag].
    * split; [constructor|]. split; [intros bb x Hb; destruct Hb|].
      exists 0, 0, 0, 0, 0, 0. split; [exact HD|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [left; split; [reflexivity | split; reflexivity]|].
      exists []. split; [reflexivity|]. reflexivity.
    * split; [constructor|]. split; [intros bb x Hb; destruct Hb|].
      exists 0, 0, 0, 0, 0, 0. split; [exact HD|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [left; split; reflexivity|].
      exists []. split; [reflexivity|]. reflexivity.
  + (* The kit's cut (CAP): the empty container's capacity *)
    exact (vrd_ncap_empty _ o v (if o then 6 else 5) HD).
  + cbn [Ledger.lsum]. lia.
Qed.
Lemma vrd_iempty_ret : forall d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v
    P r0 regs M mdc,
  vrd_ipre d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v ->
  (d < PjGrammar.MAXD)%nat ->
  PjGrammar.skip (tl (rest_atR tb text p)) = PjGrammar.closer o :: r0 ->
  rest_atR tb text (P + 1) = r0 -> p + 1 <= P < text + len ->
  spZ regs = spZ regs0 - 144 -> vi_saved W M regs0 ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 18 = w64 0 ->
  val_mem segs (mrestrict (w_H W) M) q 8 (P + 1) ->
  val_mem segs (mrestrict (w_H W) M) (q + 16) 4 (Z.of_nat d) ->
  val_mem segs (mrestrict (w_H W) M) v 4 (if o then 6 else 5) ->
  (forall x : word, ~ pi_wr (spZ regs0) q v (bv_unsigned x) -> mrestrict (w_H W) M x = mrestrict (w_H W) mem0 x) ->
  mem_grows (mrestrict (w_H W) mem0) (mrestrict (w_H W) M) ->
  ajournal_x (SK := SK) segs B prh_pst ARx (STK_parse_items d + e) (spZ regs0 + e) (rd_fp q v)
    ly Sa Hp W mem0 md0 [] ly Sa Hp W M mdc 0 ->
  SRr segs W (mkCfg (YK11.mkst regs (w64 (A_IPC A_IEPI_SLOT)) M (YK11.seg_rom segs)) mdc)
    (vrd_ipost d o q v text len p e tb regs0 ly Sa Hp W mem0 md0 Lam peak cnt fail ran most own).
Proof.
intros d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v P r0 regs M mdc
  HPRE Hd Hsk Hr0 HP Hsp HSV Hgp Htp Hs2 Vp Vd Vty KM KG HJ.
eapply SRr_mono; [exact (vrd_iempty_ret_inv (fun _ => True) vrd_inv_true d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt
  fail ran most own e q text len p tb v P r0 regs M mdc HPRE Hd Hsk Hr0 HP Hsp HSV Hgp Htp Hs2 Vp Vd Vty KM KG HJ I)|].
intros W' c' _ (H & _). exact H.
Qed.

(* ============================================================================================================== *)
(* THE EXIT AT THE END OF THE TEXT (row 78 with the cursor at text + len): rows 78..81 and the `jal grow` of row
   91, then the grow step. Generic in the world relation R of the grow step (the runner stretch at wle, lifted by
   vrd_srrG_lift).                                                                                              *)
(* ============================================================================================================== *)
Lemma vrd_iX0_inv : forall (R : world segs -> world segs -> Prop), (forall W1 W2, wle W1 W2 -> R W1 W2) ->
  (forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
  forall (Pm : (word -> option byte) -> Prop), srr_inv_laws segs Pm ->
  forall d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v,
  vrd_ipre d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v ->
  vrd_iDstep_PR R Pm d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v ->
  forall regs M mdc,
  vrd_imid d o e q text len v regs0 ly Sa Hp W mem0 md0 (text + len) regs M mdc ->
  p + 1 <= text + len ->
  PjGrammar.skip (tl (rest_atR tb text p)) = rest_atR tb text (text + len) ->
  Pm M ->
  SRrG segs R W (mkCfg (YK11.mkst regs (Z_to_bv 64 (BASE + (PI_X - A_prog_base))) M (YK11.seg_rom segs)) mdc)
    (fun W' c' => vrd_iQall d o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v W' c' /\
       Pm (ms_mem (cfg_ms c'))).
Proof.
intros R Hsub Htr Pm PLAW d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v HPRE HD
  regs M mdc HMID Hp1 Hsk HPM.
apply (vrd_srrG_lift R Hsub Htr).
pose proof HPRE as ((HPRE0 & HROD & _) & HMN & HCTX & HUC & HCE & HCHI & HQCH & H10e & H11e & H12e & HRD & Hpe & Hop & HROOM & HPKS & HPKL &
  HFU & HFR & HCWR).
pose proof HRD as (Hfrm & Hmu & Hu1 & Hu2 & HIN & HWIN & Hspq & Hqe & HRAq0 & HSRC & HHOME & HMAX & HNODE & Hqv &
  Htv & Hvw & HLED & HdM & Hcnt).
pose proof HIN as (Vp0 & Ve0 & Vd0 & RWq0 & Hq80 & Ht0 & Ht62 & Htp & Hlen & Hgt & Hqt & Hd32).
pose proof HNODE as (Hv4096 & Hv8 & _ & _ & _ & HAMv & _).
pose proof HPRE0 as (HAR & Hra & Hra4 & Hgp0 & Htp0 & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof (vrd_stk_ge d) as HSTK. pose proof H_img as (Himg1 & Himg2 & Himg3).
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAMv.
assert (Rv : 4096 <= v /\ v + 56 <= 2 ^ 47) by lia.
pose proof HMID as (HAT & Hgp & Htp' & H18 & H20 & Vty & KM & KG & HJ).
pose proof HAT as (Hsp & Hs1 & Hs2 & Hs16 & H8 & H26 & Hq1 & Hq2 & Hq3 & Hq8 & H9 & H21 & H22 & H23 & H27 & H11 & Hd &
  H19 & H12 & He & HP1 & HP2 & _).
destruct (vrd_ist_X0 regs regs0 W M o q (Z.of_nat d) text len (text + len) HAT ltac:(lia)) as [HS SHOK].
pose proof (vrd_iregs_X regs regs0 0 (text + len) q H8 H26 Hq1 Hq2 H9 H21 H22 H23 H27) as HRK.
set (E := vrd_iEX regs regs0 0 (text + len)) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold vrd_iEX; apply Eimg_env).
assert (E8X : ew E 8 = w64 q) by (subst E; rewrite (vrd_iEX_reg regs regs0 0 (text + len) 8 8%bv eq_refl); exact H8).
pose (RUNF := paj_run_xf_inv (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B prh_pst ARx LAWS Pm PLAW).
paj_run_tok_x_inv RUNF HS HJ SHOK HPM pi_Bspan;
  [apply (vrd_iawrB E q); [exact E8X | lia | lia | lia | right; reflexivity]|].
match goal with ms0 : machine_state |- _ => rename ms0 into MS end.
pose proof (vrd_ikeepB E q _ _ _ E8X ltac:(lia) HFr (or_intror eq_refl)) as KQ.
prreg HS (Z_to_bv 5 10) R10. prreg HS (Z_to_bv 5 1) R1.
apply SRr_ret. cbv beta.
eapply (HD (text + len) E _ MS _ HS); [reflexivity | reflexivity | | | | lia | exact Hsk | | exact HPM].
- apply (vrd_imid_step d o e q text len v regs0 ly Sa Hp W mem0 md0 (text + len) regs M mdc (text + len) _ _ _ HMID
    Hqv Rv); try (vrd_gstep HS HRK MS (w_H W) regs H12);
    [exact KQ | exact HG | | | lia | lia | exact HJ].
  + vrd_chunk_st HS E MS (w_H W) 1%nat 0 8%N (SOff 46 0) (text + len) VQ.
    specialize (VQ ltac:(cbn [sv_denot]; subst E; rewrite vrd_iEX_P; unfold w64; rewrite unsigned_lit_small by lia;
      rewrite Z.add_0_r; reflexivity) ltac:(lia) ltac:(lia)).
    cbn [base_val YP09.r_base] in VQ. subst E. rewrite (vrd_iEX_reg regs regs0 0 (text + len) 8 8%bv eq_refl), H8 in VQ.
    unfold w64 in VQ. rewrite unsigned_lit_small, Z.add_0_r in VQ by lia. exact VQ.
  + vrd_chunk_st HS E MS (w_H W) 3%nat 16 4%N (SOff 11 1) (Z.of_nat d + 1) VQ.
    specialize (VQ ltac:(cbn [sv_denot]; subst E; rewrite (vrd_iEX_reg regs regs0 0 (text + len) 11 11%bv eq_refl), H11;
      unfold w64; rewrite unsigned_lit_small by lia; reflexivity) ltac:(cbn; lia) ltac:(lia)).
    cbn [base_val YP09.r_base] in VQ. subst E. rewrite (vrd_iEX_reg regs regs0 0 (text + len) 8 8%bv eq_refl), H8 in VQ.
    unfold w64 in VQ. rewrite unsigned_lit_small in VQ by lia. exact VQ.
- transitivity (getr (ms_regs MS) (Z_to_bv 5 10)); [reflexivity|]. rewrite R10.
  subst E. rewrite (vrd_iEX_reg regs regs0 0 (text + len) 20 20%bv eq_refl). exact H20.
- transitivity (getr (ms_regs MS) (Z_to_bv 5 1)); [reflexivity|]. rewrite R1. vm_compute. reflexivity.
- intros r Hr. rewrite Hsk, vrd_rest_end in Hr by lia. discriminate Hr.
Qed.

Lemma vrd_iX0 : forall d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v,
  vrd_ipre d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v ->
  vrd_iDstep d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v ->
  forall regs M mdc,
  vrd_imid d o e q text len v regs0 ly Sa Hp W mem0 md0 (text + len) regs M mdc ->
  p + 1 <= text + len ->
  PjGrammar.skip (tl (rest_atR tb text p)) = rest_atR tb text (text + len) ->
  SRr' segs YGcfRehidePost.RZ_cf W
    (mkCfg (YK11.mkst regs (Z_to_bv 64 (BASE + (PI_X - A_prog_base))) M (YK11.seg_rom segs)) mdc)
    (vrd_iQall d o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v).
Proof.
intros d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v HPRE HD regs M mdc HMID Hp1
  Hsk.
eapply (SRrG_mono segs (wle' segs YGcfRehidePost.RZ_cf));
  [exact (vrd_iX0_inv (wle' segs YGcfRehidePost.RZ_cf) (wle_wle' segs YGcfRehidePost.RZ_cf)
     (wle'_trans segs YGcfRehidePost.RZ_cf) (fun _ => True) vrd_inv_true d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt
     fail ran most own e q text len p tb v HPRE (vrd_iDstep_to_P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HD) regs M
     mdc HMID Hp1 Hsk I)|].
intros W' c' _ (H & _). exact H.
Qed.

(* ============================================================================================================== *)
(* THE EXIT AT A NON-WHITE BYTE (row 78, cursor below text + len): rows 78..89 and the closer test - the empty
   container (rows 294..304, then vrd_iempty_ret) or the `jal grow` of row 91 and the grow step. Generic in the world
   relation R of the grow step, as vrd_iX0_inv.                                                                 *)
(* ============================================================================================================== *)
Lemma vrd_iX1_inv : forall (R : world segs -> world segs -> Prop), (forall W1 W2, wle W1 W2 -> R W1 W2) ->
  (forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
  forall (Pm : (word -> option byte) -> Prop), srr_inv_laws segs Pm ->
  forall d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v,
  vrd_ipre d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v ->
  (d < PjGrammar.MAXD)%nat ->
  vrd_iDstep_PR R Pm d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v ->
  forall P regs M mdc,
  vrd_imid d o e q text len v regs0 ly Sa Hp W mem0 md0 P regs M mdc ->
  p + 1 <= P < text + len ->
  PjGrammar.ws (nth (Z.to_nat (P - text)) tb 0) = false ->
  PjGrammar.skip (tl (rest_atR tb text p)) = rest_atR tb text P ->
  Pm M ->
  SRrG segs R W (mkCfg (YK11.mkst regs (Z_to_bv 64 (BASE + (PI_X - A_prog_base))) M (YK11.seg_rom segs)) mdc)
    (fun W' c' => vrd_iQall d o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v W' c' /\
       Pm (ms_mem (cfg_ms c'))).
Proof.
intros R Hsub Htr Pm PLAW d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v HPRE Hd
  HD P regs M mdc HMID HP Hnws Hsk HPM.
assert (Rr : forall W1, R W1 W1) by (intros W1; apply Hsub; apply wle_refl).
apply (vrd_srrG_lift R Hsub Htr).
pose proof HPRE as ((HPRE0 & HROD & _) & HMN & HCTX & HUC & HCE & HCHI & HQCH & H10e & H11e & H12e & HRD & Hpe & Hop & HROOM & HPKS & HPKL &
  HFU & HFR & HCWR).
pose proof HRD as (Hfrm & Hmu & Hu1 & Hu2 & HIN & HWIN & Hspq & Hqe & HRAq0 & HSRC & HHOME & HMAX & HNODE & Hqv &
  Htv & Hvw & HLED & HdM & Hcnt).
pose proof HIN as (Vp0 & Ve0 & Vd0 & RWq0 & Hq80 & Ht0 & Ht62 & Htp & Hlen & Hgt & Hqt & Hd32).
pose proof HNODE as (Hv4096 & Hv8 & _ & _ & _ & HAMv & _).
pose proof HSRC as (Hbt & Ht4096 & Htceil & Htamr & HRAt & Hhull).
pose proof HPRE0 as (HAR & Hra & Hra4 & Hgp0 & Htp0 & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof (vrd_stk_ge d) as HSTK. pose proof H_img as (Himg1 & Himg2 & Himg3).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAMv, Htamr.
rewrite Hlen in Htceil, Htamr, HRAt.
assert (Rv : 4096 <= v /\ v + 56 <= 2 ^ 47) by lia.
pose proof HMID as (HAT & Hgp & Htp' & H18 & H20 & Vty & KM & KG & HJ).
pose proof HAT as (Hsp & Hs1 & Hs2 & Hs16 & H8 & H26 & Hq1 & Hq2 & Hq3 & Hq8 & H9 & H21 & H22 & H23 & H27 & H11 & Hdd &
  H19 & H12 & He & HP1 & HP2 & HSV & _).
(* the byte at the cursor, its shadow, and that it is application memory *)
set (c := nth (Z.to_nat (P - text)) tb 0).
assert (Hj : (Z.to_nat (P - text) < length tb)%nat) by lia.
destruct (Hgt (Z.to_nat (P - text)) Hj) as [Vc0 Hc0]. fold c in Vc0, Hc0.
replace (text + Z.of_nat (Z.to_nat (P - text))) with P in Vc0 by lia.
assert (Vc : val_mem segs (mrestrict (w_H W) M) P 1 c).
{ apply (val_mem_keep segs _ _ _ _ _ Vc0). apply (vrd_rdkeep_w (w_H W) mem0 M _ _ KM).
  intros a Ha. cbn in Ha. split; [lia|]. unfold pi_wr, PI_FRAME in *. lia. }
assert (HRAP : range_addressable (aview segs (w_H W) M) SHADOW_OFF P 1).
{ apply (range_addressable_sub _ _ text len P 1); [|lia|lia].
  eapply range_addressable_agree; [|exact HRAt]. intros x Hx.
  unfold aview, mbyte. rewrite KM; [reflexivity|]. unfold shadow_of_addr.
  assert (Hsx : 0 <= x / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). unfold pi_wr, PI_FRAME in *. unfold SHADOW_OFF. lia. }
assert (HAP : P < SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= P) by (unfold SHADOW_OFF; lia).
assert (Hcr : 0 <= c <= 255) by lia.
destruct (vrd_ist_X1 regs regs0 W M o q (Z.of_nat d) text len P c HAT ltac:(lia) Hcr Vc HRAP HAP) as [HS SHOK].
pose proof (vrd_iregs_X regs regs0 c P q H8 H26 Hq1 Hq2 H9 H21 H22 H23 H27) as HRK.
assert (HEI : img_env VAL A_LIM (vrd_iEX regs regs0 c P)) by (unfold vrd_iEX; apply Eimg_env).
assert (E19 : ew (vrd_iEX regs regs0 c P) 19 = w64 (if o then 1 else 0))
  by (rewrite (vrd_iEX_reg regs regs0 c P 19 19%bv eq_refl); exact H19).
assert (E8X : ew (vrd_iEX regs regs0 c P) 8 = w64 q)
  by (rewrite (vrd_iEX_reg regs regs0 c P 8 8%bv eq_refl); exact H8).
assert (Hrc : rest_atR tb text P = c :: rest_atR tb text (P + 1)) by (apply vrd_rest_cons; lia).
assert (Hlr : Z.of_nat (length (rest_atR tb text (P + 1))) = text + len - (P + 1)) by (rewrite vrd_rest_len; lia).
pose (RUNF := paj_run_xf_inv (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B prh_pst ARx LAWS Pm PLAW).
pose (RUNTO := paj_run_to_xf_inv (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B prh_pst ARx LAWS Pm PLAW).
pose (BR := paj_branch (PI := PI_prog_A)).
(* rows 78..87 and the `beqz s3` of row 87 *)
paj_run_tok_x_inv RUNF HS HJ SHOK HPM pi_Bspan;
  [apply (vrd_iawrB _ q); [exact E8X | lia | lia | lia | left; reflexivity]|].
rename HFr into HFr1, HG into HG1. clear HF.
psrr_branch_tok RUNF BR HS SHOK pi_Bspan;
  rewrite branch_eq_U, U_SOff, U_SLit in Hc; rewrite ?ew_ewset_other in Hc by lia; rewrite E19 in Hc;
  destruct o; [ exfalso; vm_compute in Hc; discriminate Hc | | | exfalso; vm_compute in Hc; discriminate Hc ].
- (* an array (s3 = 0): the ']' test of row 294 *)
  clear Hc.
  paj_run_tok_x_inv RUNF HS HJ SHOK HPM pi_Bspan;
    [apply (vrd_iawrB _ q); [rewrite ?ew_ewset_other by lia; exact E8X | lia | lia | lia | left; vm_compute; reflexivity]|].
  rename HFr into HFr2, HG into HG2. clear HF.
  psrr_branch_tok RUNF BR HS SHOK pi_Bspan;
    rewrite branch_ne_U, U_SOff, U_SLit in Hc; rewrite ?ew_ewset_other in Hc by lia; rewrite vrd_iEX_c in Hc;
    unfold w64 in Hc; rewrite unsigned_lit_small, Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia).
  + (* 93 <> c: rows 90..91, the jal grow *)
    apply negb_true_iff, Z.eqb_neq in Hc.
    paj_run_tok_x_inv RUNF HS HJ SHOK HPM pi_Bspan;
      [apply (vrd_iawrB _ q); [rewrite ?ew_ewset_other by lia; exact E8X | lia | lia | lia | left; vm_compute; reflexivity]|].
    rename HFr into HFr3, HG into HG3. clear HF.
    lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => set (MS := m) in * end.
    vrd_kq HFr1 E8X q K1. vrd_kq HFr2 E8X q K2. vrd_kq HFr3 E8X q K3.
    vrd_rk HS HRK RK.
    prreg HS (Z_to_bv 5 10) R10. prreg HS (Z_to_bv 5 1) R1.
    apply SRr_ret. cbv beta.
    eapply (HD P _ _ MS _ HS); [reflexivity | reflexivity | | | | lia | exact Hsk | | exact HPM].
    * apply (vrd_imid_step d false e q text len v regs0 ly Sa Hp W mem0 md0 P regs M mdc P _ _ _ HMID Hqv Rv);
        try (vrd_gstep HS RK MS (w_H W) regs H12);
        [intros x Hx; rewrite (K3 x Hx), (K2 x Hx); exact (K1 x Hx)
        | exact (mem_grows_trans _ _ _ (mem_grows_trans _ _ _ HG1 HG2) HG3) | | | lia | lia | exact HJ].
      -- vrd_chunk_stH HS MS (w_H W) 2%nat 0 8%N (SOff 46 0) P VQ.
         specialize (VQ ltac:(cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite vrd_iEX_P; unfold w64;
           rewrite unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity) ltac:(lia) ltac:(lia)).
         cbn [base_val YP09.r_base] in VQ. rewrite ?ew_ewset_other in VQ by lia. rewrite E8X in VQ.
         unfold w64 in VQ. rewrite unsigned_lit_small, Z.add_0_r in VQ by lia. exact VQ.
      -- vrd_chunk_stH HS MS (w_H W) 4%nat 16 4%N (SOff 11 1) (Z.of_nat d + 1) VQ.
         specialize (VQ ltac:(cbn [sv_denot]; rewrite ?ew_ewset_other by lia;
           rewrite (vrd_iEX_reg regs regs0 c P 11 11%bv eq_refl), H11; unfold w64; rewrite unsigned_lit_small by lia;
           reflexivity) ltac:(cbn; lia) ltac:(lia)).
         cbn [base_val YP09.r_base] in VQ. rewrite ?ew_ewset_other in VQ by lia. rewrite E8X in VQ.
         unfold w64 in VQ. rewrite unsigned_lit_small in VQ by lia. exact VQ.
    * transitivity (getr (ms_regs MS) (Z_to_bv 5 10)); [reflexivity|]. rewrite R10.
      rewrite ?ew_ewset_other by lia. rewrite (vrd_iEX_reg regs regs0 c P 20 20%bv eq_refl). exact H20.
    * transitivity (getr (ms_regs MS) (Z_to_bv 5 1)); [reflexivity|]. rewrite R1. vm_compute. reflexivity.
    * intros r Hr. rewrite Hsk, Hrc in Hr. injection Hr as Hr _. cbn in Hr. lia.
  + (* 93 = c: rows 294..304, the empty array *)
    apply negb_false_iff, Z.eqb_eq in Hc.
    paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM pi_Bspan (4 * Z.of_nat A_IEPI_SLOT);
      [apply (vrd_iawrB _ q); [rewrite ?ew_ewset_other by lia; exact E8X | lia | lia | lia | left; vm_compute; reflexivity]|].
    rename HFr into HFr3, HG into HG3. clear HF.
    lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => set (MS := m) in * end.
    vrd_kq HFr1 E8X q K1. vrd_kq HFr2 E8X q K2. vrd_kq HFr3 E8X q K3.
    assert (KQ : forall x : word, ~ (q <= bv_unsigned x < q + 8 \/ q + 16 <= bv_unsigned x < q + 20) ->
      mrestrict (w_H W) (ms_mem MS) x = mrestrict (w_H W) M x)
      by (intros x Hx; rewrite (K3 x Hx), (K2 x Hx); exact (K1 x Hx)).
    vrd_rk HS HRK RK.
    prreg HS (Z_to_bv 5 18) R18.
    pmkst HS.
    lazymatch goal with |- SRr _ _ (mkCfg (YK11.mkst _ ?pc _ _) _) _ =>
      replace pc with (w64 (A_IPC A_IEPI_SLOT)) by (vm_compute; reflexivity) end.
    apply (SRr_mono segs _ _ (fun W' c' => vrd_ipost d false q v text len p e tb regs0 ly Sa Hp W mem0 md0 Lam peak cnt fail
      ran most own W' c' /\ Pm (ms_mem (cfg_ms c'))));
      [| intros W' c' _ (Hq' & Hpm'); apply (SRrG_ret segs R Rr); split; [right; exact Hq' | exact Hpm']].
    apply (vrd_iempty_ret_inv Pm PLAW d CTX false ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v P
      (rest_atR tb text (P + 1)) _ _ _ HPRE Hd).
    * rewrite Hsk, Hrc, <- Hc. reflexivity.
    * reflexivity.
    * lia.
    * unfold spZ. rewrite (vrd_carry _ _ MS (w_H W) vrd_rX regs 2%bv HS RK ltac:(vm_compute; reflexivity)). exact Hsp.
    * intros jj Hjj. apply (val_mem_keep segs _ _ _ _ _ (HSV jj Hjj)).
      apply (vrd_rdkeep_w (w_H W) M (ms_mem MS) (fun a => q <= a < q + 8 \/ q + 16 <= a < q + 20) _ KQ).
      intros a Ha. cbn in Ha. split; [lia | cbv beta; lia].
    * rewrite (vrd_carry _ _ MS (w_H W) vrd_rX regs 3%bv HS RK ltac:(vm_compute; reflexivity)). exact Hgp.
    * rewrite (vrd_carry _ _ MS (w_H W) vrd_rX regs 4%bv HS RK ltac:(vm_compute; reflexivity)). exact Htp'.
    * transitivity (getr (ms_regs MS) (Z_to_bv 5 18)); [reflexivity|]. exact R18.
    * vrd_chunkH HS MS (w_H W) 2%nat 0 8%N (SOff 46 1) (P + 1) VQ.
      specialize (VQ ltac:(cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite vrd_iEX_P; unfold w64;
        rewrite unsigned_lit_small by lia; reflexivity) ltac:(lia) ltac:(lia)).
      cbn [base_val YP09.r_base] in VQ. rewrite ?ew_ewset_other in VQ by lia. rewrite E8X in VQ.
      unfold w64 in VQ. rewrite unsigned_lit_small, Z.add_0_r in VQ by lia. exact VQ.
    * vrd_chunkH HS MS (w_H W) 4%nat 16 4%N (SOff 11 0) (Z.of_nat d) VQ.
      specialize (VQ ltac:(cbn [sv_denot]; rewrite ?ew_ewset_other by lia;
        rewrite (vrd_iEX_reg regs regs0 c P 11 11%bv eq_refl), H11; unfold w64; rewrite unsigned_lit_small by lia;
        rewrite Z.add_0_r; reflexivity) ltac:(cbn; lia) ltac:(lia)).
      cbn [base_val YP09.r_base] in VQ. rewrite ?ew_ewset_other in VQ by lia. rewrite E8X in VQ.
      unfold w64 in VQ. rewrite unsigned_lit_small in VQ by lia. exact VQ.
    * apply (val_mem_keep segs _ _ _ _ _ Vty).
      apply (vrd_rdkeep_w (w_H W) M (ms_mem MS) (fun a => q <= a < q + 8 \/ q + 16 <= a < q + 20) _ KQ).
      intros a Ha. cbn in Ha. split; [lia | cbv beta; lia].
    * intros x Hx. rewrite KQ; [exact (KM x Hx)|]. intros Hq0. apply Hx. unfold pi_wr. right. lia.
    * exact (mem_grows_trans _ _ _ KG (mem_grows_trans _ _ _ (mem_grows_trans _ _ _ HG1 HG2) HG3)).
    * exact HJ.
    * exact HPM.
- (* an object (s3 <> 0): the '}' test of rows 88..89 *)
  clear Hc.
  paj_run_tok_x_inv RUNF HS HJ SHOK HPM pi_Bspan;
    [apply (vrd_iawrB _ q); [rewrite ?ew_ewset_other by lia; exact E8X | lia | lia | lia | left; vm_compute; reflexivity]|].
  rename HFr into HFr2, HG into HG2. clear HF.
  psrr_branch_tok RUNF BR HS SHOK pi_Bspan;
    rewrite branch_eq_U, U_SOff, U_SLit in Hc; rewrite ?ew_ewset_other in Hc by lia; rewrite vrd_iEX_c in Hc;
    unfold w64 in Hc; rewrite unsigned_lit_small, Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia).
  + (* 125 = c: rows 296..304, the empty object *)
    apply Z.eqb_eq in Hc.
    paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM pi_Bspan (4 * Z.of_nat A_IEPI_SLOT);
      [apply (vrd_iawrB _ q); [rewrite ?ew_ewset_other by lia; exact E8X | lia | lia | lia | left; vm_compute; reflexivity]|].
    rename HFr into HFr3, HG into HG3. clear HF.
    lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => set (MS := m) in * end.
    vrd_kq HFr1 E8X q K1. vrd_kq HFr2 E8X q K2. vrd_kq HFr3 E8X q K3.
    assert (KQ : forall x : word, ~ (q <= bv_unsigned x < q + 8 \/ q + 16 <= bv_unsigned x < q + 20) ->
      mrestrict (w_H W) (ms_mem MS) x = mrestrict (w_H W) M x)
      by (intros x Hx; rewrite (K3 x Hx), (K2 x Hx); exact (K1 x Hx)).
    vrd_rk HS HRK RK.
    prreg HS (Z_to_bv 5 18) R18.
    pmkst HS.
    lazymatch goal with |- SRr _ _ (mkCfg (YK11.mkst _ ?pc _ _) _) _ =>
      replace pc with (w64 (A_IPC A_IEPI_SLOT)) by (vm_compute; reflexivity) end.
    apply (SRr_mono segs _ _ (fun W' c' => vrd_ipost d true q v text len p e tb regs0 ly Sa Hp W mem0 md0 Lam peak cnt fail
      ran most own W' c' /\ Pm (ms_mem (cfg_ms c'))));
      [| intros W' c' _ (Hq' & Hpm'); apply (SRrG_ret segs R Rr); split; [right; exact Hq' | exact Hpm']].
    apply (vrd_iempty_ret_inv Pm PLAW d CTX true ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v P
      (rest_atR tb text (P + 1)) _ _ _ HPRE Hd).
    * rewrite Hsk, Hrc, <- Hc. reflexivity.
    * reflexivity.
    * lia.
    * unfold spZ. rewrite (vrd_carry _ _ MS (w_H W) vrd_rX regs 2%bv HS RK ltac:(vm_compute; reflexivity)). exact Hsp.
    * intros jj Hjj. apply (val_mem_keep segs _ _ _ _ _ (HSV jj Hjj)).
      apply (vrd_rdkeep_w (w_H W) M (ms_mem MS) (fun a => q <= a < q + 8 \/ q + 16 <= a < q + 20) _ KQ).
      intros a Ha. cbn in Ha. split; [lia | cbv beta; lia].
    * rewrite (vrd_carry _ _ MS (w_H W) vrd_rX regs 3%bv HS RK ltac:(vm_compute; reflexivity)). exact Hgp.
    * rewrite (vrd_carry _ _ MS (w_H W) vrd_rX regs 4%bv HS RK ltac:(vm_compute; reflexivity)). exact Htp'.
    * transitivity (getr (ms_regs MS) (Z_to_bv 5 18)); [reflexivity|]. exact R18.
    * vrd_chunkH HS MS (w_H W) 2%nat 0 8%N (SOff 46 1) (P + 1) VQ.
      specialize (VQ ltac:(cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite vrd_iEX_P; unfold w64;
        rewrite unsigned_lit_small by lia; reflexivity) ltac:(lia) ltac:(lia)).
      cbn [base_val YP09.r_base] in VQ. rewrite ?ew_ewset_other in VQ by lia. rewrite E8X in VQ.
      unfold w64 in VQ. rewrite unsigned_lit_small, Z.add_0_r in VQ by lia. exact VQ.
    * vrd_chunkH HS MS (w_H W) 4%nat 16 4%N (SOff 11 0) (Z.of_nat d) VQ.
      specialize (VQ ltac:(cbn [sv_denot]; rewrite ?ew_ewset_other by lia;
        rewrite (vrd_iEX_reg regs regs0 c P 11 11%bv eq_refl), H11; unfold w64; rewrite unsigned_lit_small by lia;
        rewrite Z.add_0_r; reflexivity) ltac:(cbn; lia) ltac:(lia)).
      cbn [base_val YP09.r_base] in VQ. rewrite ?ew_ewset_other in VQ by lia. rewrite E8X in VQ.
      unfold w64 in VQ. rewrite unsigned_lit_small in VQ by lia. exact VQ.
    * apply (val_mem_keep segs _ _ _ _ _ Vty).
      apply (vrd_rdkeep_w (w_H W) M (ms_mem MS) (fun a => q <= a < q + 8 \/ q + 16 <= a < q + 20) _ KQ).
      intros a Ha. cbn in Ha. split; [lia | cbv beta; lia].
    * intros x Hx. rewrite KQ; [exact (KM x Hx)|]. intros Hq0. apply Hx. unfold pi_wr. right. lia.
    * exact (mem_grows_trans _ _ _ KG (mem_grows_trans _ _ _ (mem_grows_trans _ _ _ HG1 HG2) HG3)).
    * exact HJ.
    * exact HPM.
  + (* 125 <> c: row 90..91, the jal grow *)
    apply Z.eqb_neq in Hc.
    paj_run_tok_x_inv RUNF HS HJ SHOK HPM pi_Bspan;
      [apply (vrd_iawrB _ q); [rewrite ?ew_ewset_other by lia; exact E8X | lia | lia | lia | left; vm_compute; reflexivity]|].
    rename HFr into HFr3, HG into HG3. clear HF.
    lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => set (MS := m) in * end.
    vrd_kq HFr1 E8X q K1. vrd_kq HFr2 E8X q K2. vrd_kq HFr3 E8X q K3.
    vrd_rk HS HRK RK.
    prreg HS (Z_to_bv 5 10) R10. prreg HS (Z_to_bv 5 1) R1.
    apply SRr_ret. cbv beta.
    eapply (HD P _ _ MS _ HS); [reflexivity | reflexivity | | | | lia | exact Hsk | | exact HPM].
    * apply (vrd_imid_step d true e q text len v regs0 ly Sa Hp W mem0 md0 P regs M mdc P _ _ _ HMID Hqv Rv);
        try (vrd_gstep HS RK MS (w_H W) regs H12);
        [intros x Hx; rewrite (K3 x Hx), (K2 x Hx); exact (K1 x Hx)
        | exact (mem_grows_trans _ _ _ (mem_grows_trans _ _ _ HG1 HG2) HG3) | | | lia | lia | exact HJ].
      -- vrd_chunk_stH HS MS (w_H W) 2%nat 0 8%N (SOff 46 0) P VQ.
         specialize (VQ ltac:(cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite vrd_iEX_P; unfold w64;
           rewrite unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity) ltac:(lia) ltac:(lia)).
         cbn [base_val YP09.r_base] in VQ. rewrite ?ew_ewset_other in VQ by lia. rewrite E8X in VQ.
         unfold w64 in VQ. rewrite unsigned_lit_small, Z.add_0_r in VQ by lia. exact VQ.
      -- vrd_chunk_stH HS MS (w_H W) 4%nat 16 4%N (SOff 11 1) (Z.of_nat d + 1) VQ.
         specialize (VQ ltac:(cbn [sv_denot]; rewrite ?ew_ewset_other by lia;
           rewrite (vrd_iEX_reg regs regs0 c P 11 11%bv eq_refl), H11; unfold w64; rewrite unsigned_lit_small by lia;
           reflexivity) ltac:(cbn; lia) ltac:(lia)).
         cbn [base_val YP09.r_base] in VQ. rewrite ?ew_ewset_other in VQ by lia. rewrite E8X in VQ.
         unfold w64 in VQ. rewrite unsigned_lit_small in VQ by lia. exact VQ.
    * transitivity (getr (ms_regs MS) (Z_to_bv 5 10)); [reflexivity|]. rewrite R10.
      rewrite ?ew_ewset_other by lia. rewrite (vrd_iEX_reg regs regs0 c P 20 20%bv eq_refl). exact H20.
    * transitivity (getr (ms_regs MS) (Z_to_bv 5 1)); [reflexivity|]. rewrite R1. vm_compute. reflexivity.
    * intros r Hr. rewrite Hsk, Hrc in Hr. injection Hr as Hr _. cbn in Hr. lia.
Qed.

Lemma vrd_iX1 : forall d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v,
  vrd_ipre d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v ->
  (d < PjGrammar.MAXD)%nat ->
  vrd_iDstep d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v ->
  forall P regs M mdc,
  vrd_imid d o e q text len v regs0 ly Sa Hp W mem0 md0 P regs M mdc ->
  p + 1 <= P < text + len ->
  PjGrammar.ws (nth (Z.to_nat (P - text)) tb 0) = false ->
  PjGrammar.skip (tl (rest_atR tb text p)) = rest_atR tb text P ->
  SRr' segs YGcfRehidePost.RZ_cf W
    (mkCfg (YK11.mkst regs (Z_to_bv 64 (BASE + (PI_X - A_prog_base))) M (YK11.seg_rom segs)) mdc)
    (vrd_iQall d o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v).
Proof.
intros d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v HPRE Hd HD P regs M mdc
  HMID HP Hnws Hsk.
eapply (SRrG_mono segs (wle' segs YGcfRehidePost.RZ_cf));
  [exact (vrd_iX1_inv (wle' segs YGcfRehidePost.RZ_cf) (wle_wle' segs YGcfRehidePost.RZ_cf)
     (wle'_trans segs YGcfRehidePost.RZ_cf) (fun _ => True) vrd_inv_true d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt
     fail ran most own e q text len p tb v HPRE Hd (vrd_iDstep_to_P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HD) P
     regs M mdc HMID HP Hnws Hsk I)|].
intros W' c' _ (H & _). exact H.
Qed.

(* ============================================================================================================== *)
(* B. THE INLINED skip_ws LOOP (rows 59..74): from the loop head with the cursor P (a0 = a3 = P, a4 = 32, a5 = the
   white-space mask), the byte at P is tested (rows 64 and 67); a non-white byte leaves at row 78 (vrd_iX1); a white
   one is consumed (rows 68..72, the store q->p := P + 1) and the loop goes on at P + 1 (row 73), or leaves at row
   78 when P + 1 is the end (vrd_iX0). By induction on the bytes left.                                             *)
(* ============================================================================================================== *)
Lemma vrd_U_at : forall E (n : nat) x, ew E n = w64 x -> 0 <= x < 2 ^ 64 -> U E (SOff n 0) = x.
Proof.
intros E n x H Hx. rewrite U_SOff, H. unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
apply zcanon_id. unfold M64. lia.
Qed.

(* rows 65..67 decide PjGrammar.ws for a byte at most 32 *)
Lemma vrd_ws_bit : forall E c, ew E 15 = w64 PI_WSMASK -> U E (SOff 45 0) = c -> 0 <= c <= 32 ->
  (U E (SAlu ALU_AND (SAlu ALU_SRL (SOff 15 0) (SOff 45 0)) (SLit 1)) =? U E (SLit 0)) = negb (PjGrammar.ws c).
Proof.
intros E c H15 H45 Hc. rewrite !U_SAlu, !U_SLit, H45, (vrd_U_at E 15 PI_WSMASK H15) by (unfold PI_WSMASK; lia).
destruct (Z_of_nat_complete c ltac:(lia)) as [k ->].
assert (Hk : (k <= 32)%nat) by lia. clear Hc H45.
do 33 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
Qed.

Lemma vrd_ws_big : forall c, 32 < c -> PjGrammar.ws c = false.
Proof.
intros c Hc. unfold PjGrammar.ws.
destruct (Z.eqb_spec c 32), (Z.eqb_spec c 9), (Z.eqb_spec c 10), (Z.eqb_spec c 13); first [lia | reflexivity].
Qed.

(* the loop, generic in the world relation R of the grow step, as vrd_iX0_inv *)
Lemma vrd_iloop_inv : forall (R : world segs -> world segs -> Prop), (forall W1 W2, wle W1 W2 -> R W1 W2) ->
  (forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
  forall (Pm : (word -> option byte) -> Prop), srr_inv_laws segs Pm ->
  forall d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v,
  vrd_ipre d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v ->
  (d < PjGrammar.MAXD)%nat ->
  vrd_iDstep_PR R Pm d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v ->
  forall n P regs M mdc, Z.to_nat (text + len - P) = n ->
  vrd_imid d o e q text len v regs0 ly Sa Hp W mem0 md0 P regs M mdc ->
  getr regs 10 = w64 P -> getr regs 13 = w64 P -> getr regs 14 = w64 32 -> getr regs 15 = w64 PI_WSMASK ->
  p + 1 <= P < text + len ->
  PjGrammar.skip (tl (rest_atR tb text p)) = PjGrammar.skip (rest_atR tb text P) ->
  Pm M ->
  SRrG segs R W (mkCfg (YK11.mkst regs (Z_to_bv 64 (BASE + (PI_SKIPHD - A_prog_base))) M (YK11.seg_rom segs)) mdc)
    (fun W' c' => vrd_iQall d o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v W' c' /\
       Pm (ms_mem (cfg_ms c'))).
Proof.
intros R Hsub Htr Pm PLAW d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v HPRE
  Hd HD.
pose proof HPRE as ((HPRE0 & HROD & _) & HMN & HCTX & HUC & HCE & HCHI & HQCH & H10e & H11e & H12e & HRD & Hpe & Hop & HROOM & HPKS & HPKL &
  HFU & HFR & HCWR).
pose proof HRD as (Hfrm & Hmu & Hu1 & Hu2 & HIN & HWIN & Hspq & Hqe & HRAq0 & HSRC & HHOME & HMAX & HNODE & Hqv &
  Htv & Hvw & HLED & HdM & Hcnt).
pose proof HIN as (Vp0 & Ve0 & Vd0 & RWq0 & Hq80 & Ht0 & Ht62 & Htp & Hlen & Hgt & Hqt & Hd32).
pose proof HNODE as (Hv4096 & Hv8 & _ & _ & _ & HAMv & _).
pose proof HSRC as (Hbt & Ht4096 & Htceil & Htamr & HRAt & Hhull).
pose proof HPRE0 as (HAR & Hra & Hra4 & Hgp0 & Htp0 & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof (vrd_stk_ge d) as HSTK. pose proof H_img as (Himg1 & Himg2 & Himg3). unfold PI_FRAME in HSTK.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAMv, Htamr.
rewrite Hlen in Htceil, Htamr, HRAt.
assert (Rv : 4096 <= v /\ v + 56 <= 2 ^ 47) by lia.
pose (RUNF := paj_run_xf_inv (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B prh_pst ARx LAWS Pm PLAW).
pose (RUNTO := paj_run_to_xf_inv (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B prh_pst ARx LAWS Pm PLAW).
pose (BR := paj_branch (PI := PI_prog_A)).
intros n. induction n as [|n IH]; intros P regs M mdc Hn HMID H10 H13 H14 H15 HP Hinv HPM; [exfalso; lia|].
apply (vrd_srrG_lift R Hsub Htr).
pose proof HMID as (HAT & Hgp & Htp' & H18 & H20 & Vty & KM & KG & HJ).
pose proof HAT as (Hsp & Hs1 & Hs2 & Hs16 & H8 & H26 & Hq1 & Hq2 & Hq3 & Hq8 & H9 & H21 & H22 & H23 & H27 & H11 & Hdd &
  H19 & H12 & He & HP1 & HP2 & HSV & _).
(* the byte at the cursor, its shadow, and that it is application memory *)
set (c := nth (Z.to_nat (P - text)) tb 0).
assert (Hj : (Z.to_nat (P - text) < length tb)%nat) by lia.
destruct (Hgt (Z.to_nat (P - text)) Hj) as [Vc0 Hc0]. fold c in Vc0, Hc0.
replace (text + Z.of_nat (Z.to_nat (P - text))) with P in Vc0 by lia.
assert (Vc : val_mem segs (mrestrict (w_H W) M) P 1 c).
{ apply (val_mem_keep segs _ _ _ _ _ Vc0). apply (vrd_rdkeep_w (w_H W) mem0 M _ _ KM).
  intros a Ha. cbn in Ha. split; [lia|]. unfold pi_wr, PI_FRAME in *. lia. }
assert (HRAP : range_addressable (aview segs (w_H W) M) SHADOW_OFF P 1).
{ apply (range_addressable_sub _ _ text len P 1); [|lia|lia].
  eapply range_addressable_agree; [|exact HRAt]. intros x Hx.
  unfold aview, mbyte. rewrite KM; [reflexivity|]. unfold shadow_of_addr.
  assert (Hsx : 0 <= x / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). unfold pi_wr, PI_FRAME in *. unfold SHADOW_OFF. lia. }
assert (HAP : P < SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= P) by (unfold SHADOW_OFF; lia).
assert (Hcr : 0 <= c <= 255) by lia.
destruct (vrd_ist_L regs regs0 W M o q (Z.of_nat d) text len P c HAT ltac:(lia) Hcr Vc HRAP HAP H10 H13)
  as [HS SHOK].
pose proof (vrd_iregs_L regs regs0 c P q H8 H26 Hq1 Hq2 H9 H21 H22 H23 H27 H10 H13 ltac:(lia)) as HRK.
assert (HEI : img_env VAL A_LIM (vrd_iEX regs regs0 c P)) by (unfold vrd_iEX; apply Eimg_env).
assert (E8X : ew (vrd_iEX regs regs0 c P) 8 = w64 q)
  by (rewrite (vrd_iEX_reg regs regs0 c P 8 8%bv eq_refl); exact H8).
assert (Hrc : rest_atR tb text P = c :: rest_atR tb text (P + 1)) by (apply vrd_rest_cons; lia).
(* rows 59..64: the shadow of the byte, the byte, and `bltu a4, a6` *)
paj_run_tok_x_inv RUNF HS HJ SHOK HPM pi_Bspan;
  [apply (vrd_iawrB _ q); [exact E8X | lia | lia | lia | left; reflexivity]|].
rename HFr into HFr1, HG into HG1. clear HF.
psrr_branch_tok RUNF BR HS SHOK pi_Bspan;
  rewrite branch_ltu_U, !U_SOff in Hc; rewrite ?ew_ewset_other in Hc by lia;
  rewrite (vrd_iEX_reg regs regs0 c P 14 14%bv eq_refl), H14, vrd_iEX_c in Hc; unfold w64 in Hc;
  rewrite !unsigned_lit_small, !Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia).
- (* 32 < c: not white, row 78 *)
  apply Z.ltb_lt in Hc.
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM pi_Bspan (PI_X - A_prog_base);
    [apply (vrd_iawrB _ q); [rewrite ?ew_ewset_other by lia; exact E8X | lia | lia | lia | left; vm_compute; reflexivity]|].
  rename HFr into HFr2, HG into HG2. clear HF.
  lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => set (MS := m) in * end.
  vrd_kq HFr1 E8X q K1. vrd_kq HFr2 E8X q K2. vrd_rk HS HRK RK.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (YK11.mkst _ ?pc _ _) _) _ =>
    replace pc with (Z_to_bv 64 (BASE + (PI_X - A_prog_base))) by (vm_compute; reflexivity) end.
  apply SRr_ret. cbv beta.
  apply (vrd_iX1_inv R Hsub Htr Pm PLAW d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p
    tb v HPRE Hd HD P);
    [ | lia | exact (vrd_ws_big c Hc) | rewrite Hinv, Hrc; cbn [PjGrammar.skip]; rewrite (vrd_ws_big c Hc);
      reflexivity | exact HPM].
  apply (vrd_imid_step d o e q text len v regs0 ly Sa Hp W mem0 md0 P regs M mdc P _ _ _ HMID Hqv Rv);
    try (apply (vrd_carry _ _ MS (w_H W) vrd_rL regs _ HS RK); vm_compute; reflexivity);
    [intros x Hx; rewrite (K2 x Hx); exact (K1 x Hx) | exact (mem_grows_trans _ _ _ HG1 HG2) | | | lia | lia
    | exact HJ].
  + vrd_chunkH HS MS (w_H W) 2%nat 0 8%N (SOff 46 0) P VQ.
    specialize (VQ ltac:(cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite vrd_iEX_P; unfold w64;
      rewrite unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity) ltac:(lia) ltac:(lia)).
    cbn [base_val YP09.r_base] in VQ. rewrite ?ew_ewset_other in VQ by lia. rewrite E8X in VQ.
    unfold w64 in VQ. rewrite unsigned_lit_small, Z.add_0_r in VQ by lia. exact VQ.
  + vrd_chunkH HS MS (w_H W) 4%nat 16 4%N (SOff 11 1) (Z.of_nat d + 1) VQ.
    specialize (VQ ltac:(cbn [sv_denot]; rewrite ?ew_ewset_other by lia;
      rewrite (vrd_iEX_reg regs regs0 c P 11 11%bv eq_refl), H11; unfold w64; rewrite unsigned_lit_small by lia;
      reflexivity) ltac:(cbn; lia) ltac:(lia)).
    cbn [base_val YP09.r_base] in VQ. rewrite ?ew_ewset_other in VQ by lia. rewrite E8X in VQ.
    unfold w64 in VQ. rewrite unsigned_lit_small in VQ by lia. exact VQ.
- (* c <= 32: rows 65..67, the mask test *)
  apply Z.ltb_ge in Hc. rename Hc into Hc32.
  paj_run_tok_x_inv RUNF HS HJ SHOK HPM pi_Bspan;
    [apply (vrd_iawrB _ q); [rewrite ?ew_ewset_other by lia; exact E8X | lia | lia | lia | left; vm_compute; reflexivity]|].
  rename HFr into HFr2, HG into HG2. clear HF.
  psrr_branch_tok RUNF BR HS SHOK pi_Bspan;
    lazymatch type of HS with st_ok_pi _ _ ?E1 _ _ =>
      assert (H15' : ew E1 15 = w64 PI_WSMASK)
        by (rewrite ?ew_ewset_other by lia; rewrite (vrd_iEX_reg regs regs0 c P 15 15%bv eq_refl); exact H15);
      assert (H45' : U E1 (SOff 45 0) = c)
        by (rewrite U_SOff; rewrite ?ew_ewset_other by lia; rewrite vrd_iEX_c; unfold w64;
            rewrite unsigned_lit_small by lia; rewrite Z.add_0_r; apply zcanon_id; unfold M64; lia);
      rewrite branch_eq_U, (vrd_ws_bit E1 c H15' H45' ltac:(lia)) in Hc end.
  + (* the mask bit is clear: not white, row 78 *)
    apply negb_true_iff in Hc.
    paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM pi_Bspan (PI_X - A_prog_base);
      [apply (vrd_iawrB _ q); [rewrite ?ew_ewset_other by lia; exact E8X | lia | lia | lia
                               | left; vm_compute; reflexivity]|].
    rename HFr into HFr3, HG into HG3. clear HF.
    lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => set (MS := m) in * end.
    vrd_kq HFr1 E8X q K1. vrd_kq HFr2 E8X q K2. vrd_kq HFr3 E8X q K3. vrd_rk HS HRK RK.
    pmkst HS.
    lazymatch goal with |- SRr _ _ (mkCfg (YK11.mkst _ ?pc _ _) _) _ =>
      replace pc with (Z_to_bv 64 (BASE + (PI_X - A_prog_base))) by (vm_compute; reflexivity) end.
    apply SRr_ret. cbv beta.
    apply (vrd_iX1_inv R Hsub Htr Pm PLAW d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len
      p tb v HPRE Hd HD P); [ | lia | exact Hc | rewrite Hinv, Hrc; cbn [PjGrammar.skip]; rewrite Hc; reflexivity
      | exact HPM].
    apply (vrd_imid_step d o e q text len v regs0 ly Sa Hp W mem0 md0 P regs M mdc P _ _ _ HMID Hqv Rv);
      try (apply (vrd_carry _ _ MS (w_H W) vrd_rL regs _ HS RK); vm_compute; reflexivity);
      [intros x Hx; rewrite (K3 x Hx), (K2 x Hx); exact (K1 x Hx)
      | exact (mem_grows_trans _ _ _ (mem_grows_trans _ _ _ HG1 HG2) HG3) | | | lia | lia | exact HJ].
    * vrd_chunkH HS MS (w_H W) 2%nat 0 8%N (SOff 46 0) P VQ.
      specialize (VQ ltac:(cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite vrd_iEX_P; unfold w64;
        rewrite unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity) ltac:(lia) ltac:(lia)).
      cbn [base_val YP09.r_base] in VQ. rewrite ?ew_ewset_other in VQ by lia. rewrite E8X in VQ.
      unfold w64 in VQ. rewrite unsigned_lit_small, Z.add_0_r in VQ by lia. exact VQ.
    * vrd_chunkH HS MS (w_H W) 4%nat 16 4%N (SOff 11 1) (Z.of_nat d + 1) VQ.
      specialize (VQ ltac:(cbn [sv_denot]; rewrite ?ew_ewset_other by lia;
        rewrite (vrd_iEX_reg regs regs0 c P 11 11%bv eq_refl), H11; unfold w64; rewrite unsigned_lit_small by lia;
        reflexivity) ltac:(cbn; lia) ltac:(lia)).
      cbn [base_val YP09.r_base] in VQ. rewrite ?ew_ewset_other in VQ by lia. rewrite E8X in VQ.
      unfold w64 in VQ. rewrite unsigned_lit_small in VQ by lia. exact VQ.
  + (* white: rows 68..73, the store q->p := P + 1 and `bne a3, a2` *)
    apply negb_false_iff in Hc. rename Hc into Hws.
    paj_run_tok_x_inv RUNF HS HJ SHOK HPM pi_Bspan;
      [apply (vrd_iawrB _ q); [rewrite ?ew_ewset_other by lia; exact E8X | lia | lia | lia
                               | left; vm_compute; reflexivity]|].
    rename HFr into HFr3, HG into HG3. clear HF.
    psrr_branch_tok RUNF BR HS SHOK pi_Bspan;
      rewrite branch_ne_U, !U_SOff in Hc; rewrite ?ew_ewset_other in Hc by lia;
      rewrite vrd_iEX_P, (vrd_iEX_reg regs regs0 c P 12 12%bv eq_refl), H12 in Hc; unfold w64 in Hc;
      rewrite !unsigned_lit_small, Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia).
    * (* P + 1 <> end: the loop head again, at P + 1 *)
      apply negb_true_iff, Z.eqb_neq in Hc.
      paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM pi_Bspan (PI_SKIPHD - A_prog_base);
        [apply (vrd_iawrB _ q); [rewrite ?ew_ewset_other by lia; exact E8X | lia | lia | lia
                                 | left; vm_compute; reflexivity]|].
      rename HFr into HFr4, HG into HG4. clear HF.
      lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => set (MS := m) in * end.
      vrd_kq HFr1 E8X q K1. vrd_kq HFr2 E8X q K2. vrd_kq HFr3 E8X q K3. vrd_kq HFr4 E8X q K4. vrd_rk HS HRK RK.
      prreg HS (Z_to_bv 5 10) R10. prreg HS (Z_to_bv 5 13) R13.
      pmkst HS.
      lazymatch goal with |- SRr _ _ (mkCfg (YK11.mkst _ ?pc _ _) _) _ =>
        replace pc with (Z_to_bv 64 (BASE + (PI_SKIPHD - A_prog_base))) by (vm_compute; reflexivity) end.
      apply SRr_ret. cbv beta.
      apply (IH (P + 1)); [lia | | | | | | lia | rewrite Hinv, Hrc; cbn [PjGrammar.skip]; rewrite Hws; reflexivity
        | exact HPM].
      -- apply (vrd_imid_step d o e q text len v regs0 ly Sa Hp W mem0 md0 P regs M mdc (P + 1) _ _ _ HMID Hqv Rv);
           try (apply (vrd_carry _ _ MS (w_H W) vrd_rL regs _ HS RK); vm_compute; reflexivity);
           [intros x Hx; rewrite (K4 x Hx), (K3 x Hx), (K2 x Hx); exact (K1 x Hx)
           | exact (mem_grows_trans _ _ _ (mem_grows_trans _ _ _ (mem_grows_trans _ _ _ HG1 HG2) HG3) HG4)
           | | | lia | lia | exact HJ].
         ++ vrd_chunkH HS MS (w_H W) 2%nat 0 8%N (SOff 46 1) (P + 1) VQ.
            specialize (VQ ltac:(cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite vrd_iEX_P; unfold w64;
              rewrite unsigned_lit_small by lia; reflexivity) ltac:(lia) ltac:(lia)).
            cbn [base_val YP09.r_base] in VQ. rewrite ?ew_ewset_other in VQ by lia. rewrite E8X in VQ.
            unfold w64 in VQ. rewrite unsigned_lit_small, Z.add_0_r in VQ by lia. exact VQ.
         ++ vrd_chunkH HS MS (w_H W) 4%nat 16 4%N (SOff 11 1) (Z.of_nat d + 1) VQ.
            specialize (VQ ltac:(cbn [sv_denot]; rewrite ?ew_ewset_other by lia;
              rewrite (vrd_iEX_reg regs regs0 c P 11 11%bv eq_refl), H11; unfold w64;
              rewrite unsigned_lit_small by lia; reflexivity) ltac:(cbn; lia) ltac:(lia)).
            cbn [base_val YP09.r_base] in VQ. rewrite ?ew_ewset_other in VQ by lia. rewrite E8X in VQ.
            unfold w64 in VQ. rewrite unsigned_lit_small in VQ by lia. exact VQ.
      -- transitivity (getr (ms_regs MS) (Z_to_bv 5 10)); [reflexivity|]. rewrite R10.
         rewrite ?ew_ewset_other by lia. rewrite vrd_iEX_P. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
      -- transitivity (getr (ms_regs MS) (Z_to_bv 5 13)); [reflexivity|]. rewrite R13.
         rewrite ?ew_ewset_other by lia. rewrite vrd_iEX_P. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
      -- rewrite (vrd_carry _ _ MS (w_H W) vrd_rL regs 14%bv HS RK ltac:(vm_compute; reflexivity)). exact H14.
      -- rewrite (vrd_carry _ _ MS (w_H W) vrd_rL regs 15%bv HS RK ltac:(vm_compute; reflexivity)). exact H15.
    * (* P + 1 = end: row 74's jump to row 78 *)
      apply negb_false_iff, Z.eqb_eq in Hc.
      paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM pi_Bspan (PI_X - A_prog_base);
        [apply (vrd_iawrB _ q); [rewrite ?ew_ewset_other by lia; exact E8X | lia | lia | lia
                                 | left; vm_compute; reflexivity]|].
      rename HFr into HFr4, HG into HG4. clear HF.
      lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => set (MS := m) in * end.
      vrd_kq HFr1 E8X q K1. vrd_kq HFr2 E8X q K2. vrd_kq HFr3 E8X q K3. vrd_kq HFr4 E8X q K4. vrd_rk HS HRK RK.
      pmkst HS.
      lazymatch goal with |- SRr _ _ (mkCfg (YK11.mkst _ ?pc _ _) _) _ =>
        replace pc with (Z_to_bv 64 (BASE + (PI_X - A_prog_base))) by (vm_compute; reflexivity) end.
      apply SRr_ret. cbv beta.
      apply (vrd_iX0_inv R Hsub Htr Pm PLAW d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text
        len p tb v HPRE HD);
        [ | lia | rewrite Hinv, Hrc; cbn [PjGrammar.skip]; rewrite Hws, Hc, (vrd_rest_end tb text (text + len))
                    by lia; reflexivity | exact HPM].
      rewrite <- Hc.
      apply (vrd_imid_step d o e q text len v regs0 ly Sa Hp W mem0 md0 P regs M mdc (P + 1) _ _ _ HMID Hqv Rv);
        try (apply (vrd_carry _ _ MS (w_H W) vrd_rL regs _ HS RK); vm_compute; reflexivity);
        [intros x Hx; rewrite (K4 x Hx), (K3 x Hx), (K2 x Hx); exact (K1 x Hx)
        | exact (mem_grows_trans _ _ _ (mem_grows_trans _ _ _ (mem_grows_trans _ _ _ HG1 HG2) HG3) HG4)
        | | | lia | lia | exact HJ].
      -- vrd_chunkH HS MS (w_H W) 2%nat 0 8%N (SOff 46 1) (P + 1) VQ.
         specialize (VQ ltac:(cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite vrd_iEX_P; unfold w64;
           rewrite unsigned_lit_small by lia; reflexivity) ltac:(lia) ltac:(lia)).
         cbn [base_val YP09.r_base] in VQ. rewrite ?ew_ewset_other in VQ by lia. rewrite E8X in VQ.
         unfold w64 in VQ. rewrite unsigned_lit_small, Z.add_0_r in VQ by lia. exact VQ.
      -- vrd_chunkH HS MS (w_H W) 4%nat 16 4%N (SOff 11 1) (Z.of_nat d + 1) VQ.
         specialize (VQ ltac:(cbn [sv_denot]; rewrite ?ew_ewset_other by lia;
           rewrite (vrd_iEX_reg regs regs0 c P 11 11%bv eq_refl), H11; unfold w64;
           rewrite unsigned_lit_small by lia; reflexivity) ltac:(cbn; lia) ltac:(lia)).
         cbn [base_val YP09.r_base] in VQ. rewrite ?ew_ewset_other in VQ by lia. rewrite E8X in VQ.
         unfold w64 in VQ. rewrite unsigned_lit_small in VQ by lia. exact VQ.
Qed.

Lemma vrd_iloop : forall d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v,
  vrd_ipre d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v ->
  (d < PjGrammar.MAXD)%nat ->
  vrd_iDstep d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v ->
  forall n P regs M mdc, Z.to_nat (text + len - P) = n ->
  vrd_imid d o e q text len v regs0 ly Sa Hp W mem0 md0 P regs M mdc ->
  getr regs 10 = w64 P -> getr regs 13 = w64 P -> getr regs 14 = w64 32 -> getr regs 15 = w64 PI_WSMASK ->
  p + 1 <= P < text + len ->
  PjGrammar.skip (tl (rest_atR tb text p)) = PjGrammar.skip (rest_atR tb text P) ->
  SRr' segs YGcfRehidePost.RZ_cf W
    (mkCfg (YK11.mkst regs (Z_to_bv 64 (BASE + (PI_SKIPHD - A_prog_base))) M (YK11.seg_rom segs)) mdc)
    (vrd_iQall d o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v).
Proof.
intros d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v HPRE Hd HD n P regs M mdc
  Hn HMID H10 H13 H14 H15 HP Hinv.
eapply (SRrG_mono segs (wle' segs YGcfRehidePost.RZ_cf));
  [exact (vrd_iloop_inv (wle' segs YGcfRehidePost.RZ_cf) (wle_wle' segs YGcfRehidePost.RZ_cf)
     (wle'_trans segs YGcfRehidePost.RZ_cf) (fun _ => True) vrd_inv_true d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt
     fail ran most own e q text len p tb v HPRE Hd (vrd_iDstep_to_P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HD) n P
     regs M mdc Hn HMID H10 H13 H14 H15 HP Hinv I)|].
intros W' c' _ (H & _). exact H.
Qed.

(* ============================================================================================================== *)
(* B0. FROM THE ENTRY TO THE LOOP: rows 1..53 with the depth test passed; the end-of-text branch of row 53 goes to
   row 78 (vrd_iX0, the text ended after the opener) or, through rows 54..58, to the loop head (vrd_iloop at
   P = p + 1). The re-entry facts at both come from the row-53 symbolic state, which rows 54..58 change only in
   a0, a4 and a5.                                                                                                *)
(* ============================================================================================================== *)
Lemma vrd_U_shxm : forall E (n m : nat) k x, ew E n = w64 x -> ew E m = w64 SHADOW_OFF ->
  0 <= x < 2 ^ 64 -> 0 <= x + k <= 2 ^ 47 ->
  U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n k) (SLit 3)) (SOff m 0)) = shx (x + k).
Proof.
intros E n m k x Hn Hm Hx Hxk. unfold shx.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite U_SOff, U_SLit, U_SOff, Hn, Hm. unfold w64.
rewrite (unsigned_lit_small x) by lia. rewrite (unsigned_lit_small SHADOW_OFF) by (unfold SHADOW_OFF; lia).
rewrite (zcanon_id (x + k)) by (unfold M64; lia). rewrite (zcanon_id 3) by (unfold M64; lia).
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (H8 : 0 <= (x + k) / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
rewrite (zcanon_id ((x + k) / 8)) by (unfold M64; lia).
rewrite (zcanon_id (SHADOW_OFF + 0)) by (unfold M64, SHADOW_OFF; lia).
rewrite Z.add_0_r, Z.add_comm. apply zcanon_id. unfold M64, SHADOW_OFF. lia.
Qed.

(* the row-53 memory: the frame at the entry sp, the two GOT cells, the cursor's three fields, the node's type *)
Definition pi_rs53 : smem := Eval vm_compute in ss_mem (sh_ss (fst (pi_run ss_igo))).

Lemma vrd_imid_of53 : forall d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v
    E' (ss : sstate) ms mdc,
  vrd_ipre d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v ->
  (d < PjGrammar.MAXD)%nat -> p + 1 <= text + len ->
  st_ok_pi segs VAL E' ss (restrict (w_H W) ms) ->
  (forall n, (n < 36)%nat -> ew E' n = ew (vrd_iE regs0 p (text + len) (Z.of_nat d)) n) ->
  sr_get (ss_regs ss) 2%bv = SOff 2 (-144) -> sr_get (ss_regs ss) 3%bv = SOff 3 0 ->
  sr_get (ss_regs ss) 4%bv = SOff 4 0 -> sr_get (ss_regs ss) 8%bv = SOff 10 0 ->
  sr_get (ss_regs ss) 9%bv = SOff 10 16 -> sr_get (ss_regs ss) 11%bv = SOff 35 0 ->
  sr_get (ss_regs ss) 12%bv = SOff 34 0 -> sr_get (ss_regs ss) 18%bv = SLit 18446744073709551615 ->
  sr_get (ss_regs ss) 19%bv = SOff 12 0 -> sr_get (ss_regs ss) 20%bv = SOff 11 0 ->
  sr_get (ss_regs ss) 21%bv = SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 16) (SLit 3)) (SOff 32 0) ->
  sr_get (ss_regs ss) 22%bv = SOff 10 8 ->
  sr_get (ss_regs ss) 23%bv = SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 8) (SLit 3)) (SOff 32 0) ->
  sr_get (ss_regs ss) 26%bv = SOff 32 0 ->
  sr_get (ss_regs ss) 27%bv = SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 0) (SLit 3)) (SOff 32 0) ->
  ss_mem ss = pi_rs53 ->
  (forall x : word, ~ pi_wr (spZ regs0) q v (bv_unsigned x) ->
     mrestrict (w_H W) (ms_mem ms) x = mrestrict (w_H W) mem0 x) ->
  mem_grows (mrestrict (w_H W) mem0) (mrestrict (w_H W) (ms_mem ms)) ->
  ajournal_x (SK := SK) segs B prh_pst ARx (STK_parse_items d + e) (spZ regs0 + e) (rd_fp q v)
    ly Sa Hp W mem0 md0 [] ly Sa Hp W (ms_mem ms) mdc 0 ->
  vrd_imid d o e q text len v regs0 ly Sa Hp W mem0 md0 (p + 1) (ms_regs ms) (ms_mem ms) mdc.
Proof.
intros d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v E' ss ms mdc
  HPRE Hd Hp1 HS HE R2 R3 R4 R8 R9 R11 R12 R18 R19 R20 R21 R22 R23 R26 R27 Hmem KM KG HJ.
pose proof HPRE as ((HPRE0 & HROD & _) & HMN & HCTX & HUC & HCE & HCHI & HQCH & H10 & H11 & H12 & HRD & Hpe & Hop & HROOM & HPKS & HPKL & HFU
  & HFR & HCWR).
pose proof HRD as (Hfrm & Hmu & Hu1 & Hu2 & HIN & HWIN & Hspq & Hqe & HRAq & HSRC & HHOME & HMAX & HNODE & Hqv &
  Htv & Hvw & HLED & HdM & Hcnt).
pose proof HIN as (Vp & Ve & Vd & RWq & Hq8 & Ht0 & Ht62 & Htp & Hlen & Hgt & Hqt & Hd32).
pose proof HNODE as (Hv4096 & Hv8 & _ & _ & _ & HAMv & _).
pose proof HSRC as (Hbt & Ht4096 & Htceil & Htamr & HRAt & Hhull).
pose proof HPRE0 as (HAR & Hra & Hra4 & Hgp & Htp' & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof HWIN as (He0 & He16 & Hetop & Hepres).
pose proof (vrd_stk_ge d) as HSTK. pose proof H_img as (Himg1 & Himg2 & Himg3). unfold PI_FRAME in HSTK.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAMv.
rewrite Hlen in Htceil, Htamr.
destruct ss as [pc0 rr0 fr0 mm0 rv0 fc0]. cbn [ss_mem ss_regs] in *. subst mm0.
set (E := vrd_iE regs0 p (text + len) (Z.of_nat d)) in *.
assert (EX : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E' n = getr regs0 r)
  by (intros n r Hn Hr; rewrite (HE n ltac:(lia)); subst E; exact (vrd_iE_reg regs0 _ _ _ r n Hr)).
assert (E32 : ew E' 32 = w64 SHADOW_OFF)
  by (rewrite (HE 32%nat ltac:(lia)); subst E; unfold vrd_iE; rewrite Eimg_low by (unfold A_TEXT; lia);
      exact (ew_Ereg_extra regs0 _ 0)).
assert (E33 : ew E' 33 = w64 p)
  by (rewrite (HE 33%nat ltac:(lia)); subst E; unfold vrd_iE; rewrite Eimg_low by (unfold A_TEXT; lia);
      exact (ew_Ereg_extra regs0 _ 1)).
assert (E34 : ew E' 34 = w64 (text + len))
  by (rewrite (HE 34%nat ltac:(lia)); subst E; unfold vrd_iE; rewrite Eimg_low by (unfold A_TEXT; lia);
      exact (ew_Ereg_extra regs0 _ 2)).
assert (E35 : ew E' 35 = w64 (Z.of_nat d))
  by (rewrite (HE 35%nat ltac:(lia)); subst E; unfold vrd_iE; rewrite Eimg_low by (unfold A_TEXT; lia);
      exact (ew_Ereg_extra regs0 _ 3)).
assert (E10 : ew E' 10 = w64 q) by (rewrite (EX 10%nat 10%bv ltac:(lia) eq_refl); exact H10).
assert (E11 : ew E' 11 = w64 v) by (rewrite (EX 11%nat 11%bv ltac:(lia) eq_refl); exact H11).
assert (E12 : ew E' 12 = w64 (if o then 1 else 0)) by (rewrite (EX 12%nat 12%bv ltac:(lia) eq_refl); exact H12).
assert (U2 : bv_unsigned (ew E' 2) = spZ regs0) by (rewrite (EX 2%nat 2%bv ltac:(lia) eq_refl); reflexivity).
assert (GR : forall (r : bv 5) sv, sr_get rr0 r = sv -> getr (ms_regs ms) r = sv_denot E' sv)
  by (intros r sv Hr; rewrite <- Hr; exact (st_ok_pi_restrict_reg (w_H W) E' _ ms r HS)).
assert (GOFF : forall (r : bv 5) (n : nat) x k, sr_get rr0 r = SOff n k -> ew E' n = w64 x -> 0 <= x < 2 ^ 64 ->
    0 <= x + k < 2 ^ 64 -> getr (ms_regs ms) r = w64 (x + k)).
{ intros r n x k Hr Hn Hx Hxk. rewrite (GR r _ Hr). cbn [sv_denot]. rewrite Hn. unfold w64.
  rewrite unsigned_lit_small by lia. reflexivity. }
assert (GSHX : forall (r : bv 5) k, sr_get rr0 r = SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 k) (SLit 3)) (SOff 32 0) ->
    0 <= q + k <= 2 ^ 47 -> getr (ms_regs ms) r = w64 (shx (q + k))).
{ intros r k Hr Hk. rewrite (GR r _ Hr), denot_lit_U, (vrd_U_shxm E' 10 32 k q E10 E32 ltac:(lia) Hk). reflexivity. }
assert (Hd31 : Z.of_nat d <= 31) by (unfold PjGrammar.MAXD in Hd; lia).
assert (KW : forall a, writable_at segs (mrestrict (w_H W) mem0) a ->
  writable_at segs (mrestrict (w_H W) (ms_mem ms)) a)
  by (intros a; apply writable_at_grows; exact KG).
split; [|split; [|split; [|split; [|split]]]].
- (* vrd_iat *)
  split.
  { unfold spZ at 1. rewrite (GR 2%bv _ R2). cbn [sv_denot]. rewrite U2.
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
  split; [lia|]. split; [lia|]. split; [exact Hal16|].
  split; [pose proof (GOFF 8%bv 10%nat q 0 R8 E10 ltac:(lia) ltac:(lia)) as G; rewrite Z.add_0_r in G; exact G|].
  split; [pose proof (GOFF 26%bv 32%nat SHADOW_OFF 0 R26 E32 ltac:(unfold SHADOW_OFF; lia)
            ltac:(unfold SHADOW_OFF; lia)) as G; rewrite Z.add_0_r in G; exact G|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hq8|].
  split; [exact (GOFF 9%bv 10%nat q 16 R9 E10 ltac:(lia) ltac:(lia))|].
  split; [exact (GSHX 21%bv 16 R21 ltac:(lia))|].
  split; [exact (GOFF 22%bv 10%nat q 8 R22 E10 ltac:(lia) ltac:(lia))|].
  split; [exact (GSHX 23%bv 8 R23 ltac:(lia))|].
  split; [pose proof (GSHX 27%bv 0 R27 ltac:(lia)) as G; rewrite Z.add_0_r in G; exact G|].
  split; [pose proof (GOFF 11%bv 35%nat (Z.of_nat d) 0 R11 E35 ltac:(lia) ltac:(lia)) as G;
          rewrite Z.add_0_r in G; exact G|].
  split; [lia|].
  split; [rewrite (GR 19%bv _ R19); cbn [sv_denot]; rewrite E12; unfold w64;
          rewrite unsigned_lit_small by (destruct o; lia); rewrite Z.add_0_r; reflexivity|].
  split; [pose proof (GOFF 12%bv 34%nat (text + len) 0 R12 E34 ltac:(lia) ltac:(lia)) as G;
          rewrite Z.add_0_r in G; exact G|].
  split; [lia|]. split; [lia|]. split; [lia|].
  split.
  { intros j Hj. cbn [nth vi_extras].
    assert (FR : forall (r : bv 5) (n : nat) off, (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
        In (YP09.mkChunk off (CVal 8 (SOff n 0))) (YP09.r_chunks (nth 0 pi_rs53 (YP09.mkRegion None 0 0 0 0 []))) ->
        val_mem segs (mrestrict (w_H W) (ms_mem ms)) (spZ regs0 + off) 8 (bv_unsigned (getr regs0 r))).
    { intros r n off Hn Hr Hin.
      pose proof (vrd_chunk_val _ _ ms (w_H W) _ 0 off 8 (SOff n 0)
        (bv_unsigned (getr regs0 r)) HS eq_refl Hin) as VQ.
      specialize (VQ ltac:(cbn [sv_denot]; rewrite (EX n r Hn Hr), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
        ltac:(pose proof (bv_unsigned_in_range 64 (getr regs0 r)) as Hb; change (bv_modulus 64) with (2 ^ 64) in Hb;
              cbn; lia) ltac:(lia)).
      cbn [base_val YP09.r_base pi_rs53 nth] in VQ. rewrite U2 in VQ. exact VQ. }
    do 13 (destruct j as [|j];
      [cbn [nth Z.of_nat Pos.of_succ_nat];
       lazymatch goal with |- val_mem _ _ (spZ regs0 - 8 - 8 * ?k) _ (bv_unsigned (getr regs0 ?r)) =>
         let nk := eval vm_compute in (bv_unsigned r) in
         let off := eval vm_compute in (-8 - 8 * k) in
         replace (spZ regs0 - 8 - 8 * k) with (spZ regs0 + off) by lia;
         exact (FR r (Z.to_nat nk) off ltac:(cbn; lia) eq_refl ltac:(cbn; tauto)) end |]).
    lia. }
  split.
  { pose proof (vrd_chunk_val _ _ ms (w_H W) _ 3 0 8 (SOff 33 1) (p + 1) HS eq_refl
      ltac:(cbn; tauto)) as VQ.
    specialize (VQ ltac:(cbn [sv_denot]; rewrite E33; unfold w64; rewrite unsigned_lit_small by lia; reflexivity)
      ltac:(lia) ltac:(lia)).
    cbn [base_val YP09.r_base] in VQ. rewrite E10 in VQ. unfold w64 in VQ.
    rewrite unsigned_lit_small, Z.add_0_r in VQ by lia. exact VQ. }
  split.
  { pose proof (vrd_chunk_val _ _ ms (w_H W) _ 4 8 8 (SOff 34 0) (text + len) HS
      eq_refl ltac:(cbn; tauto)) as VQ.
    specialize (VQ ltac:(cbn [sv_denot]; rewrite E34; unfold w64; rewrite unsigned_lit_small by lia;
      rewrite Z.add_0_r; reflexivity) ltac:(lia) ltac:(lia)).
    cbn [base_val YP09.r_base] in VQ. rewrite E10 in VQ. unfold w64 in VQ.
    rewrite unsigned_lit_small in VQ by lia. exact VQ. }
  split.
  { pose proof (vrd_chunk_val _ _ ms (w_H W) _ 5 16 4 (SOff 35 1) (Z.of_nat d + 1) HS
      eq_refl ltac:(cbn; tauto)) as VQ.
    specialize (VQ ltac:(cbn [sv_denot]; rewrite E35; unfold w64; rewrite unsigned_lit_small by lia; reflexivity)
      ltac:(cbn; lia) ltac:(lia)).
    cbn [base_val YP09.r_base] in VQ. rewrite E10 in VQ. unfold w64 in VQ.
    rewrite unsigned_lit_small in VQ by lia. exact VQ. }
  split; [intros x Hx; apply KW; exact (RWq x Hx)|].
  eapply range_addressable_agree; [|exact HRAq]. intros x Hx.
  unfold aview, mbyte. rewrite KM; [reflexivity|]. unfold shadow_of_addr.
  assert (Hsx : 0 <= x / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). unfold pi_wr, PI_FRAME, SHADOW_OFF. lia.
- rewrite (GR 3%bv _ R3). cbn [sv_denot]. rewrite (EX 3%nat 3%bv ltac:(lia) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned.
  exact Hgp.
- rewrite (GR 4%bv _ R4). cbn [sv_denot]. rewrite (EX 4%nat 4%bv ltac:(lia) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned.
  exact Htp'.
- rewrite (GR 18%bv _ R18). cbn [sv_denot]. apply bv_eq. unfold w64. rewrite !Z_to_bv_unsigned. reflexivity.
- pose proof (GOFF 20%bv 11%nat v 0 R20 E11 ltac:(lia) ltac:(lia)) as G; rewrite Z.add_0_r in G; exact G.
- split.
  { pose proof (vrd_chunk_val _ _ ms (w_H W) _ 6 0 4
      (SAlu ALU_ADD (SAlu ALU_SLTU (SLit 0) (SOff 12 0)) (SLit 5)) (if o then 6 else 5) HS eq_refl
      ltac:(cbn; tauto)) as VQ.
    specialize (VQ ltac:(cbn [sv_denot]; rewrite E12; destruct o; vm_compute; reflexivity)
      ltac:(cbn; destruct o; lia) ltac:(lia)).
    cbn [base_val YP09.r_base] in VQ. rewrite E11 in VQ. unfold w64 in VQ.
    rewrite unsigned_lit_small, Z.add_0_r in VQ by lia. exact VQ. }
  split; [exact KM|]. split; [exact KG | exact HJ].
Qed.

(* the segment with the depth test passed, up to the grow step: rows 1..53, then row 78 (vrd_iX0) or the loop;
   generic in the world relation R of the grow step, as vrd_iX0_inv *)
Lemma vrd_ipro_go_inv : forall (R : world segs -> world segs -> Prop), (forall W1 W2, wle W1 W2 -> R W1 W2) ->
  (forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
  forall (Pm : (word -> option byte) -> Prop), srr_inv_laws segs Pm ->
  forall d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v,
  vrd_ipre d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v ->
  (d < PjGrammar.MAXD)%nat ->
  vrd_iDstep_PR R Pm d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v ->
  Pm mem ->
  SRrG segs R W (cfg_at segs (pa_sigma AS_parse_items) regs mem md)
    (fun W' c' => vrd_iQall d o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v W' c' /\
       Pm (ms_mem (cfg_ms c'))).
Proof.
intros R Hsub Htr Pm PLAW d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v HPRE Hd
  HD HPM.
apply (vrd_srrG_lift R Hsub Htr).
pose proof (vrd_iawr d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v HPRE) as HAWR.
destruct (vrd_ientry d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v HPRE)
  as [HS SHOK].
pose proof HPRE as ((HPRE0 & HROD & _) & HMN & HCTX & HUC & HCE & HCHI & HQCH & H10 & H11 & H12 & HRD & Hpe & Hop & HROOM & HPKS & HPKL & HFU
  & HFR & HCWR).
pose proof HRD as (Hfrm & Hmu & Hu1 & Hu2 & HIN & HWIN & Hspq & Hqe & HRAq & HSRC & HHOME & HMAX & HNODE & Hqv &
  Htv & Hvw & HLED & HdM & Hcnt).
pose proof HIN as (Vp & Ve & Vd & RWq & Hq8 & Ht0 & Ht62 & Htp & Hlen & Hgt & Hqt & Hd32).
pose proof HNODE as (Hv4096 & Hv8 & _ & _ & _ & HAMv & _).
pose proof HPRE0 as (HAR & Hra & Hra4 & Hgp & Htp' & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof HWIN as (He0 & He16 & Hetop & Hepres).
pose proof (vrd_stk_ge d) as HSTK. pose proof H_img as (Himg1 & Himg2 & Himg3). unfold PI_FRAME in HSTK.
pose proof HSRC as (Hbt & Ht4096 & Htceil & Htamr & HRAt & Hhull).
rewrite Hlen in Htceil, Htamr.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAMv.
pose proof (vrd_jinit (STK_parse_items d) e (rd_fp q v) ly Sa Hp W regs mem md ch HPRE0 HWIN) as HJ.
assert (U10 : bv_unsigned (getr regs 10) = q) by (rewrite H10; apply unsigned_lit_small; lia).
assert (U11 : bv_unsigned (getr regs 11) = v) by (rewrite H11; apply unsigned_lit_small; lia).
set (E := vrd_iE regs p (text + len) (Z.of_nat d)) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold vrd_iE; apply Eimg_env).
assert (E33 : ew E 33 = w64 p)
  by (subst E; unfold vrd_iE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = w64 (text + len))
  by (subst E; unfold vrd_iE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = w64 (Z.of_nat d))
  by (subst E; unfold vrd_iE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (Hrp : rest_atR tb text p = (if o then 123 else 91) :: rest_atR tb text (p + 1)).
{ rewrite (vrd_rest_cons tb text p) by lia. f_equal. apply nth_error_nth. exact Hop. }
pose (RUNF := paj_run_xf_inv (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B prh_pst ARx LAWS Pm PLAW).
pose (RUNTO := paj_run_to_xf_inv (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B prh_pst ARx LAWS Pm PLAW).
pose (BR := paj_branch (PI := PI_prog_A)).
unfold cfg_at. change (w64 (pa_sigma AS_parse_items)) with (Z_to_bv 64 (BASE + (PI_ENTRY - A_prog_base))).
(* ---- rows 1..39 and the depth test ---- *)
paj_run_tok_x_inv RUNF HS HJ SHOK HPM pi_Bspan; [exact HAWR|].
rename HFr into HFr1, HG into HG1. clear HF.
psrr_branch_tok RUNF BR HS SHOK pi_Bspan.
{ exfalso. cbn [sv_denot] in Hc. rewrite E35 in Hc. clear - Hc Hd. unfold PjGrammar.MAXD in Hd.
  do 32 (destruct d as [|d]; [vm_compute in Hc; discriminate Hc|]). lia. }
(* ---- rows 40..53 and the end-of-text test ---- *)
clear Hc.
paj_run_tok_x_inv RUNF HS HJ SHOK HPM pi_Bspan;
  [apply (vrd_iawr_sk d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v _ HPRE);
   vm_compute; reflexivity|].
rename HFr into HFr2, HG into HG2. clear HF.
psrr_branch_tok RUNF BR HS SHOK pi_Bspan;
  rewrite branch_geu_U, !U_SOff in Hc; rewrite ?ew_ewset_other in Hc by lia; rewrite E33, E34 in Hc; unfold w64 in Hc;
  rewrite !unsigned_lit_small, !zcanon_id in Hc by (unfold M64; lia).
- (* p + 1 = end: row 78 *)
  apply negb_true_iff, Z.ltb_ge in Hc. assert (Hpe1 : p + 1 = text + len) by lia.
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM pi_Bspan (PI_X - A_prog_base);
    [apply (vrd_iawr_sk d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v _ HPRE);
     vm_compute; reflexivity|].
  rename HFr into HFr3, HG into HG3. clear HF.
  lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => set (MS := m) in * end.
  pose proof (vrd_ikeep regs p (text + len) (Z.of_nat d) q v _ _ _ U10 U11 HFr1 eq_refl) as K1.
  pose proof (vrd_ikeep regs p (text + len) (Z.of_nat d) q v _ _ _ U10 U11 HFr2 ltac:(vm_compute; reflexivity)) as K2.
  pose proof (vrd_ikeep regs p (text + len) (Z.of_nat d) q v _ _ _ U10 U11 HFr3 ltac:(vm_compute; reflexivity)) as K3.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (YK11.mkst _ ?pc _ _) _) _ =>
    replace pc with (Z_to_bv 64 (BASE + (PI_X - A_prog_base))) by (vm_compute; reflexivity) end.
  apply SRr_ret. cbv beta.
  apply (vrd_iX0_inv R Hsub Htr Pm PLAW d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p
    tb v HPRE HD);
    [ | lia | rewrite Hrp; cbn [tl]; rewrite Hpe1, (vrd_rest_end tb text (text + len)) by lia; reflexivity
    | exact HPM].
  rewrite <- Hpe1.
  apply (vrd_imid_of53 d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v _ _ MS _ HPRE Hd
    ltac:(lia) HS);
    [ intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity
    | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | intros x Hx; rewrite (K3 x Hx), (K2 x Hx); exact (K1 x Hx)
    | exact (mem_grows_trans _ _ _ (mem_grows_trans _ _ _ HG1 HG2) HG3) | exact HJ ].
- (* p + 1 < end: rows 54..58, the loop head at p + 1 *)
  apply negb_false_iff, Z.ltb_lt in Hc.
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM pi_Bspan (PI_SKIPHD - A_prog_base);
    [apply (vrd_iawr_sk d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v _ HPRE);
     vm_compute; reflexivity|].
  rename HFr into HFr3, HG into HG3. clear HF.
  lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => set (MS := m) in * end.
  pose proof (vrd_ikeep regs p (text + len) (Z.of_nat d) q v _ _ _ U10 U11 HFr1 eq_refl) as K1.
  pose proof (vrd_ikeep regs p (text + len) (Z.of_nat d) q v _ _ _ U10 U11 HFr2 ltac:(vm_compute; reflexivity)) as K2.
  pose proof (vrd_ikeep regs p (text + len) (Z.of_nat d) q v _ _ _ U10 U11 HFr3 ltac:(vm_compute; reflexivity)) as K3.
  prreg HS (Z_to_bv 5 10) R10. prreg HS (Z_to_bv 5 13) R13. prreg HS (Z_to_bv 5 14) R14. prreg HS (Z_to_bv 5 15) R15.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (YK11.mkst _ ?pc _ _) _) _ =>
    replace pc with (Z_to_bv 64 (BASE + (PI_SKIPHD - A_prog_base))) by (vm_compute; reflexivity) end.
  apply SRr_ret. cbv beta.
  apply (vrd_iloop_inv R Hsub Htr Pm PLAW d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len
    p tb v HPRE Hd HD (Z.to_nat (text + len - (p + 1))) (p + 1)); [reflexivity | | | | | | lia | rewrite Hrp; reflexivity
    | exact HPM].
  + apply (vrd_imid_of53 d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v _ _ MS _ HPRE
      Hd ltac:(lia) HS);
      [ intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity
      | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | intros x Hx; rewrite (K3 x Hx), (K2 x Hx); exact (K1 x Hx)
      | exact (mem_grows_trans _ _ _ (mem_grows_trans _ _ _ HG1 HG2) HG3) | exact HJ ].
  + transitivity (getr (ms_regs MS) (Z_to_bv 5 10)); [reflexivity|]. rewrite R10.
    rewrite ?ew_ewset_other by lia. rewrite E33. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
  + transitivity (getr (ms_regs MS) (Z_to_bv 5 13)); [reflexivity|]. rewrite R13.
    rewrite ?ew_ewset_other by lia. rewrite E33. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
  + transitivity (getr (ms_regs MS) (Z_to_bv 5 14)); [reflexivity|]. rewrite R14. reflexivity.
  + transitivity (getr (ms_regs MS) (Z_to_bv 5 15)); [reflexivity|]. rewrite R15. reflexivity.
Qed.

Lemma vrd_ipro_go : forall d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v,
  vrd_ipre d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v ->
  (d < PjGrammar.MAXD)%nat ->
  vrd_iDstep d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v ->
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (pa_sigma AS_parse_items) regs mem md)
    (vrd_iQall d o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v).
Proof.
intros d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v HPRE Hd HD.
eapply (SRrG_mono segs (wle' segs YGcfRehidePost.RZ_cf));
  [exact (vrd_ipro_go_inv (wle' segs YGcfRehidePost.RZ_cf) (wle_wle' segs YGcfRehidePost.RZ_cf)
     (wle'_trans segs YGcfRehidePost.RZ_cf) (fun _ => True) vrd_inv_true d CTX o ly Sa Hp W regs mem md ch Lam peak cnt
     fail ran most own e q text len p tb v HPRE Hd (vrd_iDstep_to_P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HD)
     I)|].
intros W' c' _ (H & _). exact H.
Qed.

(* ============================================================================================================== *)
(* F (the empty container). The empty case never reaches the grow step: its premise (the byte after the white
   space is no closer) contradicts the empty premise, so the grow step holds outright there - at wle, so the empty
   container keeps its SRr statement (vrd_ipro_go_inv at R := wle).                                              *)
(* ============================================================================================================== *)
Lemma vrd_iempty_ok_inv : forall (Pm : (word -> option byte) -> Prop), srr_inv_laws segs Pm ->
  forall d CTX, vrd_iempty_stmt_P Pm d CTX.
Proof.
intros Pm PLAW d CTX ly Sa Hp W regs mem md ch e q text len p tb v o Lam peak cnt fail ran most own r0 HPRE Hd Hsk HPM.
eapply SRr_mono.
- apply (vrd_ipro_go_inv (@wle segs) (fun _ _ H => H) (wle_trans segs) Pm PLAW d CTX o ly Sa Hp W regs mem md ch Lam peak
    cnt fail ran most own e q text len p tb v HPRE Hd); [|exact HPM].
  intros P E ss ms mdc _ _ _ _ _ _ _ _ Hnc _. exfalso. exact (Hnc r0 Hsk).
- intros W' c' _ ([(ch2 & P & _ & _ & _ & Hnc) | Hpost] & Hpm); [exfalso; exact (Hnc r0 Hsk) | exact (conj Hpost Hpm)].
Qed.

Lemma vrd_iempty_ok : forall d CTX, vrd_iempty_stmt d CTX.
Proof.
intros d CTX ly Sa Hp W regs mem md ch e q text len p tb v o Lam peak cnt fail ran most own r0 HPRE Hd Hsk.
eapply SRr_mono; [exact (vrd_iempty_ok_inv (fun _ => True) vrd_inv_true d CTX ly Sa Hp W regs mem md ch e q text len p tb
  v o Lam peak cnt fail ran most own r0 HPRE Hd Hsk I)|].
intros W' c' _ (H & _). exact H.
Qed.

Lemma vrd_ipre_d32 : forall d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v,
  vrd_ipre d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v -> Z.of_nat d <= 32.
Proof.
intros d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v HPRE.
pose proof (vrd_ipre_prj d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v HPRE)
  as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hd32 & _).
exact Hd32.
Qed.

(* F (the segment). The depth arm when d = MAXD (pj_in_okR bounds d by 32; at wle, lifted to SRr'), else
   vrd_ipro_go_inv at wle'; what is left is the grow step D, the one premise below, which a later lemma discharges. *)
Lemma vrd_ipro_ok_of_D_inv : forall (Pm : (word -> option byte) -> Prop), srr_inv_laws segs Pm -> forall d CTX,
  (forall ly Sa Hp W regs mem md ch e q text len p tb v o Lam peak cnt fail ran most own,
     vrd_ipre d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v ->
     (d < PjGrammar.MAXD)%nat ->
     vrd_iDstep_P Pm d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v) ->
  vrd_ipro_stmt_P Pm d CTX.
Proof.
intros Pm PLAW d CTX HDall ly Sa Hp W regs mem md ch e q text len p tb v o Lam peak cnt fail ran most own HPRE HPM.
destruct (Nat.lt_ge_cases d PjGrammar.MAXD) as [Hd | Hd].
- eapply (SRrG_mono segs (wle' segs YGcfRehidePost.RZ_cf)).
  + exact (vrd_ipro_go_inv (wle' segs YGcfRehidePost.RZ_cf) (wle_wle' segs YGcfRehidePost.RZ_cf)
      (wle'_trans segs YGcfRehidePost.RZ_cf) Pm PLAW d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e
      q text len p tb v HPRE Hd (HDall ly Sa Hp W regs mem md ch e q text len p tb v o Lam peak cnt fail ran most own HPRE
      Hd) HPM).
  + intros W' c' _ ([(ch2 & P & HW & Hc & HE & _) | Hpost] & Hpm); split; try exact Hpm;
      [left; exists ch2, P; tauto | right; exact Hpost].
- assert (Hdm : d = PjGrammar.MAXD).
  { pose proof (vrd_ipre_d32 d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v HPRE) as Hd32.
    unfold PjGrammar.MAXD in *. lia. }
  apply (SRr_SRr' segs YGcfRehidePost.RZ_cf).
  eapply SRr_mono;
    [exact (vrd_ipro_depth_inv Pm PLAW d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v
              HPRE Hdm HPM)
    | intros W' c' _ (Hpost & Hpm); split; [right; exact Hpost | exact Hpm]].
Qed.

Lemma vrd_ipro_ok_of_D : forall d CTX,
  (forall ly Sa Hp W regs mem md ch e q text len p tb v o Lam peak cnt fail ran most own,
     vrd_ipre d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v ->
     (d < PjGrammar.MAXD)%nat ->
     vrd_iDstep d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v) ->
  vrd_ipro_stmt d CTX.
Proof.
intros d CTX HDall ly Sa Hp W regs mem md ch e q text len p tb v o Lam peak cnt fail ran most own HPRE.
eapply (SRrG_mono segs (wle' segs YGcfRehidePost.RZ_cf)).
- apply (vrd_ipro_ok_of_D_inv (fun _ => True) vrd_inv_true d CTX); [|exact HPRE | exact I].
  intros ly' Sa' Hp' W' regs' mem' md' ch' e' q' text' len' p' tb' v' o' Lam' peak' cnt' fail' ran' most' own' H1 H2.
  exact (vrd_iDstep_to_P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (HDall ly' Sa' Hp' W' regs' mem' md' ch' e' q'
    text' len' p' tb' v' o' Lam' peak' cnt' fail' ran' most' own' H1 H2)).
- intros W' c' _ (H & _). exact H.
Qed.

(* ============================================================================================================== *)
(* D1. THE FIRST GROW'S PREMISES at the `jal grow` of row 91 (everything tgrow_specX asks but the callee's
   afn_pre_x and the chain from s0, which vrd_call_W supplies), and the head of the granted trace it charges.       *)
(* ============================================================================================================== *)
(* the trace of a monadic bind, when its first part succeeds *)
Lemma vrd_jbind_tr : forall A Bt (m : PjGrammar.M A) (k : A -> PjGrammar.M Bt) ok a t ok1,
  m ok = (Some a, t, ok1) -> snd (fst (PjGrammar.jbind m k ok)) = t ++ snd (fst (k a ok1)).
Proof.
intros A Bt m k ok a t ok1 H. unfold PjGrammar.jbind. rewrite H. destruct (k a ok1) as [[r t'] ok2]. reflexivity.
Qed.

(* the granted run of a container that is neither too deep nor empty starts with the first grow's reallocs *)
Lemma vrd_gtrace_grow : forall d o x, (d < PjGrammar.MAXD)%nat ->
  (forall r, PjGrammar.skip (tl x) <> PjGrammar.closer o :: r) ->
  exists t, prhPi_gtrace d o x =
    PjGrammar.EGrow 0 448 :: (if o then [PjGrammar.EGrow 0 64] else []) ++ t.
Proof.
intros d o x Hd Hnc. unfold prhPi_gtrace, PjGrammar.jr_items, PjGrammar.jr_cont.
replace (Nat.ltb PjGrammar.MAXD (S d)) with false by (symmetry; apply Nat.ltb_ge; lia).
cbv zeta.
assert (Hjrl : forall y, exists t, snd (fst (PjGrammar.jrl prh_jr_strtod (2 * length x + 2) (S d) o 0 0 [] y [])) =
    PjGrammar.EGrow 0 448 :: (if o then [PjGrammar.EGrow 0 64] else []) ++ t).
{ intros y. replace (2 * length x + 2)%nat with (S (2 * length x + 1)) by lia. cbn [PjGrammar.jrl].
  destruct o.
  - rewrite (vrd_jbind_tr _ _ (PjGrammar.grow true 0 0) _ [] 8%nat [PjGrammar.EGrow 0 448; PjGrammar.EGrow 0 64] [])
      by (vm_compute; reflexivity).
    eexists. reflexivity.
  - rewrite (vrd_jbind_tr _ _ (PjGrammar.grow false 0 0) _ [] 8%nat [PjGrammar.EGrow 0 448] [])
      by (vm_compute; reflexivity).
    eexists. reflexivity. }
cbn beta iota.
destruct (PjGrammar.skip (tl x)) as [|c r] eqn:Hy; [exact (Hjrl [])|].
destruct (Z.eqb_spec c (PjGrammar.closer o)) as [Hc|Hc].
- exfalso. apply (Hnc r). first [rewrite Hy, Hc; reflexivity | rewrite Hc; reflexivity].
- exact (Hjrl (c :: r)).
Qed.

Lemma vrd_hpeak_nonneg : forall t, 0 <= hpeakR t.
Proof. intros [|e t]; cbn [hpeakR]; lia. Qed.

(* the call's granted events start with the first grow's, as grow's text states them (prhPg_evs with cf_head; the
   reader's rd_hevs with PresetReqAt.HEAD: HI_head is the bridge) *)
Lemma vrd_gevs_prefix : forall d o x, (d < PjGrammar.MAXD)%nat ->
  (forall r, PjGrammar.skip (tl x) <> PjGrammar.closer o :: r) ->
  exists t, PresetReqAt.rd_hevs (prhPi_gtrace d o x) = prhPg_evs ((if o then 6 else 5) =? 6) 0 0 [] ++ t.
Proof.
intros d o x Hd Hnc. destruct (vrd_gtrace_grow d o x Hd Hnc) as (t & Ht).
exists (PresetReqAt.rd_hevs t). rewrite Ht. unfold prhPg_evs, prhPg_ev. rewrite HI_head.
destruct o; reflexivity.
Qed.

(* THE HULL across the first grow: grow's budget is the prefix of the call's (PresetHullBudget.hull_budget_infix at an
   empty used list), and grow's use is a use of the call's granted events (PresetHullBudget.hull_used_infix) *)
Lemma vrd_hull_grow_budget : forall d o x (S : astate), (d < PjGrammar.MAXD)%nat ->
  (forall r, PjGrammar.skip (tl x) <> PjGrammar.closer o :: r) ->
  PresetHullBudget.hull_budget S (PresetReqAt.rd_hevs (prhPi_gtrace d o x)) ->
  PresetHullBudget.hull_budget S (prhPg_evs ((if o then 6 else 5) =? 6) 0 0 []).
Proof.
intros d o x S Hd Hnc HB. destruct (vrd_gevs_prefix d o x Hd Hnc) as (t & Ht). rewrite Ht in HB.
exact (PresetHullBudget.hull_budget_infix S S [] (prhPg_evs ((if o then 6 else 5) =? 6) 0 0 []) t HB
  (PresetHullBudget.hull_used_refl S [])).
Qed.

Lemma vrd_hull_gtrace : forall d o x (S S' : astate), (d < PjGrammar.MAXD)%nat ->
  (forall r, PjGrammar.skip (tl x) <> PjGrammar.closer o :: r) ->
  PresetHullBudget.hull_used S S' (prhPg_evs ((if o then 6 else 5) =? 6) 0 0 []) ->
  PresetHullBudget.hull_used S S' (PresetReqAt.rd_hevs (prhPi_gtrace d o x)).
Proof.
intros d o x S S' Hd Hnc HU. destruct (vrd_gevs_prefix d o x Hd Hnc) as (t & Ht). rewrite Ht.
exact (PresetHullBudget.hull_used_infix S S' [] (prhPg_evs ((if o then 6 else 5) =? 6) 0 0 []) t HU).
Qed.

(* a count peak over a prefix of the events is at most the peak over all of them (PresetRun.pkR_app) *)
Lemma vrd_pk_prefix : forall f s a b, (PresetRun.pkR f s a <= PresetRun.pkR f s (a ++ b))%nat.
Proof. intros f s a b. rewrite PresetRun.pkR_app. lia. Qed.

(* ---- THE FIRST GROW'S ARMS AGAINST THE CALL'S ALL-GRANTED TRACE (the kit's cut: PRH_FnParse.v f0d92dcec7e9 /
   PRH_FnReader.v f1ae32e3b2cd): the arm's
   event list in grow's form is the arm's trace's in the reader's form (HI_head), the granted trace begins with the
   granted grow, and the refusal peak and the OUTCOME's window read its first one or two calls ---- *)

(* each arm's events, grow's form = the reader's form of the arm's trace *)
Lemma vrd_gevs_arm : forall (o : bool),
  prhPg_evs ((if o then 6 else 5) =? 6) 0 0 [false] = PresetReqAt.rd_hevs [PjGrammar.EFail 448] /\
  prhPg_evs ((if o then 6 else 5) =? 6) 0 0 [true] =
    PresetReqAt.rd_hevs ([PjGrammar.EGrow 0 448] ++ (if o then [PjGrammar.EGrow 0 64] else [])) /\
  prhPg_evs (6 =? 6) 0 0 [true; false] = PresetReqAt.rd_hevs [PjGrammar.EGrow 0 448; PjGrammar.EFail 64] /\
  prhPg_evs (6 =? 6) 0 0 [true; true] = PresetReqAt.rd_hevs [PjGrammar.EGrow 0 448; PjGrammar.EGrow 0 64].
Proof.
intros o. unfold prhPg_evs, prhPg_ev. rewrite HI_head. destruct o; repeat split; reflexivity.
Qed.

(* the granted trace's held bytes after its first calls, and its call count *)
Lemma vrd_gt_helds : forall d o x, (d < PjGrammar.MAXD)%nat ->
  (forall r, PjGrammar.skip (tl x) <> PjGrammar.closer o :: r) ->
  exists hs, prh_ev_helds (prhPi_gtrace d o x) = 448 :: (if o then [512] else []) ++ hs.
Proof.
intros d o x Hd Hnc. destruct (vrd_gtrace_grow d o x Hd Hnc) as (t & Ht). rewrite Ht.
destruct o; eexists; reflexivity.
Qed.

Lemma vrd_gt_calls : forall d o x, (d < PjGrammar.MAXD)%nat ->
  (forall r, PjGrammar.skip (tl x) <> PjGrammar.closer o :: r) ->
  ((if o then 2 else 1) <= PjGrammar.calls (prhPi_gtrace d o x))%nat.
Proof.
intros d o x Hd Hnc. destruct (vrd_gtrace_grow d o x Hd Hnc) as (t & Ht). rewrite Ht.
destruct o; cbn [PjGrammar.calls PjGrammar.is_call app]; lia.
Qed.

(* THE OUTCOME's exclusion from grow's REFUSED arm: a run whose next events are the call's granted ones begins with
   grow's granted events, every allocation among them a consumer event - which grow's arm excludes *)
Lemma vrd_excl_grow : forall d o x (S : astate), (d < PjGrammar.MAXD)%nat ->
  (forall r, PjGrammar.skip (tl x) <> PjGrammar.closer o :: r) ->
  (forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x0 os i H0 hist S ->
     PRH_Base.prh_run_at sm x0 os i (prhPg_evs ((if o then 6 else 5) =? 6) 0 0 []) ->
     PRH_Base.prh_cons_from sm x0 os i (length (prhPg_evs ((if o then 6 else 5) =? 6) 0 0 [])) -> False) ->
  forall (cnt fail : Z) (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat))
    (i : nat) (H0 : list Z) (hist : list YG00.chunk),
  PresetRoomPos.iface_room_pos sm x0 os i H0 hist S ->
  PRH_Base.prh_run_at sm x0 os i (PresetReqAt.rd_hevs (prhPi_gtrace d o x)) ->
  PRH_Base.prh_cons_from sm x0 os i (length (PresetReqAt.rd_hevs (prhPi_gtrace d o x))) ->
  (fail < cnt \/ cnt + Z.of_nat (PjGrammar.calls (prhPi_gtrace d o x)) <= fail) -> False.
Proof.
intros d o x S Hd Hnc HX cnt fail sm x0 os i H0 hist HP HR HC _.
destruct (vrd_gevs_prefix d o x Hd Hnc) as (t & Ht). rewrite Ht in HR, HC.
apply PRH_Base.prh_run_at_app_iff in HR as [HR1 _].
rewrite length_app in HC. apply PRH_Base.prh_cons_from_app_iff in HC as [HC1 _].
exact (HX sm x0 os i H0 hist HP HR1 HC1).
Qed.

(* ... and from grow's CHOSEN failure at its k-th call (k = 0 the kids realloc, k = 1 an object's keys realloc): the
   window premise of the OUTCOME says no failure is chosen among the granted trace's calls, which include it *)
Lemma vrd_excl_fail : forall d o x (S : astate) cnt fail (k : nat), (d < PjGrammar.MAXD)%nat ->
  (forall r, PjGrammar.skip (tl x) <> PjGrammar.closer o :: r) ->
  fail = cnt + Z.of_nat k -> (k < (if o then 2 else 1))%nat ->
  forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
    (H0 : list Z) (hist : list YG00.chunk),
  PresetRoomPos.iface_room_pos sm x0 os i H0 hist S ->
  PRH_Base.prh_run_at sm x0 os i (PresetReqAt.rd_hevs (prhPi_gtrace d o x)) ->
  PRH_Base.prh_cons_from sm x0 os i (length (PresetReqAt.rd_hevs (prhPi_gtrace d o x))) ->
  (fail < cnt \/ cnt + Z.of_nat (PjGrammar.calls (prhPi_gtrace d o x)) <= fail) -> False.
Proof.
intros d o x S cnt fail k Hd Hnc Hf Hk sm x0 os i H0 hist _ _ _ HW.
pose proof (vrd_gt_calls d o x Hd Hnc) as Hc. destruct o; lia.
Qed.

(* ---- THE OUTCOME OF AN INJECTED READING at the first grow's refused arms (the post's conjunct, PRH_FnParse.tpiP_Q):
   the call's events under any grant list begin with the first grow's events under that list (vrd_inj_first); with
   the chosen failure past grow's window, grow's events under the model's list are its all-granted ones
   (vrd_pg_okk0). The chosen-failure arms meet the clause by their own counters (vrd_inj_kids_fail /
   vrd_inj_keys_fail); the refused arms meet no such run (vrd_inj_kids_ref / vrd_inj_keys_ref) ---- *)
Lemma vrd_inj_first : forall d o x okt, (d < PjGrammar.MAXD)%nat ->
  (forall r, PjGrammar.skip (tl x) <> PjGrammar.closer o :: r) ->
  exists t, PresetReqAt.rd_hevs (snd (fst (jr_items prh_jr_strtod d o x okt))) =
    prhPg_evs ((if o then 6 else 5) =? 6) 0 0 okt ++ t.
Proof.
intros d o x okt Hd Hnc. rewrite (vrd_items_go d o x okt Hd Hnc), vrd_jrl_unfold.
lazymatch goal with |- context [PjGrammar.jbind ?m ?k okt] =>
  destruct (vrd_jbind_prefix _ _ m k okt) as (t2 & Et) end.
rewrite Et, PresetHullBudget.hull_rd_app. exists (PresetReqAt.rd_hevs t2).
rewrite (prhPg_evs_model ((if o then 6 else 5) =? 6) 0 0 okt ltac:(lia) ltac:(lia) HI_head).
destruct o; reflexivity.
Qed.

Lemma vrd_pg_okk0 : forall (o : bool) j, ((if o then 2 else 1) <= j)%nat ->
  prhPg_evs ((if o then 6 else 5) =? 6) 0 0 (PresetReqAt.okk j) = prhPg_evs ((if o then 6 else 5) =? 6) 0 0 [].
Proof.
intros o j Hj. destruct j as [|[|j]].
- destruct o; cbv iota beta in Hj; lia.
- destruct o; [cbv iota beta in Hj; lia | reflexivity].
- destruct o; reflexivity.
Qed.

(* grow's arm 2: the refused kids realloc is the chosen failure (cnt = fail) *)
Lemma vrd_inj_kids_fail : forall d o x (S : astate) cnt fail, cnt = fail ->
  forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
    (H0 : list Z) (hist : list YG00.chunk),
  PresetRoomPos.iface_room_pos sm x0 os i H0 hist S ->
  PRH_Base.prh_run_at sm x0 os i (PresetReqAt.rd_hevs (snd (fst (jr_items prh_jr_strtod d o x
    (PresetReqAt.okk (Z.to_nat (fail - cnt))))))) ->
  PRH_Base.prh_cons_from sm x0 os i (length (PresetReqAt.rd_hevs (snd (fst (jr_items prh_jr_strtod d o x
    (PresetReqAt.okk (Z.to_nat (fail - cnt)))))))) ->
  cnt <= fail < cnt + Z.of_nat (PjGrammar.calls (prhPi_gtrace d o x)) ->
  PRH_Base.prh_granted [false] cnt fail (PjGrammar.calls [PjGrammar.EFail 448]).
Proof.
intros d o x S cnt fail Hcf sm x0 os i H0 hist _ _ _ _ k Hk _.
cbn [PjGrammar.calls PjGrammar.is_call] in Hk. assert (Ek : k = 0%nat) by lia. subst k. lia.
Qed.

(* grow's arm 5: the kids realloc granted, the refused keys realloc is the chosen failure (cnt + 1 = fail) *)
Lemma vrd_inj_keys_fail : forall d x (S : astate) cnt fail, cnt + 1 = fail ->
  forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
    (H0 : list Z) (hist : list YG00.chunk),
  PresetRoomPos.iface_room_pos sm x0 os i H0 hist S ->
  PRH_Base.prh_run_at sm x0 os i (PresetReqAt.rd_hevs (snd (fst (jr_items prh_jr_strtod d true x
    (PresetReqAt.okk (Z.to_nat (fail - cnt))))))) ->
  PRH_Base.prh_cons_from sm x0 os i (length (PresetReqAt.rd_hevs (snd (fst (jr_items prh_jr_strtod d true x
    (PresetReqAt.okk (Z.to_nat (fail - cnt)))))))) ->
  cnt <= fail < cnt + Z.of_nat (PjGrammar.calls (prhPi_gtrace d true x)) ->
  PRH_Base.prh_granted [true; false] cnt fail (PjGrammar.calls [PjGrammar.EGrow 0 448; PjGrammar.EFail 64]).
Proof.
intros d x S cnt fail Hcf sm x0 os i H0 hist _ _ _ _ k Hk Hn.
cbn [PjGrammar.calls PjGrammar.is_call] in Hk.
destruct k as [|[|k]]; [cbn in Hn; discriminate Hn | lia | lia].
Qed.

(* grow's arm 3: the kids realloc refused, not chosen (cnt <> fail). Inside grow's window the arm's own injected
   exclusion meets the run's first events; past it they are grow's all-granted events, which the arm's OUTCOME
   exclusion meets *)
Lemma vrd_inj_kids_ref : forall d o x (S : astate) cnt fail, (d < PjGrammar.MAXD)%nat ->
  (forall r, PjGrammar.skip (tl x) <> PjGrammar.closer o :: r) ->
  (forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x0 os i H0 hist S ->
     PRH_Base.prh_run_at sm x0 os i (prhPg_evs ((if o then 6 else 5) =? 6) 0 0 []) ->
     PRH_Base.prh_cons_from sm x0 os i (length (prhPg_evs ((if o then 6 else 5) =? 6) 0 0 [])) -> False) ->
  (forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x0 os i H0 hist S ->
     PRH_Base.prh_run_at sm x0 os i (prhPg_evs ((if o then 6 else 5) =? 6) 0 0 (PresetReqAt.okk (Z.to_nat (fail - cnt)))) ->
     PRH_Base.prh_cons_from sm x0 os i
       (length (prhPg_evs ((if o then 6 else 5) =? 6) 0 0 (PresetReqAt.okk (Z.to_nat (fail - cnt))))) ->
     cnt <= fail < cnt + Z.of_nat (PjGrammar.calls (PRH_Charge.prhPg_gtrace ((if o then 6 else 5) =? 6) 0 0)) ->
     False) ->
  forall (ok : list bool) (tr : list PjGrammar.ev)
    (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
    (H0 : list Z) (hist : list YG00.chunk),
  PresetRoomPos.iface_room_pos sm x0 os i H0 hist S ->
  PRH_Base.prh_run_at sm x0 os i (PresetReqAt.rd_hevs (snd (fst (jr_items prh_jr_strtod d o x
    (PresetReqAt.okk (Z.to_nat (fail - cnt))))))) ->
  PRH_Base.prh_cons_from sm x0 os i (length (PresetReqAt.rd_hevs (snd (fst (jr_items prh_jr_strtod d o x
    (PresetReqAt.okk (Z.to_nat (fail - cnt)))))))) ->
  cnt <= fail < cnt + Z.of_nat (PjGrammar.calls (prhPi_gtrace d o x)) ->
  PRH_Base.prh_granted ok cnt fail (PjGrammar.calls tr).
Proof.
intros d o x S cnt fail Hd Hnc HX HJ ok tr sm x0 os i H0 hist HP HR HC (Hle & _). exfalso.
destruct (vrd_inj_first d o x (PresetReqAt.okk (Z.to_nat (fail - cnt))) Hd Hnc) as (t & Et).
rewrite Et in HR, HC. rewrite length_app in HC.
apply PRH_Base.prh_run_at_app_iff in HR as [HR1 _].
apply PRH_Base.prh_cons_from_app_iff in HC as [HC1 _].
destruct (Z_lt_le_dec fail
  (cnt + Z.of_nat (PjGrammar.calls (PRH_Charge.prhPg_gtrace ((if o then 6 else 5) =? 6) 0 0)))) as [HwIn | HwOut].
- exact (HJ sm x0 os i H0 hist HP HR1 HC1 (conj Hle HwIn)).
- assert (Hgc : PjGrammar.calls (PRH_Charge.prhPg_gtrace ((if o then 6 else 5) =? 6) 0 0) = (if o then 2 else 1)%nat)
    by (destruct o; reflexivity).
  rewrite Hgc in HwOut.
  assert (Hj : ((if o then 2 else 1) <= Z.to_nat (fail - cnt))%nat) by (destruct o; cbv iota beta in HwOut |- *; lia).
  rewrite (vrd_pg_okk0 o _ Hj) in HR1, HC1. exact (HX sm x0 os i H0 hist HP HR1 HC1).
Qed.

(* grow's arm 6: the kids realloc granted, the keys realloc refused, neither chosen (cnt <> fail, cnt + 1 <> fail): a
   chosen failure in the call's window is past grow's two calls, so the run's first events are grow's all-granted
   events, which the arm's OUTCOME exclusion meets *)
Lemma vrd_inj_keys_ref : forall d x (S : astate) cnt fail, (d < PjGrammar.MAXD)%nat ->
  (forall r, PjGrammar.skip (tl x) <> PjGrammar.closer true :: r) ->
  cnt <> fail -> cnt + 1 <> fail ->
  (forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x0 os i H0 hist S ->
     PRH_Base.prh_run_at sm x0 os i (prhPg_evs (6 =? 6) 0 0 []) ->
     PRH_Base.prh_cons_from sm x0 os i (length (prhPg_evs (6 =? 6) 0 0 [])) -> False) ->
  forall (ok : list bool) (tr : list PjGrammar.ev)
    (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
    (H0 : list Z) (hist : list YG00.chunk),
  PresetRoomPos.iface_room_pos sm x0 os i H0 hist S ->
  PRH_Base.prh_run_at sm x0 os i (PresetReqAt.rd_hevs (snd (fst (jr_items prh_jr_strtod d true x
    (PresetReqAt.okk (Z.to_nat (fail - cnt))))))) ->
  PRH_Base.prh_cons_from sm x0 os i (length (PresetReqAt.rd_hevs (snd (fst (jr_items prh_jr_strtod d true x
    (PresetReqAt.okk (Z.to_nat (fail - cnt)))))))) ->
  cnt <= fail < cnt + Z.of_nat (PjGrammar.calls (prhPi_gtrace d true x)) ->
  PRH_Base.prh_granted ok cnt fail (PjGrammar.calls tr).
Proof.
intros d x S cnt fail Hd Hnc Hc0 Hc1 HX ok tr sm x0 os i H0 hist HP HR HC (Hle & _). exfalso.
destruct (vrd_inj_first d true x (PresetReqAt.okk (Z.to_nat (fail - cnt))) Hd Hnc) as (t & Et).
rewrite Et in HR, HC. rewrite length_app in HC.
apply PRH_Base.prh_run_at_app_iff in HR as [HR1 _].
apply PRH_Base.prh_cons_from_app_iff in HC as [HC1 _].
assert (Hj : ((if true then 2 else 1) <= Z.to_nat (fail - cnt))%nat) by (cbv iota beta; lia).
rewrite (vrd_pg_okk0 true _ Hj) in HR1, HC1. exact (HX sm x0 os i H0 hist HP HR1 HC1).
Qed.

(* the refusal flag and peak of one or two calls, read off their definitions *)
Lemma vrd_refused_t : forall ok cnt fail i, nth i ok true = true -> prh_refused ok cnt fail i = false.
Proof. intros ok cnt fail i H. unfold prh_refused. rewrite H. reflexivity. Qed.
Lemma vrd_refused_f : forall ok cnt fail i, nth i ok true = false ->
  prh_refused ok cnt fail i = negb (cnt + Z.of_nat i =? fail).
Proof. intros ok cnt fail i H. unfold prh_refused. rewrite H. reflexivity. Qed.
Lemma vrd_rpeak1 : forall ok cnt fail hs, prh_refused_peak ok cnt fail 1 hs =
  Z.max (if prh_refused ok cnt fail 0 then Z.min SIZE_MAXZ (nth 0 hs 0) else 0) 0.
Proof. reflexivity. Qed.
Lemma vrd_rpeak2 : forall ok cnt fail hs, prh_refused_peak ok cnt fail 2 hs =
  Z.max (if prh_refused ok cnt fail 0 then Z.min SIZE_MAXZ (nth 0 hs 0) else 0)
    (Z.max (if prh_refused ok cnt fail 1 then Z.min SIZE_MAXZ (nth 1 hs 0) else 0) 0).
Proof. reflexivity. Qed.

(* THE LEDGER MOVE OF grow's KIDS-REFUSING ARMS from the call's entry (tr = [EFail 448], ok = [false]): the chosen
   failure (arm 2: cnt = fail, the counter moves and g_fail_at is spent, peak and g_ran_out kept) and the refusal
   (arm 3: g_peak to the refused request's live count, g_ran_out set when the 448-byte request is at most g_most);
   the refusal peak reads the granted trace's first held count, 448 (vrd_gt_helds) *)
Lemma vrd_lm_kids_fail : forall d o x Lam peak cnt fail ran most, (d < PjGrammar.MAXD)%nat ->
  (forall r, PjGrammar.skip (tl x) <> PjGrammar.closer o :: r) ->
  0 <= Ledger.lsum Lam <= peak -> 0 <= cnt -> cnt + 2 < 2 ^ 64 - 1 -> cnt = fail ->
  rd_ledger_move Lam peak cnt fail ran most [false] (prhPi_gtrace d o x) [PjGrammar.EFail 448] [] Lam peak (cnt + 1)
    SIZE_MAXZ ran.
Proof.
intros d o x Lam peak cnt fail ran most Hd Hnc HLb Hc0 Hc Hcf. subst fail.
unfold rd_ledger_move. cbn [PjGrammar.calls PjGrammar.is_call].
split; [split; [|split]|].
- intros i Hi _. assert (i = 0%nat) by lia. subst i. reflexivity.
- left. reflexivity.
- intros i Hi Hr _. exfalso. assert (i = 0%nat) by lia. subst i.
  rewrite vrd_refused_f in Hr by reflexivity. cbn [Z.of_nat] in Hr. rewrite Z.add_0_r, Z.eqb_refl in Hr. discriminate Hr.
- split; [cbn [Z.of_nat]; rewrite Z.mod_small by lia; reflexivity|].
  split; [split; [intros _; reflexivity | intros Hno; exfalso; apply Hno; cbn [Z.of_nat]; lia]|].
  split; [apply Permutation_refl|]. split; [apply Permutation_refl|]. split; [reflexivity|].
  assert (Hrf : prh_refused [false] cnt cnt 0 = false)
    by (rewrite vrd_refused_f by reflexivity; apply negb_false_iff, Z.eqb_eq; cbn [Z.of_nat]; lia).
  rewrite vrd_rpeak1, Hrf. cbn [hpeakR PjGrammar.held_ev]. lia.
Qed.

Lemma vrd_lm_kids_ref : forall d o x Lam peak cnt fail ran most, (d < PjGrammar.MAXD)%nat ->
  (forall r, PjGrammar.skip (tl x) <> PjGrammar.closer o :: r) ->
  0 <= Ledger.lsum Lam <= peak -> 0 <= cnt -> cnt + 2 < 2 ^ 64 - 1 -> cnt <> fail ->
  rd_ledger_move Lam peak cnt fail ran most [false] (prhPi_gtrace d o x) [PjGrammar.EFail 448] [] Lam
    (if 0 =? 0 then Z.max peak (Z.min SIZE_MAXZ (Ledger.lsum Lam + 56 * cap2R 0))
     else Z.max peak (Z.min SIZE_MAXZ (Ledger.lsum Lam - 56 * 0 + 56 * cap2R 0)))
    ((cnt + 1) mod 2 ^ 64) fail (if 56 * cap2R 0 <=? most then 1 else ran).
Proof.
intros d o x Lam peak cnt fail ran most Hd Hnc HLb Hc0 Hc Hcf.
destruct (vrd_gt_helds d o x Hd Hnc) as (hs & Hhs).
assert (Hrf : prh_refused [false] cnt fail 0 = true).
{ rewrite vrd_refused_f by reflexivity. cbn [Z.of_nat]. rewrite Z.add_0_r.
  destruct (Z.eqb_spec cnt fail); [lia | reflexivity]. }
change (56 * cap2R 0) with 448. change (0 =? 0) with true. cbv iota beta.
unfold rd_ledger_move. cbn [PjGrammar.calls PjGrammar.is_call].
split; [split; [|split]|].
- intros i Hi He. exfalso. assert (i = 0%nat) by lia. subst i. cbn [Z.of_nat] in He. lia.
- destruct (Z.leb_spec 448 most) as [Hm | Hm]; [right | left; reflexivity].
  split; [reflexivity|]. exists 0%nat. split; [lia|]. split; [exact Hrf|]. exact Hm.
- intros i Hi _ Hle. assert (i = 0%nat) by lia. subst i. assert (Hle' : 448 <= most) by exact Hle.
  destruct (Z.leb_spec 448 most); [reflexivity | lia].
- split; [reflexivity|].
  split; [split; [intros (H1 & H2); cbn [Z.of_nat] in H2; lia | intros _; reflexivity]|].
  split; [apply Permutation_refl|]. split; [apply Permutation_refl|]. split; [reflexivity|].
  rewrite vrd_rpeak1, Hrf, Hhs. cbn [map nth hpeakR PjGrammar.held_ev]. lia.
Qed.

(* the first grow's request and its live room AT EACH OF ITS EVENTS (tgrow_specX's per-event premise, the kit's cut
   7cdbb61b5fa0), out of the call's rd_room: grow's events are a prefix of the call's all-granted events
   (VrdLedgerStep.vl_live_evs_prefix) *)
Lemma vrd_grow_room : forall d o x S, (d < PjGrammar.MAXD)%nat ->
  (forall r, PjGrammar.skip (tl x) <> PjGrammar.closer o :: r) ->
  rd_room S (prhPi_gtrace d o x) ->
  56 * cap2R 0 + cf_head < cf_malloc_max /\ prh_live_evs S (prhPg_evs ((if o then 6 else 5) =? 6) 0 0 []).
Proof.
intros d o x S Hd Hnc (_ & Hreq & Hlive). split.
- destruct (vrd_gtrace_grow d o x Hd Hnc) as (t & Ht). rewrite Ht in Hreq.
  assert (Hmr : forall u, 448 <= prh_maxreq (PjGrammar.EGrow 0 448 :: u))
    by (intros u; unfold prh_maxreq; cbn [map fold_right PjGrammar.esize]; lia).
  specialize (Hmr ((if o then [PjGrammar.EGrow 0 64] else []) ++ t)).
  unfold cap2R. cbn [Z.eqb]. lia.
- destruct (vrd_gevs_prefix d o x Hd Hnc) as (t & Ht). rewrite Ht in Hlive.
  exact (VrdLedgerStep.vl_live_evs_prefix _ _ _ Hlive).
Qed.

Lemma vrd_igrow_pre : forall d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v
    P regs M mdc,
  vrd_ipre d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v ->
  (d < PjGrammar.MAXD)%nat ->
  vrd_imid d o e q text len v regs0 ly Sa Hp W mem0 md0 P regs M mdc ->
  (forall r, PjGrammar.skip (tl (rest_atR tb text p)) <> PjGrammar.closer o :: r) ->
  arodata_okP segs pa_relro_lo pa_relro_hi B (aview segs (w_H W) M) /\
  spZ regs + 64 <= ly_stk_hi ly /\
  v + 56 <= YM05.alloc_ceiling /\
  pj_hdrR segs (mrestrict (w_H W) M) v (if o then 6 else 5) 0 0 0 0 0 0 /\
  fwin ly W regs M (e + 144) /\ prhReader_at B ly Sa Lam regs (e + 144) v 56 /\
  range_addressable (aview segs (w_H W) M) SHADOW_OFF v 56 /\
  prh_ledger B ly Sa Hp W M Lam peak cnt fail ran most own /\ cnt + 2 < 2 ^ 64 - 1 /\
  56 * cap2R 0 + cf_head < cf_malloc_max /\ prh_live_evs Sa (prhPg_evs ((if o then 6 else 5) =? 6) 0 0 []).
Proof.
intros d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v P regs M mdc HPRE Hd HMID Hnc.
pose proof HPRE as ((HPRE0 & HROD & Hshi64 & _) & HMN & HCTX & HUC & HCE & HCHI & HQCH & H10 & H11 & H12 & HRD & Hpe & Hop &
  HROOM & HPKS & HPKL & HFU & HFR & HCWR).
pose proof HRD as (Hfrm & Hmu & Hu1 & Hu2 & HIN & HWIN & Hspq & Hqe & HRAq & HSRC & HHOME & HMAX & HNODE & Hqv &
  Htv & Hvw & HLED & HdM & Hcnt).
pose proof HIN as (Vp & Ve & Vd & RWq & Hq8 & Ht0 & Ht62 & Htp & Hlen & Hgt & Hqt & Hd32).
pose proof HNODE as (Hv4096 & Hv8 & (Hvmod & RWv) & HZv & HATv & HAMv & HNv & HRAv).
pose proof HPRE0 as (HAR & Hra & Hra4 & Hgp & Htp' & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof HWIN as (He0 & He16 & Hetop & Hepres).
pose proof (vrd_stk_ge d) as HSTK. pose proof H_img as (Himg1 & Himg2 & Himg3). unfold PI_FRAME in HSTK.
pose proof HSRC as (Hbt & Ht4096 & Htceil & Htamr & HRAt & Hhull).
rewrite Hlen in Htceil, Htamr.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAMv.
pose proof HMID as (HAT & Hgp1 & Htp1 & H18 & H20 & Vty & KM & KG & HJ).
pose proof HAT as (Hsp & Hs1 & Hs2 & Hs16 & H8 & H26 & Hq1 & Hq2 & Hq3 & _).
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ pi_wr (spZ regs0) q v a ->
  aview segs (w_H W) M a = aview segs (w_H W) mem0 a)
  by (intros a Ha Hn; unfold aview, mbyte; rewrite KM; [reflexivity | rewrite unsigned_lit_small by lia; exact Hn]).
assert (Hvimg : forall a, v <= a < v + 56 -> ~ in_img segs a).
{ intros a Ha.
  exact (proj1 (vrd_v_place ly Sa Hp W mem0 md0 Lam peak cnt fail ran most own regs0 e v HAR HLED HATv ltac:(lia) a Ha)). }
assert (Hvfr : forall a, v <= a < v + 56 -> ~ (spZ regs0 - PI_FRAME <= a < spZ regs0)).
{ intros a Ha Hf. apply (proj2 (HNv a Ha)). unfold PI_FRAME in *. lia. }
(* the node below alloc_ceiling: prhReader_at's window case is excluded by rd_pre's node-window conjunct *)
assert (Hvlow : v + 56 <= YM05.alloc_ceiling).
{ destruct HATv as [(a0 & k0 & Hin & Hle & Hhi) | [(b0 & m0 & Hin & _ & Hle & Hhi) | [(cid & pos & Hin & Hle & Hhi) | Hww]]].
  - destruct (vrd_led_hblk ly Sa Hp W mem0 Lam peak cnt fail ran _ _ a0 k0 HLED Hin) as (Hk0 & Hab0 & _).
    destruct (alx_blocks segs B ARx LAWS _ _ _ _ _ _ _ _ HAR Hab0) as (_ & _ & Hc0 & _).
    assert (Hrq : k0 + cf_head <= req_size (k0 + cf_head))
      by (unfold req_size; destruct (Z.eqb_spec (k0 + cf_head) 0); lia).
    pose proof (@cf_head_nonneg cp). lia.
  - destruct (alx_blocks segs B ARx LAWS _ _ _ _ _ _ _ _ HAR Hin) as (_ & _ & Hc0 & _).
    assert (Hrq : m0 <= req_size m0) by (unfold req_size; destruct (Z.eqb_spec m0 0); lia). lia.
  - destruct (frames_bounds_x segs B ARx LAWS _ _ _ _ _ _ cid pos HAR Hin) as (_ & Hc0 & _). lia.
  - lia. }
assert (Hpres_up : forall a, apresent (w_H W) mem0 a -> apresent (w_H W) M a).
{ intros a (Hh & b & Hb). split; [exact Hh|].
  specialize (KG (Z_to_bv 64 a)). unfold mrestrict in KG. rewrite Hh in KG.
  destruct (M (Z_to_bv 64 a)) as [b'|] eqn:HM; [exists b'; reflexivity|].
  exfalso. apply KG; [rewrite Hb; discriminate | reflexivity]. }
destruct (vrd_grow_room d o (rest_atR tb text p) Sa Hd Hnc HROOM) as [Hreq Hlive].
split.
{ intros a Hro Hn He. rewrite KA; [exact (HROD a Hro Hn He)| |].
  - assert (Hi : in_img segs a)
      by (destruct Hro as [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr]
                                                      | exact (pa_relro_img a Hr)]).
    pose proof (@pa_segs_low _ _ PI_prog_A a Hi). unfold kLowMemEnd in *. lia.
  - assert (Hi : in_img segs a)
      by (destruct Hro as [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr]
                                                      | exact (pa_relro_img a Hr)]).
    pose proof (@pa_segs_low _ _ PI_prog_A a Hi) as Hlow. unfold kLowMemEnd in Hlow.
    unfold pi_wr, PI_FRAME. intros [H|[H|[H|H]]]; [lia | lia | lia | exact (Hvimg a ltac:(lia) Hi)]. }
split; [unfold spZ in *; lia|].
split; [exact Hvlow|].
split.
{ apply (vrd_hdr_typed (mrestrict (w_H W) mem0) _ v); [exact HZv | | | destruct o; lia | exact Vty].
  - apply (vrd_rdkeep_w (w_H W) mem0 M _ _ KM). intros a Ha. cbv beta in Ha. split; [lia|]. unfold pi_wr.
    intros [H|[H|[H|H]]]; [exact (Hvfr a ltac:(lia) H) | lia | lia | lia].
  - split; [exact Hvmod | intros x Hx; apply (writable_at_grows segs _ _ x KG); exact (RWv x Hx)]. }
split.
{ split; [lia|]. split; [rewrite Z.add_mod by lia; rewrite He16; reflexivity|].
  split; [lia|].
  intros a Ha. apply Hpres_up. destruct (Z_lt_le_dec a (spZ regs0)) as [Hlt|Hge].
  - apply Hpres. lia.
  - apply Hepres. lia. }
split.
{ destruct HATv as [A|[Bc|[C|Dw]]]; [left; exact A | right; left; exact Bc | right; right; left; exact C | exfalso; lia]. }
split.
{ eapply range_addressable_agree; [|exact HRAv]. intros x Hx.
  unfold aview, mbyte. rewrite KM; [reflexivity|]. unfold shadow_of_addr.
  assert (Hsx : 0 <= x / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). unfold pi_wr, PI_FRAME, SHADOW_OFF. lia. }
split; [exact (vrd_iledger d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v M HPRE KM)|].
split.
{ assert (Hrp : (1 <= length (rest_atR tb text p))%nat).
  { rewrite (vrd_rest_cons tb text p) by lia. cbn [length]. lia. }
  lia. }
split; [exact Hreq | exact Hlive].
Qed.

(* ============================================================================================================== *)
(* D2. THE CALL. grow's footprint, and its post as the text's own named post body PRH_FnReader.tgrP_Q (tgrP_Q_check:
   the text concludes fpostWmR .. at tgrP_Q) under this file's argument order, so the step after the call (D3,
   vrd_iRet) has a statement. The text's threaded hull use (`hull_used S S'` over grow's all-granted events) is its
   second conjunct; the arms are tgrP_A1 .. tgrP_A7.                                                              *)
(* ============================================================================================================== *)
Definition vrd_gfp (ty kids keys cap v : Z) : list (Z * Z) :=
  [(v + 24, v + 40); (v + 48, v + 56)] ++ ablocks_fp (prhReader_ab (kids_blkR kids cap ++ keys_blkR ty keys cap)).

Definition vrd_gpost (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (mem : word -> option byte)
  (v ty num str kids keys n cap : Z) (kb yb : list Z) (Lam : list (Z * Z)) (peak cnt fail ran most own : Z)
  : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  tgrP_Q (L := A_prog_listing) (PA := PI_prog_A) B most own ly S Hp W mem v ty num str kids keys n cap kb yb Lam peak
    cnt fail ran.

(* the grow text, read back through the two names: a sanity statement that they are its footprint and post (the text
   concludes SRr' segs RZ_cf with the post fpostWmR at wle', and takes the hull budget over its all-granted events) *)
Lemma vrd_grow_named : forall most own ly S Hp W regs mem md ch e v ty num str kids keys n cap kb yb Lam peak cnt fail
    ran,
  fpre B ARx STK_grow ly S Hp W regs mem md ch -> prh_univ_closure B CTX0 ->
  (exists ch, achain ly (aview segs (w_H W) mem) (spZ regs - pi_frame F_grow) (prh_s0 F_grow v) ch) ->
  room_live_cf S ->
  Z.of_nat (PresetRun.pkR YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (prhPg_evs (ty =? 6) n cap [])) <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV ->
  Z.of_nat (PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (prhPg_evs (ty =? 6) n cap [])) <= PresetLiveBounds.L24 + PresetLiveBounds.DRV ->
  PresetHullBudget.hull_budget S (prhPg_evs (ty =? 6) n cap []) ->
  getr regs 10 = w64 v -> v <> 0 -> v mod 8 = 0 ->
  pj_hdrR segs (mrestrict (w_H W) mem) v ty num str kids keys n cap ->
  pj_slots_atR (prh_lin Lam) ty kids keys n cap ->
  pj_apartR (kids_blkR kids cap ++ keys_blkR ty keys cap) v ->
  fwin ly W regs mem e -> prhReader_at B ly S Lam regs e v 56 ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF v 56 ->
  (n = cap -> bytes_at W mem kids kb /\ Z.of_nat (length kb) = 56 * cap /\
     (ty = 6 -> bytes_at W mem keys yb /\ Z.of_nat (length yb) = 8 * cap)) ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  cnt + 2 < 2 ^ 64 - 1 ->
  (n = cap -> 56 * cap2R cap + cf_head < cf_malloc_max /\ prh_live_evs S (prhPg_evs (ty =? 6) n cap [])) ->
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (pa_sigma AS_grow) regs mem md)
    (fpostWmR B ARx SK (wle' segs YGcfRehidePost.RZ_cf) STK_grow e (vrd_gfp ty kids keys cap v) regs ly S Hp W mem md
       (vrd_gpost ly S Hp W mem v ty num str kids keys n cap kb yb Lam peak cnt fail ran most own)).
Proof. exact (H_grow). Qed.

(* ---- THE CHAIN FROM s0 = q AT THE CALL (vrd_call_W's premise 12): the words at q - 16 and q - 8 are frame slots
   (the saved ra / s0, VrdIStep.vi_saved) or caller words of the granted window kept since the entry; the one at
   q - 16 is below alloc_ceiling by prh_cur_entry, so VproC's vrd_cur_chain_call gives the chain ---- *)
Lemma vrd_aview_present : forall (H : word -> bool) m a, apresent H m a -> exists b, aview segs H m a = Some b.
Proof.
intros H m a (Hh & b & Hb). exists (bv_unsigned b). unfold aview, mbyte, mrestrict. rewrite Hh, Hb. reflexivity.
Qed.

Lemma vrd_rdword_present : forall (H : word -> bool) m a, (forall k, 0 <= k < 8 -> apresent H m (a + k)) ->
  exists w, rdword (aview segs H m) a = Some w.
Proof.
intros H m a Hp.
destruct (vrd_aview_present H m (a + 0) (Hp 0 ltac:(lia))) as [b0 E0]. rewrite Z.add_0_r in E0.
destruct (vrd_aview_present H m (a + 1) (Hp 1 ltac:(lia))) as [b1 E1].
destruct (vrd_aview_present H m (a + 2) (Hp 2 ltac:(lia))) as [b2 E2].
destruct (vrd_aview_present H m (a + 3) (Hp 3 ltac:(lia))) as [b3 E3].
destruct (vrd_aview_present H m (a + 4) (Hp 4 ltac:(lia))) as [b4 E4].
destruct (vrd_aview_present H m (a + 5) (Hp 5 ltac:(lia))) as [b5 E5].
destruct (vrd_aview_present H m (a + 6) (Hp 6 ltac:(lia))) as [b6 E6].
destruct (vrd_aview_present H m (a + 7) (Hp 7 ltac:(lia))) as [b7 E7].
unfold rdword. rewrite E0, E1, E2, E3, E4, E5, E6, E7. eexists. reflexivity.
Qed.

Lemma vrd_qchain : forall d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v P regs M mdc,
  vrd_ipre d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v ->
  vrd_imid d o e q text len v regs0 ly Sa Hp W mem0 md0 P regs M mdc ->
  exists ch1, achain ly (aview segs (w_H W) M) (spZ regs0 - 144) q ch1.
Proof.
intros d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v P regs M mdc HPRE HMID.
pose proof HPRE as ((HPRE0 & HROD & Hshi64 & _) & HMN & HCTX & HUC & HCE & HCHI & HQCH & H10 & H11 & H12 & HRD & Hpe & Hop &
  HROOM & HPKS & HPKL & HFU & HFR & HCWR).
pose proof HRD as (Hfrm & Hmu & Hu1 & Hu2 & HIN & HWIN & Hspq & Hqe & HRAq & HSRC & HHOME & HMAX & HNODE & Hqv &
  Htv & Hvw & HLED & HdM & Hcnt).
pose proof HIN as (Vp & Ve & Vd & RWq & Hq8 & _).
pose proof HPRE0 as (HAR & Hra & Hra4 & Hgp & Htp' & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof HWIN as (He0 & He16 & Hetop & Hepres).
pose proof (vrd_stk_ge d) as HSTK. pose proof H_img as (Himg1 & Himg2 & Himg3). unfold PI_FRAME in HSTK.
pose proof HMID as (HAT & _ & _ & _ & _ & _ & KM & KG & _).
pose proof HAT as (_ & Hs1 & Hs2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSV & _).
destruct (Z_lt_le_dec q (ly_top ly - 16)) as [Hqt | Hqt].
2:{ exists []. left. split; [right; left; exact Hqt | reflexivity]. }
assert (KA : forall x, 0 <= x < 2 ^ 64 -> ~ pi_wr (spZ regs0) q v x ->
  aview segs (w_H W) M x = aview segs (w_H W) mem0 x)
  by (intros x Hx Hn; unfold aview, mbyte; rewrite KM; [reflexivity | rewrite unsigned_lit_small by lia; exact Hn]).
assert (HW : forall a, a = q - 16 \/ a = q - 8 ->
  exists w, rdword (aview segs (w_H W) M) a = Some w /\ prh_word_entry W mem0 regs0 a w).
{ intros a Ha.
  destruct (Z.eq_dec a (spZ regs0 - 8)) as [E8|N8]; [| destruct (Z.eq_dec a (spZ regs0 - 16)) as [E16|N16]].
  - exists (raZ regs0). split.
    + rewrite E8. apply vrd_rdword_of_val_mem.
      * pose proof (HSV 0%nat ltac:(lia)) as V. cbn [nth vi_extras] in V.
        replace (spZ regs0 - 8 - 8 * Z.of_nat 0) with (spZ regs0 - 8) in V by lia. exact V.
      * pose proof (bv_unsigned_in_range 64 (getr regs0 1)) as Hb. change (bv_modulus 64) with (2 ^ 64) in Hb.
        exact Hb.
    + unfold prh_word_entry. rewrite E8, Z.eqb_refl. reflexivity.
  - exists (s0Z regs0). split.
    + rewrite E16. apply vrd_rdword_of_val_mem.
      * pose proof (HSV 1%nat ltac:(lia)) as V. cbn [nth vi_extras] in V.
        replace (spZ regs0 - 8 - 8 * Z.of_nat 1) with (spZ regs0 - 16) in V by lia. exact V.
      * pose proof (bv_unsigned_in_range 64 (getr regs0 8)) as Hb. change (bv_modulus 64) with (2 ^ 64) in Hb.
        exact Hb.
    + unfold prh_word_entry. rewrite (proj2 (Z.eqb_neq a (spZ regs0 - 8)) N8), E16, Z.eqb_refl. reflexivity.
  - assert (Ha0 : spZ regs0 <= a /\ a + 8 <= q) by lia.
    destruct (vrd_rdword_present (w_H W) mem0 a) as [w Hw].
    { intros k Hk. apply Hepres. lia. }
    exists w. split.
    + rewrite (rdword_ext (aview segs (w_H W) mem0) (aview segs (w_H W) M) a); [exact Hw|].
      intros k Hk. apply KA; [lia|]. unfold pi_wr, PI_FRAME. lia.
    + unfold prh_word_entry. rewrite (proj2 (Z.eqb_neq a (spZ regs0 - 8)) N8),
        (proj2 (Z.eqb_neq a (spZ regs0 - 16)) N16). exact Hw. }
destruct (HW (q - 16) (or_introl eq_refl)) as (w16 & H16 & E16).
destruct (HW (q - 8) (or_intror eq_refl)) as (w8 & H8 & _).
assert (Hw16 : w16 < YM05.alloc_ceiling).
{ destruct HCE as (_ & HCE'). pose proof (HCE' F_parse_items (or_intror eq_refl)) as Hlo.
  unfold prh_s0 in Hlo. rewrite H_s0, Z.add_0_r in Hlo.
  exact (Hlo w16 E16). }
assert (Hcq : YM05.alloc_ceiling <= q) by lia.
exact (vrd_cur_chain_call ly (w_H W) M (spZ regs0 - 144) q w16 Hcq Hqt Hq8 ltac:(lia) H16 Hw16 (ex_intro _ w8 H8)).
Qed.

(* ---- D3's statement: the state at row 92, after the first grow returned (vrd_call_WR's conclusion, with the
   position's a2 restored). grow's text concludes SRr' segs RZ_cf, so the world after the call is a wle' extension,
   both journals are at wle' and the step concludes SRr' (the re-hiding move) ---- *)
Definition vrd_iRet (d : nat) (o : bool) (ly : alayout) (Sa : astate) (Hp : list Z) (W : world segs)
  (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (ch : list (Z * Z * Z))
  (Lam : list (Z * Z)) (peak cnt fail ran most own e q text len p : Z) (tb : list Z) (v : Z) : Prop :=
  forall P regsC MC mdc W2 ly2 S2 Hp2 regs2 mem2 md2 k1,
  vrd_imid d o e q text len v regs0 ly Sa Hp W mem0 md0 P regsC MC mdc ->
  p + 1 <= P <= text + len -> PjGrammar.skip (tl (rest_atR tb text p)) = rest_atR tb text P ->
  (forall r, PjGrammar.skip (tl (rest_atR tb text p)) <> PjGrammar.closer o :: r) ->
  wle' segs YGcfRehidePost.RZ_cf W W2 ->
  ajournal_xR (SK := SK) segs B prh_pst ARx (wle' segs YGcfRehidePost.RZ_cf) (STK_parse_items d + e) (spZ regs0 + e)
    (rd_fp q v) ly Sa Hp W mem0 md0 [] ly2 S2 Hp2 W2 mem2 md2 (0 + k1) ->
  ajournal_xR (SK := SK) segs B prh_pst ARx (wle' segs YGcfRehidePost.RZ_cf) (STK_grow + (e + 144)) (spZ regs0 + e)
    (vrd_gfp (if o then 6 else 5) 0 0 0 v) ly Sa Hp W MC mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  (forall a, spZ regs0 + e + - (e + 144) <= a < spZ regs0 + e -> ~ inFP (vrd_gfp (if o then 6 else 5) 0 0 0 v) a ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W) MC a) ->
  aregs_preserved regsC regs2 ->
  vrd_gpost ly Sa Hp W MC v
    (if o then 6 else 5) 0 0 0 0 0 0 [] [] Lam peak cnt fail ran most own ly2 S2 Hp2 W2 regs2 mem2 md2 ->
  SRr' segs YGcfRehidePost.RZ_cf W2
    (mkCfg (YK11.mkst regs2 (Z_to_bv 64 (BASE + (PI_GROWRET - A_prog_base))) mem2 (YK11.seg_rom segs)) md2)
    (vrd_iQall d o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v).

(* D3 IN THE GENERIC FORM: vrd_iRet's premises, P of the memory grow returned, and P of the memory the segment ends
   with in the post. The segment (row 92 to row 108, or to the return) crosses no call, so its laws are the single
   srr_inv_laws premise of vrd_iRet_inv. *)
Definition vrd_iRet_P (Pm : (word -> option byte) -> Prop) (d : nat) (o : bool) (ly : alayout) (Sa : astate)
  (Hp : list Z) (W : world segs)
  (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (ch : list (Z * Z * Z))
  (Lam : list (Z * Z)) (peak cnt fail ran most own e q text len p : Z) (tb : list Z) (v : Z) : Prop :=
  forall P regsC MC mdc W2 ly2 S2 Hp2 regs2 mem2 md2 k1,
  vrd_imid d o e q text len v regs0 ly Sa Hp W mem0 md0 P regsC MC mdc ->
  p + 1 <= P <= text + len -> PjGrammar.skip (tl (rest_atR tb text p)) = rest_atR tb text P ->
  (forall r, PjGrammar.skip (tl (rest_atR tb text p)) <> PjGrammar.closer o :: r) ->
  wle' segs YGcfRehidePost.RZ_cf W W2 ->
  ajournal_xR (SK := SK) segs B prh_pst ARx (wle' segs YGcfRehidePost.RZ_cf) (STK_parse_items d + e) (spZ regs0 + e)
    (rd_fp q v) ly Sa Hp W mem0 md0 [] ly2 S2 Hp2 W2 mem2 md2 (0 + k1) ->
  ajournal_xR (SK := SK) segs B prh_pst ARx (wle' segs YGcfRehidePost.RZ_cf) (STK_grow + (e + 144)) (spZ regs0 + e)
    (vrd_gfp (if o then 6 else 5) 0 0 0 v) ly Sa Hp W MC mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  (forall a, spZ regs0 + e + - (e + 144) <= a < spZ regs0 + e -> ~ inFP (vrd_gfp (if o then 6 else 5) 0 0 0 v) a ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W) MC a) ->
  aregs_preserved regsC regs2 ->
  vrd_gpost ly Sa Hp W MC v
    (if o then 6 else 5) 0 0 0 0 0 0 [] [] Lam peak cnt fail ran most own ly2 S2 Hp2 W2 regs2 mem2 md2 ->
  Pm mem2 ->
  SRr' segs YGcfRehidePost.RZ_cf W2
    (mkCfg (YK11.mkst regs2 (Z_to_bv 64 (BASE + (PI_GROWRET - A_prog_base))) mem2 (YK11.seg_rom segs)) md2)
    (fun W' c' => vrd_iQall d o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v W' c' /\
       Pm (ms_mem (cfg_ms c'))).

(* THE CALL RULE for grow's primed text: VrdArm.vrd_call_W over the R forms at wle' segs RZ_cf - the callee concludes
   SRr' with its post fpostWR at wle', the caller's journal is at wle', and the conclusion is SRr' with both journals
   at wle' (the callee's entry pre by YCbqG.afn_pre_x_atR, the composition by YCbqG.ajournal_x_subR at wle'_trans) *)
Lemma vrd_call_WR :
  forall W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 e1 FP1 (o : Z) raw ch1
    (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  st_ok segs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  ajournal_xR (SK := SK) segs B prh_pst ARx (wle' segs YGcfRehidePost.RZ_cf) STK sp0 FP ly S Hp W0 mem md own
    lyc Sc Hpc W (ms_mem ms) mdc k ->
  spZ (ms_regs ms) = sp0 + o ->
  o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK -> o + e1 = 0 ->
  getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
  getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview segs (w_H W) (ms_mem ms)) (sp0 + o) (s0Z (ms_regs ms)) ch1 ->
  (afn_pre_x segs B ARx STK1 lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch1 ->
   SRr' segs YGcfRehidePost.RZ_cf W
     (mkCfg (YK11.mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (YK11.seg_rom segs)) mdc)
     (fpostWR B ARx SK (wle' segs YGcfRehidePost.RZ_cf) STK1 e1 FP1 (ms_regs ms) lyc Sc Hpc W (ms_mem ms) mdc Q)) ->
  (forall a, inFP FP1 a -> inFP FP a \/ in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a \/
     (exists f, In f own /\ in_zr a (frame_rng lyc f)) \/
     (alloc_ceiling <= a /\ sp0 - STK <= a < sp0)) ->
  SRr' segs YGcfRehidePost.RZ_cf W (mkCfg ms mdc)
    (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
       c2 = mkCfg (YK11.mkst regs2 raw mem2 (YK11.seg_rom segs)) md2 /\
       ajournal_xR (SK := SK) segs B prh_pst ARx (wle' segs YGcfRehidePost.RZ_cf) STK sp0 FP ly S Hp W0 mem md own
         ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
       ajournal_xR (SK := SK) segs B prh_pst ARx (wle' segs YGcfRehidePost.RZ_cf) (STK1 + e1) sp0 FP1 lyc Sc Hpc W
         (ms_mem ms) mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
       (forall a, sp0 + o <= a < sp0 -> ~ inFP FP1 a ->
          aview segs (w_H W2) mem2 a = aview segs (w_H W) (ms_mem ms) a) /\
       aregs_preserved (ms_regs ms) regs2 /\ Q ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof.
intros W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 e1 FP1 o raw ch1 Q
  HS Hrv HJ Hsp' Hal Hneg Hstk1 Hbud Hoe Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
rewrite (st_ok_restrict_mkst segs (w_H W) E ss ms HS Hrv).
eapply (SRrG_mono segs (wle' segs YGcfRehidePost.RZ_cf)).
{ apply Hcallee.
  eapply (afn_pre_x_atR segs B prh_pst ARx (wle' segs YGcfRehidePost.RZ_cf) STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc
    W (ms_mem ms) mdc k (ms_regs ms) STK1 o ch1); try eassumption.
  - rewrite Hra. exact Hraw.
  - unfold raZ. rewrite Hra. exact Hra4.
  - rewrite Hsp'. exact Hch. }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ1 & HWIN & HP & HQ).
exists ly2, S2, Hp2, regs2, mem2, md2, k1. rewrite Hra. split; [reflexivity|].
rewrite Hsp' in HJ1, HWIN.
replace (sp0 + o + e1) with sp0 in HJ1 by lia.
split; [| split; [exact HJ1 | split; [| split; [exact HP | exact HQ]]]].
- change own with ([] ++ own).
  eapply (ajournal_x_subR segs B prh_pst ARx LAWS (@pa_segs_low _ _ PI_prog_A) (wle' segs YGcfRehidePost.RZ_cf)
            (wle'_trans segs YGcfRehidePost.RZ_cf));
    [exact HJ | exact HJ1 | lia | lia
    | intros a Ha; destruct (HF a Ha) as [H|[H|[H|[_ H]]]]; [left | right; left | right; right; left
      | right; right; right]; exact H].
- intros a Ha Hn. apply HWIN; [lia | exact Hn].
Qed.

(* D2. the first grow at row 91, by vrd_call_WR at o = -(e + 144), e1 = e + 144, STK1 = STK_grow, with H_grow; the
   caller's journal at wle lifts to wle' (YCbqG.ajournal_xwR_mono at YA0nH.wle_wle'), and grow's hull budget is the
   prefix of the call's (vrd_hull_grow_budget) *)
Lemma vrd_igrow_inv : forall (Pm : (word -> option byte) -> Prop), srr_inv_laws segs Pm -> srr_inv_call segs Pm ->
  forall d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v,
  vrd_ipre d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v ->
  (d < PjGrammar.MAXD)%nat ->
  vrd_iRet_P Pm d o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v ->
  vrd_iDstep_P Pm d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v.
Proof.
intros Pm PLAW PCALL d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v HPRE Hd HR
  P E ss ms mdc HS Hrv Hpc HMID H10 H1 HP Hsk Hnc HPM.
set (regsC := regupd (ms_regs ms) 12%bv (w64 (text + len))) in HMID.
assert (GC : forall r : bv 5, bv_unsigned r <> 12 -> getr (ms_regs ms) r = getr regsC r)
  by (intros r Hr; subst regsC; symmetry; apply vrd_getr_upd_other; exact Hr).
pose proof HPRE as ((HPRE0 & HROD & Hshi64 & _) & HMN & HCTX & HUC & HCE & HCHI & HQCH & H10e & H11e & H12e & HRD & Hpe & Hop &
  HROOM & HPKS & HPKL & HFU & HFR & HCWR).
pose proof HCWR as (_ & _ & HHB).
pose proof HRD as (Hfrm & Hmu & Hu1 & Hu2 & HIN & HWIN & Hspq & Hqe & HRAq & HSRC & HHOME & HMAX & HNODE & Hqv &
  Htv & Hvw & HLED & HdM & Hcnt).
pose proof HNODE as (Hv4096 & Hv8 & _).
pose proof HPRE0 as (HAR & Hra & Hra4 & Hgp & Htp' & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof HWIN as (He0 & He16 & Hetop & Hepres).
pose proof (vrd_stk_ge d) as HSTK. pose proof H_img as (Himg1 & Himg2 & Himg3). unfold PI_FRAME in HSTK.
pose proof HMID as (HAT & Hgp1 & Htp1 & H18 & H20 & Vty & KM & KG & HJ).
pose proof (ajournal_xwR_mono segs B prh_pst ARx (@wle segs) (wle' segs YGcfRehidePost.RZ_cf)
  (wle_wle' segs YGcfRehidePost.RZ_cf) (STK_parse_items d + e) (spZ regs0 + e) (rd_fp q v) ly Sa Hp W mem0 md0 []
  ly Sa Hp W (ms_mem ms) mdc 0 [] HJ) as HJR.
pose proof HAT as (Hsp & Hs1 & Hs2 & Hs16 & H8 & _).
destruct (vrd_igrow_pre d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v P regsC
  (ms_mem ms) mdc HPRE Hd HMID Hnc) as (HROD' & Hshi' & Hvlow & HHDR & HFW & HAT' & HRAv' & HLED' & Hcnt2 & Hreq & Hlive).
destruct (vrd_qchain d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v P regsC
  (ms_mem ms) mdc HPRE HMID) as (ch1 & Hch1).
assert (N2 : bv_unsigned (2%bv : bv 5) <> 12) by (intros Hc; vm_compute in Hc; discriminate Hc).
assert (SP : spZ (ms_regs ms) = spZ regsC) by (unfold spZ; rewrite (GC 2%bv N2); reflexivity).
assert (He16' : exists k, e = 16 * k) by (exists (e / 16); pose proof (Z.div_mod e 16 ltac:(lia)); lia).
destruct He16' as (ke & Hke).
(* grow's live-count premises: its granted events are the first of the call's (vrd_gevs_prefix), and a count peak
   over a prefix is at most the peak over the whole (vrd_pk_prefix) *)
destruct (vrd_gevs_prefix d o (rest_atR tb text p) Hd Hnc) as (tg & Htg).
pose proof (vrd_hull_grow_budget d o (rest_atR tb text p) Sa Hd Hnc HHB) as HHB'.
assert (HPKS' : Z.of_nat (PresetRun.pkR YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf Sa))
    (prhPg_evs ((if o then 6 else 5) =? 6) 0 0 [])) <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV).
{ rewrite Htg in HPKS. pose proof (vrd_pk_prefix YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf Sa))
    (prhPg_evs ((if o then 6 else 5) =? 6) 0 0 []) tg). lia. }
assert (HPKL' : Z.of_nat (PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf Sa))
    (prhPg_evs ((if o then 6 else 5) =? 6) 0 0 [])) <= PresetLiveBounds.L24 + PresetLiveBounds.DRV).
{ rewrite Htg in HPKL. pose proof (vrd_pk_prefix (PresetRoom.in_cls YG00.kBatchClass)
    (PresetRoom.rs_live (YGcfRoom.room_of_cf Sa)) (prhPg_evs ((if o then 6 else 5) =? 6) 0 0 []) tg). lia. }
set (ty := if o then 6 else 5).
eapply (SRrG_bind segs (wle' segs YGcfRehidePost.RZ_cf) (wle'_trans segs YGcfRehidePost.RZ_cf)).
- apply (vrd_call_WR W E ss ms (STK_parse_items d + e) (spZ regs0 + e) (rd_fp q v) ly Sa Hp W mem0 md0 []
    ly Sa Hp mdc 0 STK_grow (e + 144) (vrd_gfp ty 0 0 0 v) (- (e + 144)) (getr (ms_regs ms) 1) ch1
    (fQmn (ms_mem ms) (vrd_gpost ly Sa Hp W
       (ms_mem ms) v ty 0 0 0 0 0 0 [] [] Lam peak cnt fail ran most own)) HS Hrv HJR).
  + rewrite SP, Hsp. lia.
  + replace (- (e + 144)) with ((- ke - 9) * 16) by lia. apply Z.mod_mul. lia.
  + lia.
  + exact Himg3.
  + lia.
  + lia.
  + rewrite (GC 3%bv ltac:(intros Hc; vm_compute in Hc; discriminate Hc)). exact Hgp1.
  + rewrite (GC 4%bv ltac:(intros Hc; vm_compute in Hc; discriminate Hc)). exact Htp1.
  + reflexivity.
  + rewrite H1. vm_compute. reflexivity.
  + rewrite H1. apply Z.leb_le. vm_compute. reflexivity.
  + replace (spZ regs0 + e + - (e + 144)) with (spZ regs0 - 144) by lia.
    unfold s0Z. rewrite (GC 8%bv ltac:(intros Hc; vm_compute in Hc; discriminate Hc)), H8. unfold w64.
    rewrite unsigned_lit_small by lia. exact Hch1.
  + intros HAFN. rewrite Hpc.
    assert (HFW' : fwin ly W (ms_regs ms) (ms_mem ms) (e + 144)) by (unfold fwin in *; rewrite SP; exact HFW).
    assert (HAT'' : prhReader_at B ly Sa Lam (ms_regs ms) (e + 144) v 56)
      by (unfold prhReader_at in *; rewrite SP; exact HAT').
    assert (Hshi'' : spZ (ms_regs ms) + 64 <= ly_stk_hi ly) by (rewrite SP; exact Hshi').
    assert (Hrac : raZ (ms_regs ms) < YM05.alloc_ceiling).
    { unfold raZ. rewrite H1. exact vrd_growret_ceil. }
    refine (vrd_grow_named most own ly Sa Hp W
      (ms_regs ms) (ms_mem ms) mdc ch1 (e + 144) v ty 0 0 0 0 0 0 [] [] Lam peak cnt fail ran
      (conj HAFN (conj HROD' (conj Hshi'' (conj Hrac Hfrm)))) HUC _ (proj1 HROOM) HPKS' HPKL' HHB' H10 ltac:(lia) Hv8
      HHDR
      _ _ HFW' HAT'' HRAv' _ HLED' Hcnt2 (fun _ => conj Hreq Hlive)).
    * exists []. apply achain_low. unfold prh_s0. rewrite H_s0g. lia.
    * subst ty. unfold pj_slots_atR.
      destruct o; (split; [lia|]); (split; [lia|]);
        (split; [intros _; split; [reflexivity | intros _; reflexivity] | intros Hc; lia]).
    * intros b x Hb. destruct o; cbn in Hb; destruct Hb.
    * intros _. split; [intros i Hi; cbn in Hi; lia|]. split; [reflexivity|].
      intros _. split; [intros i Hi; cbn in Hi; lia | reflexivity].
  + intros a Ha. left. unfold vrd_gfp in Ha. subst ty.
    destruct Ha as (r & Hin & Hr). destruct o; cbn [kids_blkR keys_blkR app prhReader_ab ablocks_fp map Z.eqb orb negb]
      in Hin; cbn [In] in Hin; (destruct Hin as [<- | [<- | []]]; cbn [fst snd] in Hr;
      (exists (v, v + 56); split; [right; right; left; reflexivity | cbn [fst snd]; lia])).
- intros W2 c2 Hle (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ1 & HJ2 & HWIN2 & HPR & HQ).
  rewrite H1.
  apply (HR P regsC (ms_mem ms) mdc W2 ly2 S2 Hp2 regs2 mem2 md2 k1 HMID HP Hsk Hnc Hle HJ1 HJ2 HWIN2);
    [|exact (proj1 HQ) | exact (PCALL _ _ (proj2 HQ) HPM)].
  intros r Hr. rewrite <- (GC (Z_to_bv 5 r)); [exact (HPR r Hr)|].
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. unfold acallee_saved in Hr.
  rewrite Z.mod_small by lia. lia.
Qed.

(* D3 at P := True from the old D3 statement, and back *)
Lemma vrd_iRet_to_P : forall d o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v,
  vrd_iRet d o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v ->
  vrd_iRet_P (fun _ => True) d o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v.
Proof.
intros d o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v HR
  P regsC MC mdc W2 ly2 S2 Hp2 regs2 mem2 md2 k1 HMID HP Hsk Hnc Hle HJ1 HJ2 HWIN2 HPR HQ _.
eapply (SRrG_mono segs (wle' segs YGcfRehidePost.RZ_cf));
  [exact (HR P regsC MC mdc W2 ly2 S2 Hp2 regs2 mem2 md2 k1 HMID HP Hsk Hnc Hle HJ1 HJ2 HWIN2 HPR HQ)|].
intros W' c' _ H. exact (conj H I).
Qed.

Lemma vrd_igrow : forall d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v,
  vrd_ipre d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v ->
  (d < PjGrammar.MAXD)%nat ->
  vrd_iRet d o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v ->
  vrd_iDstep d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v.
Proof.
intros d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v HPRE Hd HR.
apply vrd_iDstep_of_P.
exact (vrd_igrow_inv (fun _ => True) vrd_inv_true vrd_inv_call_true d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt
  fail ran most own e q text len p tb v HPRE Hd (vrd_iRet_to_P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HR)).
Qed.

(* F, reduced to D3: the segment master from the step after the first grow returned *)
Lemma vrd_ipro_ok_of_iRet : forall d CTX,
  (forall ly Sa Hp W regs mem md ch e q text len p tb v o Lam peak cnt fail ran most own,
     vrd_ipre d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v ->
     (d < PjGrammar.MAXD)%nat ->
     vrd_iRet d o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v) ->
  vrd_ipro_stmt d CTX.
Proof.
intros d CTX HR. apply vrd_ipro_ok_of_D.
intros ly Sa Hp W regs mem md ch e q text len p tb v o Lam peak cnt fail ran most own HPRE Hd.
exact (vrd_igrow d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v HPRE Hd
  (HR ly Sa Hp W regs mem md ch e q text len p tb v o Lam peak cnt fail ran most own HPRE Hd)).
Qed.

Lemma vrd_ipro_ok_of_iRet_inv : forall (Pm : (word -> option byte) -> Prop), srr_inv_laws segs Pm ->
  srr_inv_call segs Pm -> forall d CTX,
  (forall ly Sa Hp W regs mem md ch e q text len p tb v o Lam peak cnt fail ran most own,
     vrd_ipre d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v ->
     (d < PjGrammar.MAXD)%nat ->
     vrd_iRet_P Pm d o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v) ->
  vrd_ipro_stmt_P Pm d CTX.
Proof.
intros Pm PLAW PCALL d CTX HR. apply (vrd_ipro_ok_of_D_inv Pm PLAW).
intros ly Sa Hp W regs mem md ch e q text len p tb v o Lam peak cnt fail ran most own HPRE Hd.
exact (vrd_igrow_inv Pm PLAW PCALL d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v HPRE Hd
  (HR ly Sa Hp W regs mem md ch e q text len p tb v o Lam peak cnt fail ran most own HPRE Hd)).
Qed.

(* ============================================================================================================== *)
(* D3, the refusal arms' tail: from row 92 (slot 6024) with a0 = -1, `bnez a0` jumps to row 310 and vrd_iret
   returns; the symbolic state is IelemE's vi_ss_a0 over the thirteen saved words. After the first grow the journal
   is at wle' (grow's text), so the run is the runner's R form at wle' and the tail concludes SRr' with the post
   fpostWFR at wle'.                                                                                               *)
(* ============================================================================================================== *)
Lemma vrd_iref92 : forall (fxP : YK11.FPState) d ly Sa Hp W regs0 mem md ch e q v
    (regs : bvmap 5 word) (W' : world segs) ly' S' Hp' mem' md' (k : Z)
    (Qb : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  afn_pre_x segs B ARx (STK_parse_items d) ly Sa Hp W regs0 mem md ch ->
  spZ regs = spZ regs0 - 144 -> vi_saved W' mem' regs0 ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 18 = w64 (-1) ->
  getr regs 10 = w64 (-1) ->
  ajournal_xR (SK := SK) segs B prh_pst ARx (wle' segs YGcfRehidePost.RZ_cf) (STK_parse_items d + e) (spZ regs0 + e)
    (rd_fp q v) ly Sa Hp W mem md [] ly' S' Hp' W' mem' md' k ->
  (forall a, spZ regs0 <= a < spZ regs0 + e -> ~ inFP (rd_fp q v) a ->
     aview segs (w_H W') mem' a = aview segs (w_H W) mem a) ->
  frm_zero (@YK11.fp_csr fxP) -> fregs_kept_x fx fxP ->
  (forall regs' md'', getr regs' 10 = w64 (-1) -> aregs_preserved regs0 regs' -> Qb ly' S' Hp' W' regs' mem' md'') ->
  SRr' segs YGcfRehidePost.RZ_cf W'
    (mkCfg (@YK11.mkst fxP regs (Z_to_bv 64 (BASE + (PI_GROWRET - A_prog_base))) mem' (YK11.seg_rom segs)) md')
    (fpostWFR (fx := fx) B ARx SK (wle' segs YGcfRehidePost.RZ_cf) (STK_parse_items d) e (rd_fp q v) regs0 ly Sa Hp W
       mem md Qb).
Proof.
intros fxP d ly Sa Hp W regs0 mem md ch e q v regs W' ly' S' Hp' mem' md' k Qb
  HPRE Hsp HSV Hgp Htp Hs2 Ha0 HJ HWIN HFZ HFK HQ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (vi_st_ok_a0 6024 fxP W' regs0 regs mem' (-1) Hsp ltac:(lia) ltac:(lia) HSV ltac:(exact Ha0))
  as [HS SHOK].
replace (Z_to_bv 64 (BASE + (PI_GROWRET - A_prog_base))) with (w64 (A_IPC 6024)) by (vm_compute; reflexivity).
assert (HEI : img_env VAL A_LIM (vi_EI regs regs0)) by (unfold vi_EI; apply Eimg_env).
pose (RUNTO := paj_run_to_xR (fx := fxP) (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B prh_pst ARx LAWS
  (wle' segs YGcfRehidePost.RZ_cf) (wle'_refl segs YGcfRehidePost.RZ_cf) (wle'_trans segs YGcfRehidePost.RZ_cf)).
paj_run_to_tok_x RUNTO HS HJ SHOK vi_Bspan (4 * Z.of_nat A_IEPI_SLOT);
  [eapply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]|].
match goal with ms0 : machine_state |- _ => rename ms0 into ms2 end.
assert (Hmeq : ms_mem ms2 = mem') by (apply functional_extensionality; exact (vi_frame_all _ _ _ HF)).
pmkst HS.
lazymatch goal with |- context [mkCfg (YK11.mkst _ ?pc _ _) _] =>
  replace pc with (w64 (A_IPC A_IEPI_SLOT)) by (vm_compute; reflexivity) end.
rewrite Hmeq.
apply (vrd_iret fxP d ly Sa Hp W regs0 mem md ch e q v (ms_regs ms2) W' ly' S' Hp' mem' _ k (-1) Qb HPRE);
  [ | exact HSV | | | | first [exact HJ | rewrite Hmeq in HJ; exact HJ] | exact HWIN | exact HFZ | exact HFK
  | exact HQ].
- vi_reg HS (Z_to_bv 5 2) R2. unfold spZ. transitivity (bv_unsigned (getr (ms_regs ms2) (Z_to_bv 5 2))); [reflexivity|].
  rewrite R2, (vi_ew_low regs regs0 2 (Z_to_bv 5 2) eq_refl). exact Hsp.
- vi_reg HS (Z_to_bv 5 3) R3. transitivity (getr (ms_regs ms2) (Z_to_bv 5 3)); [reflexivity|].
  rewrite R3, (vi_ew_low regs regs0 3 (Z_to_bv 5 3) eq_refl). exact Hgp.
- vi_reg HS (Z_to_bv 5 4) R4. transitivity (getr (ms_regs ms2) (Z_to_bv 5 4)); [reflexivity|].
  rewrite R4, (vi_ew_low regs regs0 4 (Z_to_bv 5 4) eq_refl). exact Htp.
- vi_reg HS (Z_to_bv 5 18) R18. transitivity (getr (ms_regs ms2) (Z_to_bv 5 18)); [reflexivity|].
  rewrite R18, (vi_ew_low regs regs0 18 (Z_to_bv 5 18) eq_refl). exact Hs2.
Qed.

Lemma vrd_iref92_inv : forall (Pm : (word -> option byte) -> Prop), srr_inv_laws segs Pm ->
  forall (fxP : YK11.FPState) d ly Sa Hp W regs0 mem md ch e q v
    (regs : bvmap 5 word) (W' : world segs) ly' S' Hp' mem' md' (k : Z)
    (Qb : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  afn_pre_x segs B ARx (STK_parse_items d) ly Sa Hp W regs0 mem md ch ->
  spZ regs = spZ regs0 - 144 -> vi_saved W' mem' regs0 ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 18 = w64 (-1) ->
  getr regs 10 = w64 (-1) ->
  ajournal_xR (SK := SK) segs B prh_pst ARx (wle' segs YGcfRehidePost.RZ_cf) (STK_parse_items d + e) (spZ regs0 + e)
    (rd_fp q v) ly Sa Hp W mem md [] ly' S' Hp' W' mem' md' k ->
  (forall a, spZ regs0 <= a < spZ regs0 + e -> ~ inFP (rd_fp q v) a ->
     aview segs (w_H W') mem' a = aview segs (w_H W) mem a) ->
  frm_zero (@YK11.fp_csr fxP) -> fregs_kept_x fx fxP ->
  (forall regs' md'', getr regs' 10 = w64 (-1) -> aregs_preserved regs0 regs' -> Qb ly' S' Hp' W' regs' mem' md'') ->
  Pm mem' ->
  SRr' segs YGcfRehidePost.RZ_cf W'
    (mkCfg (@YK11.mkst fxP regs (Z_to_bv 64 (BASE + (PI_GROWRET - A_prog_base))) mem' (YK11.seg_rom segs)) md')
    (fun W'' c' => fpostWFR (fx := fx) B ARx SK (wle' segs YGcfRehidePost.RZ_cf) (STK_parse_items d) e (rd_fp q v)
       regs0 ly Sa Hp W mem md Qb W'' c' /\ Pm (ms_mem (cfg_ms c'))).
Proof.
intros Pm _ fxP d ly Sa Hp W regs0 mem md ch e q v regs W' ly' S' Hp' mem' md' k Qb HPRE Hsp HSV Hgp Htp Hs2 Ha0 HJ
  HWIN HFZ HFK HQ HPM.
eapply (SRrG_mono segs (wle' segs YGcfRehidePost.RZ_cf)).
- apply (vrd_iref92 fxP d ly Sa Hp W regs0 mem md ch e q v regs W' ly' S' Hp' mem' md' k
    (fun ly1 S1 Hp1 W1 regs1 mem1 md1 => Qb ly1 S1 Hp1 W1 regs1 mem1 md1 /\ Pm mem1) HPRE Hsp HSV Hgp Htp Hs2 Ha0 HJ
    HWIN HFZ HFK).
  intros regs' md'' H10 HPR. exact (conj (HQ regs' md'' H10 HPR) HPM).
- intros W'' c' _ H. exact (vrd_fpostWFR_inv (wle' segs YGcfRehidePost.RZ_cf) _ _ _ _ _ _ _ _ _ _ _ _ _ _ H).
Qed.


(* ============================================================================================================== *)
(* D3 / E / F IN THE GENERIC FORM (lane IproE, 2026-10-29). Every new segment lemma below takes
   `forall (Pm : (word -> option byte) -> Prop), srr_inv_laws segs Pm -> .. -> Pm <start memory> ->
    SRr segs W c (fun W' c' => <Q> W' c' /\ Pm (ms_mem (cfg_ms c')))`; the segments here cross no call, so the laws are
   the single srr_inv_laws premise (YC80x.v's record on the old-pin engine set, c-omx-alloc-preset-s1b 459129c18903).
   The runner segment carries Pm by YC1fPx.v's paj_run_to_x_inv; the refusal tail by vrd_iref92 at a body Qb that
   carries Pm of its memory (vrd_fpostWF_inv). The shared ledger records are read through ONE local projection lemma per shape
   (vrd_led_bounds / vrd_led_nodup / vrd_led_hblk), and the shared entry records through vrd_ipre_prj.
   THE RE-HIDING MOVE: these segments start after the first grow, whose text concludes SRr' segs RZ_cf, so each
   concludes SRr' with its journals at wle' (the runners' R forms paj_run_to_x_invR / paj_run_to_xR, the posts'
   fpostWFR, vrd_fpostWFR_inv); the journals are read through the projections ajxR_*.                           *)
(* ============================================================================================================== *)



Definition vrd_ictx (regs : bvmap 5 word) (ch ch2 : list (Z * Z * Z)) : list (list Z) :=
  (raZ regs :: spine ch) :: map (fun k => A_IPC k :: spine ch2) A_IRET_SLOTS.

Lemma vrd_ient_ok_of_ipre : forall d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v ch2,
  vrd_ipre d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v ->
  vrd_ient_ok B ARx (vrd_ictx regs ch ch2) CTX0 CW
    (vrd_ient_of d o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v ch2).
Proof.
intros d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v ch2
  (HPRE & HMN & HCTX & HUC & HCE & HCHI & HQCH & H10 & H11 & H12 & HRD & Hpe & Hop & HROOM & HPKS & HPKL & HFU & HFR & HCWR).
unfold vrd_ient_ok, vrd_ient_of; cbn [ie_ly ie_S ie_Hp ie_W ie_regs ie_mem ie_md ie_ch ie_Lam ie_peak ie_cnt ie_fail
  ie_ran ie_most ie_own ie_e ie_q ie_text ie_len ie_p ie_d ie_tb ie_v ie_o ie_ch2 ie_CW].
split; [exact HPRE|]. split; [exact H10|]. split; [exact H11|]. split; [exact H12|]. split; [exact HRD|].
split; [exact Hpe|]. split; [exact Hop|]. split; [exact HROOM|]. split; [exact (conj HMN (conj HPKS HPKL))|].
split; [left; reflexivity|]. split; [exact HUC|]. split; [exact HCE|]. split; [exact HCHI|]. split; [exact HQCH|].
split; [exact HFU|]. split; [|split; [exact HFR | exact (conj eq_refl HCWR)]].
intros k Hk. right. apply in_map_iff. exists k. split; [reflexivity | exact Hk].
Qed.

Definition ss_g92 : sstate := mkSS (PI_GROWRET - A_prog_base) (sr_set sr_atoms (Z_to_bv 5 10) (SLit 0))
  [ YP09.mkRegion (Some 2%nat) 0 PI_FRAME 8 40 [] ] None (mkFacts [ (2%nat, mkAF (2^46) (2^47) 4) ] [] []).

Lemma vrd_st_g92 : forall (W : world segs) regs0 regs mem,
  spZ regs = spZ regs0 - 144 -> 2 ^ 46 <= spZ regs0 - 144 -> spZ regs0 <= 2 ^ 47 -> spZ regs0 mod 16 = 0 ->
  (forall a, spZ regs0 - 136 <= a < spZ regs0 - 104 -> apresent (w_H W) mem a) ->
  getr regs (Z_to_bv 5 10) = Z_to_bv 64 0 ->
  st_ok_pi segs VAL (vi_EI regs regs0) ss_g92
    (restrict (w_H W) (YK11.mkst regs (Z_to_bv 64 (BASE + (PI_GROWRET - A_prog_base))) mem (YK11.seg_rom segs)))
  /\ sh_ok segs vi_Bx vi_SH (vi_EI regs regs0) (mrestrict (w_H W) mem).
Proof.
intros W regs0 regs mem Hsp Hlo Hhi Hal Hpr Ha0.
assert (Usp : bv_unsigned (ew (vi_EI regs regs0) 2) = spZ regs0 - 144)
  by (rewrite (vi_ew_low regs regs0 2 2%bv eq_refl); exact Hsp).
split; [|unfold sh_ok, vi_SH; apply Forall_nil].
rewrite restrict_mkst_fx.
unfold ss_g92. apply pa_entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | |cbn [sv_denot]; exact Ha0].
  intros H0. apply (f_equal (@bv_unsigned 5)) in H0. vm_compute in H0. discriminate H0.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite Usp. unfold PI_FRAME. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
  intros oo Hoo. apply apresent_writable. apply Hpr. lia.
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- split; [|exact (conj I I)]. cbn [f_atoms atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp. change (2 ^ 4) with 16. split; [lia|]. split; [|lia].
  replace (spZ regs0 - 144) with (spZ regs0 + (-9) * 16) by lia. rewrite Z_mod_plus_full. exact Hal.
Qed.

(* rows 92..107 after a granted first grow: the journal is at wle' (grow's text), the run the runner's R form there *)
Lemma vrd_itail_inv : forall (Pm : (word -> option byte) -> Prop), srr_inv_laws segs Pm ->
  forall d e q v (regs0 regs2 : bvmap 5 word) ly Sa Hp W mem0 md0 W2 ly2 S2 Hp2 mem2 md2 k
    (Q : world segs -> config -> Prop),
  spZ regs2 = spZ regs0 - 144 -> 2 ^ 46 <= spZ regs0 - 144 -> spZ regs0 <= 2 ^ 47 -> spZ regs0 mod 16 = 0 ->
  getr regs2 10 = w64 0 -> getr regs2 20 = w64 v -> getr regs2 26 = w64 SHADOW_OFF -> 4096 <= v -> v + 56 <= 2 ^ 47 ->
  144 <= STK_parse_items d -> 0 <= e ->
  ajournal_xR (SK := SK) segs B prh_pst ARx (wle' segs YGcfRehidePost.RZ_cf) (STK_parse_items d + e) (spZ regs0 + e)
    (rd_fp q v) ly Sa Hp W mem0 md0 [] ly2 S2 Hp2 W2 mem2 md2 k ->
  Pm mem2 ->
  (forall regs' mem' md',
     (forall r, In r [2; 3; 4; 8; 9; 19; 20; 23; 26; 27] -> getr regs' (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)) ->
     getr regs' 18 = w64 (shx (v + 40)) -> getr regs' 21 = w64 32 -> getr regs' 22 = w64 (v + 40) ->
     getr regs' 24 = w64 (v + 24) -> getr regs' 25 = w64 PI_WSMASK ->
     val_mem segs (mrestrict (w_H W2) mem') (spZ regs0 - 136) 8 (bv_unsigned (getr regs2 22)) ->
     val_mem segs (mrestrict (w_H W2) mem') (spZ regs0 - 128) 8 (bv_unsigned (getr regs2 21)) ->
     val_mem segs (mrestrict (w_H W2) mem') (spZ regs0 - 120) 8 (shx (v + 24)) ->
     val_mem segs (mrestrict (w_H W2) mem') (spZ regs0 - 112) 8 (v + 32) ->
     (forall x : word, ~ (spZ regs0 - 136 <= bv_unsigned x < spZ regs0 - 104) -> mem' x = mem2 x) ->
     ajournal_xR (SK := SK) segs B prh_pst ARx (wle' segs YGcfRehidePost.RZ_cf) (STK_parse_items d + e)
       (spZ regs0 + e) (rd_fp q v) ly Sa Hp W mem0 md0 [] ly2 S2 Hp2 W2 mem' md' k ->
     Pm mem' ->
     Q W2 (mkCfg (YK11.mkst regs' (w64 (A_IPC A_IELEM_SLOT)) mem' (YK11.seg_rom segs)) md')) ->
  SRr' segs YGcfRehidePost.RZ_cf W2
    (mkCfg (YK11.mkst regs2 (Z_to_bv 64 (BASE + (PI_GROWRET - A_prog_base))) mem2 (YK11.seg_rom segs)) md2) Q.
Proof.
intros Pm PLAW d e q v regs0 regs2 ly Sa Hp W mem0 md0 W2 ly2 S2 Hp2 mem2 md2 k Q Hsp Hlo Hhi Hal Ha0 H20 H26 Hv1 Hv2
  HSTK He0 HJ HPM HQ.
assert (Hpr : forall a, spZ regs0 - 136 <= a < spZ regs0 - 104 -> apresent (w_H W2) mem2 a).
{ intros a Ha. apply (ajxR_pres HJ). lia. }
destruct (vrd_st_g92 W2 regs0 regs2 mem2 Hsp Hlo Hhi Hal Hpr Ha0) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (vi_EI regs2 regs0)) by (unfold vi_EI; apply Eimg_env).
pose (RUNTO := paj_run_to_x_invR (fx := fx) (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B prh_pst ARx LAWS Pm PLAW
  (wle' segs YGcfRehidePost.RZ_cf) (wle'_refl segs YGcfRehidePost.RZ_cf) (wle'_trans segs YGcfRehidePost.RZ_cf)).
paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM vi_Bspan (PI_ELEM - A_prog_base).

{ intros a (r & Hin & Ha). cbn [ss_g92 ss_mem In] in Hin. destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  rewrite (vi_ew_low regs2 regs0 2 2%bv eq_refl) in Ha. change (bv_unsigned (getr regs2 2%bv)) with (spZ regs2) in Ha.
  left. lia. }
assert (Usp2 : bv_unsigned (ew (vi_EI regs2 regs0) 2) = spZ regs0 - 144)
  by (rewrite (vi_ew_low regs2 regs0 2 2%bv eq_refl); exact Hsp).
assert (E20 : ew (vi_EI regs2 regs0) 20 = w64 v) by (rewrite (vi_ew_low regs2 regs0 20 20%bv eq_refl); exact H20).
assert (E26 : ew (vi_EI regs2 regs0) 26 = w64 SHADOW_OFF)
  by (rewrite (vi_ew_low regs2 regs0 26 26%bv eq_refl); exact H26).
assert (HK : forall x : word, ~ (spZ regs0 - 136 <= bv_unsigned x < spZ regs0 - 104) -> ms_mem ms x = mem2 x).
{ intros x Hx. apply HF. intros (r & Hin & Ha). cbn [ss_g92 ss_mem In] in Hin. destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite Usp2 in Ha. apply Hx. lia. }
assert (HKr : forall r, In r [2; 3; 4; 8; 9; 19; 20; 23; 26; 27] ->
  getr (ms_regs ms) (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)).
{ intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr];
    [match goal with |- getr _ (Z_to_bv 5 ?n) = _ =>
       let Hr0 := fresh "Hr0" in vi_reg HS (Z_to_bv 5 n) Hr0; rewrite Hr0; apply vi_ew_low; reflexivity end|]).
  destruct Hr. }

assert (R18 : getr (ms_regs ms) 18 = w64 (shx (v + 40))).
{ pose proof (st_ok_pi_restrict_reg _ _ _ _ (Z_to_bv 5 18) HS) as R.
  change (sr_get _ (Z_to_bv 5 18)) with (SAlu ALU_ADD (SAlu ALU_SRL (SOff 20 40) (SLit 3)) (SOff 26 0)) in R.
  rewrite denot_lit_U, (vrd_U_shxm _ 20 26 40 v E20 E26 ltac:(lia) ltac:(lia)) in R. exact R. }

assert (OF20 : forall kk, 0 <= v + kk < 2 ^ 64 -> sv_denot (vi_EI regs2 regs0) (SOff 20 kk) = w64 (v + kk)).
{ intros kk Hkk. rewrite denot_lit_U, U_SOff, E20. unfold w64. rewrite unsigned_lit_small by lia.
  rewrite zcanon_id by (unfold M64; lia). reflexivity. }
assert (R21 : getr (ms_regs ms) 21 = w64 32).
{ pose proof (st_ok_pi_restrict_reg _ _ _ _ (Z_to_bv 5 21) HS) as R.
  change (sr_get _ (Z_to_bv 5 21)) with (SLit 32) in R. exact R. }
assert (R22 : getr (ms_regs ms) 22 = w64 (v + 40)).
{ pose proof (st_ok_pi_restrict_reg _ _ _ _ (Z_to_bv 5 22) HS) as R.
  change (sr_get _ (Z_to_bv 5 22)) with (SOff 20 40) in R. rewrite (OF20 40) in R by lia. exact R. }
assert (R24 : getr (ms_regs ms) 24 = w64 (v + 24)).
{ pose proof (st_ok_pi_restrict_reg _ _ _ _ (Z_to_bv 5 24) HS) as R.
  change (sr_get _ (Z_to_bv 5 24)) with (SOff 20 24) in R. rewrite (OF20 24) in R by lia. exact R. }
assert (R25 : getr (ms_regs ms) 25 = w64 PI_WSMASK).
{ pose proof (st_ok_pi_restrict_reg _ _ _ _ (Z_to_bv 5 25) HS) as R.
  change (sr_get _ (Z_to_bv 5 25)) with (SLit PI_WSMASK) in R. exact R. }

assert (Hb22 : 0 <= bv_unsigned (getr regs2 22%bv) < 2 ^ 64)
  by (pose proof (bv_unsigned_in_range 64 (getr regs2 22%bv)) as Hb; change (bv_modulus 64) with (2 ^ 64) in Hb; exact Hb).
assert (Hb21 : 0 <= bv_unsigned (getr regs2 21%bv) < 2 ^ 64)
  by (pose proof (bv_unsigned_in_range 64 (getr regs2 21%bv)) as Hb; change (bv_modulus 64) with (2 ^ 64) in Hb; exact Hb).
assert (C8 : val_mem segs (mrestrict (w_H W2) (ms_mem ms)) (spZ regs0 - 136) 8 (bv_unsigned (getr regs2 22))).
{ vrd_chunkH HS ms (w_H W2) 0%nat 8 8%N (SOff 22 0) (bv_unsigned (getr regs2 22)) VQ.
  specialize (VQ ltac:(cbn [sv_denot]; rewrite (vi_ew_low regs2 regs0 22 22%bv eq_refl), Z.add_0_r; reflexivity)
    ltac:(cbn; lia) ltac:(lia)).
  cbn [base_val YP09.r_base] in VQ. rewrite Usp2 in VQ. replace (spZ regs0 - 144 + 8) with (spZ regs0 - 136) in VQ by lia.
  exact VQ. }

assert (C16 : val_mem segs (mrestrict (w_H W2) (ms_mem ms)) (spZ regs0 - 128) 8 (bv_unsigned (getr regs2 21))).
{ vrd_chunkH HS ms (w_H W2) 0%nat 16 8%N (SOff 21 0) (bv_unsigned (getr regs2 21)) VQ.
  specialize (VQ ltac:(cbn [sv_denot]; rewrite (vi_ew_low regs2 regs0 21 21%bv eq_refl), Z.add_0_r; reflexivity)
    ltac:(cbn; lia) ltac:(lia)).
  cbn [base_val YP09.r_base] in VQ. rewrite Usp2 in VQ. replace (spZ regs0 - 144 + 16) with (spZ regs0 - 128) in VQ by lia.
  exact VQ. }
assert (C24 : val_mem segs (mrestrict (w_H W2) (ms_mem ms)) (spZ regs0 - 120) 8 (shx (v + 24))).
{ assert (Hsh : 0 <= shx (v + 24) < 2 ^ 64).
  { unfold shx, SHADOW_OFF. assert (0 <= (v + 24) / 8 <= 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia). lia. }
  vrd_chunkH HS ms (w_H W2) 0%nat 24 8%N (SAlu ALU_ADD (SAlu ALU_SRL (SOff 20 24) (SLit 3)) (SOff 26 0)) (shx (v + 24)) VQ.
  specialize (VQ ltac:(rewrite denot_lit_U, (vrd_U_shxm _ 20 26 24 v E20 E26 ltac:(lia) ltac:(lia)); reflexivity)
    ltac:(cbn; lia) ltac:(lia)).
  cbn [base_val YP09.r_base] in VQ. rewrite Usp2 in VQ. replace (spZ regs0 - 144 + 24) with (spZ regs0 - 120) in VQ by lia.
  exact VQ. }
assert (C32 : val_mem segs (mrestrict (w_H W2) (ms_mem ms)) (spZ regs0 - 112) 8 (v + 32)).
{ vrd_chunkH HS ms (w_H W2) 0%nat 32 8%N (SOff 20 32) (v + 32) VQ.
  specialize (VQ ltac:(rewrite (OF20 32) by lia; reflexivity) ltac:(cbn; lia) ltac:(lia)).
  cbn [base_val YP09.r_base] in VQ. rewrite Usp2 in VQ. replace (spZ regs0 - 144 + 32) with (spZ regs0 - 112) in VQ by lia.
  exact VQ. }
pmkst HS. apply (SRrG_ret segs (wle' segs YGcfRehidePost.RZ_cf) (wle'_refl segs YGcfRehidePost.RZ_cf)).
apply (HQ (ms_regs ms) (ms_mem ms) _ HKr R18 R21 R22 R24 R25 C8 C16 C24 C32 HK HJ HPM).
Qed.


Lemma vrd_gfp0 : forall (o : bool) v a, inFP (vrd_gfp (if o then 6 else 5) 0 0 0 v) a -> v <= a < v + 56.
Proof.
intros o v a (r & Hin & Hr). unfold vrd_gfp in Hin.
destruct o; cbn [kids_blkR keys_blkR app prhReader_ab ablocks_fp map Z.eqb orb negb In] in Hin;
  (destruct Hin as [<- | [<- | []]]; cbn [fst snd] in Hr; lia).
Qed.

Ltac vrd_cs := match goal with |- acallee_saved (bv_unsigned ?r) =>
  let z := eval vm_compute in (bv_unsigned r) in change (bv_unsigned r) with z; unfold acallee_saved; lia end.

(* the facts at row 92 every arm reads, from the call's re-entry facts, the journal (at wle', after grow's text), the
   agreement clause and the callee-saved registers vrd_call_WR returns *)
Lemma vrd_after92 : forall d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v
    P regsC MC mdc W2 ly2 S2 Hp2 regs2 mem2 md2 k,
  vrd_ipre d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v ->
  vrd_imid d o e q text len v regs0 ly Sa Hp W mem0 md0 P regsC MC mdc ->
  ajournal_xR (SK := SK) segs B prh_pst ARx (wle' segs YGcfRehidePost.RZ_cf) (STK_parse_items d + e) (spZ regs0 + e)
    (rd_fp q v) ly Sa Hp W mem0 md0 [] ly2 S2 Hp2 W2 mem2 md2 k ->
  (forall a, spZ regs0 + e + - (e + 144) <= a < spZ regs0 + e -> ~ inFP (vrd_gfp (if o then 6 else 5) 0 0 0 v) a ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W) MC a) ->
  aregs_preserved regsC regs2 ->
  spZ regs2 = spZ regs0 - 144 /\ vi_saved W2 mem2 regs0 /\
  getr regs2 3 = w64 (as_gp B) /\ getr regs2 4 = w64 (as_tp B) /\ getr regs2 18 = w64 (-1) /\
  getr regs2 8 = w64 q /\ getr regs2 9 = w64 (q + 16) /\ getr regs2 19 = w64 (if o then 1 else 0) /\
  getr regs2 20 = w64 v /\ getr regs2 21 = w64 (shx (q + 16)) /\ getr regs2 22 = w64 (q + 8) /\
  getr regs2 23 = w64 (shx (q + 8)) /\ getr regs2 26 = w64 SHADOW_OFF /\ getr regs2 27 = w64 (shx q) /\
  (forall a, spZ regs0 <= a < spZ regs0 + e -> ~ inFP (rd_fp q v) a ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W) mem0 a) /\
  val_mem segs (mrestrict (w_H W2) mem2) q 8 P /\ val_mem segs (mrestrict (w_H W2) mem2) (q + 8) 8 (text + len) /\
  val_mem segs (mrestrict (w_H W2) mem2) (q + 16) 4 (Z.of_nat d + 1) /\ rd_rw segs (mrestrict (w_H W2) mem2) q 24 /\
  (forall a, spZ regs0 - STK_parse_items d <= a < spZ regs0 + e -> apresent (w_H W2) mem2 a) /\
  (forall a, spZ regs0 - 144 <= a < spZ regs0 + e -> ~ (v <= a < v + 56) ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W) MC a).
Proof.
intros d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v P regsC MC mdc W2 ly2 S2 Hp2
  regs2 mem2 md2 k HPRE HMID HJ1 HWIN2 HPR.
pose proof (vrd_ipre_prj d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v HPRE)
  as (HAFN & HROD & Hshi64 & Hfrm & HAR & Hal16 & Hceil & Hslo & Hshi & H47 & Htop & Htop' & Hpres & He0 & He16 & Hetop &
      Hepres & Hspq & Hqe & Hq8 & Ht0 & Ht62 & Htp & Hlen & Hqt & Hd32 & Hv4096 & Hv8 & HAMv & HNv & HRAv & HZv & Hrwv &
      HATv & Hqv & Htv & Hvw & HLED & HdM & Hcnt & HSRC & HHOME & HRAq & HCE & H10 & H11 & H12 & Hpe & Hop & HROOM & HFR).
pose proof (vrd_stk_ge d) as HSTK. pose proof H_img as (Himg1 & Himg2 & Himg3). unfold PI_FRAME in HSTK.
pose proof HMID as (HAT & Hgp1 & Htp1 & H18 & H20 & Vty & KM & KG & HJ).
pose proof HAT as (Hsp & Hs1 & Hs2 & Hs16 & H8 & H26 & Hq1 & Hq2 & Hq3 & Hq8' & H9 & H21 & H22 & H23 & H27 & H11' & Hd &
  H19 & H12' & He & HP1 & HP2 & HSV & Vq & Vq8 & Vq16 & RWq & RAq).
assert (KR : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr regsC r)
  by (intros r Hr; exact (vi_kept regsC regs2 r HPR Hr)).
assert (Hpr2 : forall a, spZ regs0 - STK_parse_items d <= a < spZ regs0 + e -> apresent (w_H W2) mem2 a).
{ intros a Ha. apply (ajxR_pres HJ1). lia. }
assert (HFV : forall a, spZ regs0 - 144 <= a < spZ regs0 + e -> ~ (v <= a < v + 56) ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W) MC a).
{ intros a Ha Hn. apply HWIN2; [lia|]. intros Hin. exact (Hn (vrd_gfp0 o v a Hin)). }
assert (Hq : forall a (n : nat) vv, q <= a -> a + Z.of_nat n <= q + 24 ->
  val_mem segs (mrestrict (w_H W) MC) a n vv -> val_mem segs (mrestrict (w_H W2) mem2) a n vv).
{ intros a n vv H1 H2 Hv. apply (vi_vm_aview (w_H W) (w_H W2) MC mem2); [|exact Hv].
  intros kk Hkk. apply HFV; lia. }
split.
{ unfold spZ. rewrite (KR 2%bv ltac:(vrd_cs)). exact Hsp. }
split.
{ intros j Hj. apply (vi_vm_aview (w_H W) (w_H W2) MC mem2); [|exact (HSV j Hj)].
  intros kk Hkk. apply HFV; [lia|]. intros Hv. apply (proj2 (HNv _ Hv)). lia. }
split; [rewrite (KR 3%bv ltac:(vrd_cs)); exact Hgp1|].
split; [rewrite (KR 4%bv ltac:(vrd_cs)); exact Htp1|].
split; [rewrite (KR 18%bv ltac:(vrd_cs)); exact H18|].
split; [rewrite (KR 8%bv ltac:(vrd_cs)); exact H8|].
split; [rewrite (KR 9%bv ltac:(vrd_cs)); exact H9|].
split; [rewrite (KR 19%bv ltac:(vrd_cs)); exact H19|].
split; [rewrite (KR 20%bv ltac:(vrd_cs)); exact H20|].
split; [rewrite (KR 21%bv ltac:(vrd_cs)); exact H21|].
split; [rewrite (KR 22%bv ltac:(vrd_cs)); exact H22|].
split; [rewrite (KR 23%bv ltac:(vrd_cs)); exact H23|].
split; [rewrite (KR 26%bv ltac:(vrd_cs)); exact H26|].
split; [rewrite (KR 27%bv ltac:(vrd_cs)); exact H27|].
split.
{ intros a Ha Hn. rewrite (HFV a ltac:(lia)).
  - unfold aview, mbyte. rewrite KM; [reflexivity|]. rewrite unsigned_lit_small by lia.
    unfold pi_wr, PI_FRAME. intros [H|[H|[H|H]]]; [lia| | |]; apply Hn; unfold rd_fp, inFP.
    + exists (q, q + 8). split; [left; reflexivity | cbn [fst snd]; lia].
    + exists (q + 16, q + 20). split; [right; left; reflexivity | cbn [fst snd]; lia].
    + exists (v, v + 56). split; [right; right; left; reflexivity | cbn [fst snd]; lia].
  - intros Hv. apply Hn. exists (v, v + 56). split; [right; right; left; reflexivity | cbn [fst snd]; lia]. }
split; [apply Hq; [lia | cbn; lia | exact Vq]|].
split; [apply Hq; [lia | cbn; lia | exact Vq8]|].
split; [apply Hq; [lia | cbn; lia | exact Vq16]|].
split; [intros x Hx; apply apresent_writable; apply Hpr2; lia|].
split; [exact Hpr2 | exact HFV].
Qed.



(* D3's REFUSAL TAIL in the generic form: row 92 with a0 = -1 after the first grow (its four refusing arms), the
   model's refusal package of the arm, to the record post (vrd_iref92, vrd_iret) and P of the returned memory; after
   grow's text the journal is at wle' and the tail concludes SRr' *)
Lemma vrd_iref_inv : forall (Pm : (word -> option byte) -> Prop)
    d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v
    P regsC MC mdc W2 ly2 S2 Hp2 regs2 mem2 md2 k1 ok tr okr D Lam' peak' cnt' fail' ran',
  vrd_ipre d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v ->
  vrd_imid d o e q text len v regs0 ly Sa Hp W mem0 md0 P regsC MC mdc ->
  p + 1 <= P <= text + len ->
  ajournal_xR (SK := SK) segs B prh_pst ARx (wle' segs YGcfRehidePost.RZ_cf) (STK_parse_items d + e) (spZ regs0 + e)
    (rd_fp q v) ly Sa Hp W mem0 md0 [] ly2 S2 Hp2 W2 mem2 md2 (0 + k1) ->
  (forall a, spZ regs0 + e + - (e + 144) <= a < spZ regs0 + e -> ~ inFP (vrd_gfp (if o then 6 else 5) 0 0 0 v) a ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W) MC a) ->
  aregs_preserved regsC regs2 -> getr regs2 10 = w64 (-1) ->
  jr_items prh_jr_strtod d o (rest_atR tb text p) ok = (None, tr, okr) ->
  prh_ledger B ly2 S2 Hp2 W2 mem2 Lam' peak' cnt' fail' ran' most own -> room_live_cf S2 ->
  (* the hull use over the call's all-granted events (the post's conjunct) *)
  PresetHullBudget.hull_used Sa S2 (PresetReqAt.rd_hevs (prhPi_gtrace d o (rest_atR tb text p))) ->
  (* the live requests and the position moved by the arm's events, from the call's entry state *)
  Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S2))
    (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf Sa)) (PresetReqAt.rd_hevs tr)) ->
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist Sa ->
     PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs tr) ->
     exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (PresetReqAt.rd_hevs tr))%nat H0 hist' S2) ->
  (* the refusal's exclusion: no run at the call's granted events, consumer allocations and no chosen failure in
     the window, meets this arm (so the OUTCOME clause holds vacuously) *)
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist Sa ->
     PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs (prhPi_gtrace d o (rest_atR tb text p))) ->
     PRH_Base.prh_cons_from sm x os i (length (PresetReqAt.rd_hevs (prhPi_gtrace d o (rest_atR tb text p)))) ->
     (fail < cnt \/ cnt + Z.of_nat (PjGrammar.calls (prhPi_gtrace d o (rest_atR tb text p))) <= fail) -> False) ->
  (* the outcome of an injected reading at this arm (the post's conjunct): every refused call of the arm is the
     chosen failure, at a model run under the model's grant list with the failure chosen inside the call's window *)
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist Sa ->
     PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs (snd (fst (jr_items prh_jr_strtod d o
       (rest_atR tb text p) (PresetReqAt.okk (Z.to_nat (fail - cnt))))))) ->
     PRH_Base.prh_cons_from sm x os i (length (PresetReqAt.rd_hevs (snd (fst (jr_items prh_jr_strtod d o
       (rest_atR tb text p) (PresetReqAt.okk (Z.to_nat (fail - cnt)))))))) ->
     cnt <= fail < cnt + Z.of_nat (PjGrammar.calls (prhPi_gtrace d o (rest_atR tb text p))) ->
     PRH_Base.prh_granted ok cnt fail (PjGrammar.calls tr)) ->
  rd_ledger_move Lam peak cnt fail ran most ok (prhPi_gtrace d o (rest_atR tb text p)) tr D Lam' peak' cnt' fail'
    ran' ->
  rd_blocks_move B ly Sa ly2 S2 D tr (rest_atR tb text p) d ->
  blocks_bytes S2 <= blocks_bytes Sa + prh_held tr -> Ledger.lsum D = PjGrammar.held tr ->
  pj_fdR segs (mrestrict (w_H W2) mem2) (prh_lin Lam') (PjGrammar.MAXD - d) v D ->
  (* The kit's cut (FREEORD-NONE): the refused arm's order list, the post's None-arm conjunct *)
  (cf_head = PresetReqAt.HEAD -> forall n, (PjGrammar.MAXD - d <= n)%nat ->
     exists F, PRH_PjOrder.pj_foR segs (mrestrict (w_H W2) mem2) (prh_lin Lam') n v D F /\
       map (fun b => snd b + cf_head) F = prhPi_frees d o (rest_atR tb text p) ok) ->
  Pm mem2 ->
  SRr' segs YGcfRehidePost.RZ_cf W2
    (mkCfg (YK11.mkst regs2 (Z_to_bv 64 (BASE + (PI_GROWRET - A_prog_base))) mem2 (YK11.seg_rom segs)) md2)
    (fun W' c' => vrd_iQall d o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v W' c' /\
       Pm (ms_mem (cfg_ms c'))).
Proof.
intros Pm d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v P regsC MC mdc W2 ly2 S2
  Hp2 regs2 mem2 md2 k1 ok tr okr D Lam' peak' cnt' fail' ran' HPRE HMID HP HJ1 HWIN2 HPR Ha0 Hjr HLED2 Hrl2 HHU HLV HXF
  HEX HINJ HLM HBM Hbb Hls Hfd HFO HPM.
destruct (vrd_after92 d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v P regsC MC mdc W2
  ly2 S2 Hp2 regs2 mem2 md2 (0 + k1) HPRE HMID HJ1 HWIN2 HPR)
  as (Hsp2 & HSV2 & Hgp2 & Htp2 & H182 & H82 & H92 & H192 & H202 & H212 & H222 & H232 & H262 & H272 & HWINe & Vq2 &
      Vq82 & Vq162 & RWq2 & Hpr2 & HFV).
pose proof (vrd_ipre_prj d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v HPRE)
  as (HAFN & HROD & Hshi64 & Hfrm & HAR & Hal16 & Hceil & Hslo & Hshi & H47 & Htop & Htop' & Hpres & He0 & He16 & Hetop &
      Hepres & Hspq & Hqe & Hq8 & Ht0 & Ht62 & Htp & Hlen & Hqt & Hd32 & Hv4096 & Hv8 & HAMv & HNv & HRAv & HZv & Hrwv &
      HATv & Hqv & Htv & Hvw & HLED & HdM & Hcnt & HSRC & HHOME & HRAq & HCE & H10 & H11 & H12 & Hpe & Hop & HROOM & HFR).
eapply (SRrG_mono segs (wle' segs YGcfRehidePost.RZ_cf)).
- apply (vrd_iref92 fx d ly Sa Hp W regs0 mem0 md0 ch e q v regs2 W2 ly2 S2 Hp2 mem2 md2 (0 + k1)
    (fun ly' Sb Hp' W' regs' mem' md' =>
       vrd_ipost_body d o q v text len p tb ly Sa Lam peak cnt fail ran most own ly' Sb Hp' W' regs' mem' md' /\ Pm mem')
    HAFN Hsp2 HSV2 Hgp2 Htp2 H182 Ha0 HJ1 HWINe Hfrm (fun r _ => eq_refl)).
  intros regs' md'' H10' HPR'. split; [|exact HPM].
  unfold vrd_ipost_body, vrd_items_q, tpiP_Q.
  exists ok, None, tr, okr, D, Lam', peak', cnt', fail', ran'.
  split; [rewrite vrd_strtod_same; exact Hjr|]. split; [exact HLED2|]. split; [exact Hrl2|]. split; [exact HHU|].
  split; [exact HLV|]. split; [exact HXF|].
  split; [intros sm x0 os i H0 hist HP0 HR0 HC0 HW0; exfalso; exact (HEX sm x0 os i H0 hist HP0 HR0 HC0 HW0)|].
  split; [exact HINJ|].
  split; [exact HLM|].
  split; [exact HBM|]. split; [exact Hbb|]. split; [exact Hls|].
  split; [exact H10'|]. split; [exact HFO|]. split; [|exact Hfd].
  exists P, (Z.of_nat d + 1). split; [lia|]. split; [lia|].
  split; [exact Vq2|]. split; [exact Vq82|]. split; [exact Vq162 | exact RWq2].
- intros W' c' _ H.
  destruct (vrd_fpostWFR_inv (wle' segs YGcfRehidePost.RZ_cf) _ _ _ _ _ _ _ _ _ _ _ _ _ _ H) as [H1 H2].
  split; [right; apply (vrd_fpostWFb_ofR (wle' segs YGcfRehidePost.RZ_cf) (fun _ _ H => H));
    [exact (vrd_wbudget_nil CW) | exact H1] | exact H2].
Qed.





(* D3, grow's arms 2 and 3 (the kids realloc refused: set to fail, or the allocator's NULL): the model refuses with
   [EFail 448] on ok = [false], nothing was allocated, the node is the typed zero node *)
Lemma vrd_iref_kids : forall (Pm : (word -> option byte) -> Prop)
    d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v
    P regsC MC mdc W2 ly2 S2 Hp2 regs2 mem2 md2 k1 peak' cnt' fail' ran',
  vrd_ipre d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v ->
  (d < PjGrammar.MAXD)%nat ->
  vrd_imid d o e q text len v regs0 ly Sa Hp W mem0 md0 P regsC MC mdc ->
  p + 1 <= P <= text + len ->
  (forall r, PjGrammar.skip (tl (rest_atR tb text p)) <> PjGrammar.closer o :: r) ->
  ajournal_xR (SK := SK) segs B prh_pst ARx (wle' segs YGcfRehidePost.RZ_cf) (STK_parse_items d + e) (spZ regs0 + e)
    (rd_fp q v) ly Sa Hp W mem0 md0 [] ly2 S2 Hp2 W2 mem2 md2 (0 + k1) ->
  ajournal_xR (SK := SK) segs B prh_pst ARx (wle' segs YGcfRehidePost.RZ_cf) (STK_grow + (e + 144)) (spZ regs0 + e)
    (vrd_gfp (if o then 6 else 5) 0 0 0 v) ly Sa Hp W MC mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  (forall a, spZ regs0 + e + - (e + 144) <= a < spZ regs0 + e -> ~ inFP (vrd_gfp (if o then 6 else 5) 0 0 0 v) a ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W) MC a) ->
  aregs_preserved regsC regs2 ->
  getr regs2 10 = w64 (-1) -> ablocks B ly2 S2 = ablocks B ly Sa -> blocks_bytes S2 = blocks_bytes Sa ->
  prh_ledger B ly2 S2 Hp2 W2 mem2 Lam peak' cnt' fail' ran' most own ->
  pj_hdrR segs (mrestrict (w_H W2) mem2) v (if o then 6 else 5) 0 0 0 0 0 0 ->
  room_live_cf S2 ->
  (* grow's hull use over its all-granted events *)
  PresetHullBudget.hull_used Sa S2 (prhPg_evs ((if o then 6 else 5) =? 6) 0 0 []) ->
  (* grow's arm: no event (outcomes [false]), the live requests and the position kept *)
  Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S2))
    (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf Sa))
       (prhPg_evs ((if o then 6 else 5) =? 6) 0 0 [false])) ->
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist Sa ->
     PRH_Base.prh_run_at sm x os i (prhPg_evs ((if o then 6 else 5) =? 6) 0 0 [false]) ->
     exists hist', PresetRoomPos.iface_room_pos sm x os
       (i + length (prhPg_evs ((if o then 6 else 5) =? 6)%Z 0 0 [false]))%nat H0 hist' S2) ->
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist Sa ->
     PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs (prhPi_gtrace d o (rest_atR tb text p))) ->
     PRH_Base.prh_cons_from sm x os i (length (PresetReqAt.rd_hevs (prhPi_gtrace d o (rest_atR tb text p)))) ->
     (fail < cnt \/ cnt + Z.of_nat (PjGrammar.calls (prhPi_gtrace d o (rest_atR tb text p))) <= fail) -> False) ->
  (* the outcome of an injected reading at this arm (the post's conjunct at ok = [false]) *)
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist Sa ->
     PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs (snd (fst (jr_items prh_jr_strtod d o
       (rest_atR tb text p) (PresetReqAt.okk (Z.to_nat (fail - cnt))))))) ->
     PRH_Base.prh_cons_from sm x os i (length (PresetReqAt.rd_hevs (snd (fst (jr_items prh_jr_strtod d o
       (rest_atR tb text p) (PresetReqAt.okk (Z.to_nat (fail - cnt)))))))) ->
     cnt <= fail < cnt + Z.of_nat (PjGrammar.calls (prhPi_gtrace d o (rest_atR tb text p))) ->
     PRH_Base.prh_granted [false] cnt fail (PjGrammar.calls [PjGrammar.EFail 448])) ->
  rd_ledger_move Lam peak cnt fail ran most [false] (prhPi_gtrace d o (rest_atR tb text p)) [PjGrammar.EFail 448] []
    Lam peak' cnt' fail' ran' ->
  Pm mem2 ->
  SRr' segs YGcfRehidePost.RZ_cf W2
    (mkCfg (YK11.mkst regs2 (Z_to_bv 64 (BASE + (PI_GROWRET - A_prog_base))) mem2 (YK11.seg_rom segs)) md2)
    (fun W' c' => vrd_iQall d o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v W' c' /\
       Pm (ms_mem (cfg_ms c'))).
Proof.
intros Pm d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v P regsC MC mdc W2 ly2 S2
  Hp2 regs2 mem2 md2 k1 peak' cnt' fail' ran' HPRE Hd HMID HP Hnc HJ1 HJ2 HWIN2 HPR Ha0 Eab Ebb HLED2 Hhdr2 Hrl2 HHUg
  HLVg HXFg HEX HINJ HLM HPM.
pose proof (vrd_ipre_prj d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v HPRE)
  as (HAFN & HROD & Hshi64 & Hfrm & HAR & Hal16 & Hceil & Hslo & Hshi & H47 & Htop & Htop' & Hpres & He0 & He16 & Hetop &
      Hepres & Hspq & Hqe & Hq8 & Ht0 & Ht62 & Htp & Hlen & Hqt & Hd32 & Hv4096 & Hv8 & HAMv & HNv & HRAv & HZv & Hrwv &
      HATv & Hqv & Htv & Hvw & HLED & HdM & Hcnt & HSRC & HHOME & HRAq & HCE & H10 & H11 & H12 & Hpe & Hop & HROOM & HFR).
destruct (vrd_led_bounds _ _ _ _ _ _ _ _ _ _ _ _ HLED) as (HLp & HLpk & HLc & HLf & HLr).
pose proof (ajxR_frs HJ2) as Hfrs2.
pose proof (@cf_head_nonneg cp) as Hcf0.
apply (vrd_iref_inv Pm d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v P regsC MC mdc
  W2 ly2 S2 Hp2 regs2 mem2 md2 k1 [false] [PjGrammar.EFail 448] [] [] Lam peak' cnt' fail' ran'
  HPRE HMID HP HJ1 HWIN2 HPR Ha0); [ | exact HLED2 | exact Hrl2
  | exact (vrd_hull_gtrace d o (rest_atR tb text p) Sa S2 Hd Hnc HHUg) | exact HLVg | exact HXFg | exact HEX | exact HINJ
  | exact HLM
  | | | | | | exact HPM].
- exact (vrd_items_kids_fail d o (rest_atR tb text p) [] Hd Hnc).
- split; [intros a k Hin; destruct Hin|].
  split; [rewrite Eab; apply Permutation_refl|].
  split; [rewrite Hfrs2; apply Permutation_refl|]. cbn [hpeakR PjGrammar.held_ev]. lia.
- rewrite Ebb. unfold prh_held. cbn [PjGrammar.held PjGrammar.held_ev PjGrammar.calls PjGrammar.is_call Z.of_nat]. lia.
- reflexivity.
- exact (vrd_hdr_fd _ _ v (if o then 6 else 5) _ Hhdr2).
- (* The kit's cut: no block, the order list empty, as the model's (gheld's default arm at cap 0) *)
  intros _ n _. exists []. split; [exact (vrd_hdr_fo _ _ v (if o then 6 else 5) n Hhdr2)|].
  rewrite (vrd_frees_kids_fail d o (rest_atR tb text p) [] Hd Hnc). reflexivity.
Qed.

(* D3, grow's arms 5 and 6 (an object: the kids realloc granted to k', the keys realloc refused - set to fail, or
   the allocator's NULL): the model refuses with [EGrow 0 448; EFail 64] on ok = [true; false], the position owns the
   new kids block, the node holds k' with cap still 0. HMODE is the arm's ledger, as grow's text states it: the chosen
   failure at the keys call (cnt + 1 = fail) or the refusal (g_peak to the refused keys request's live count,
   g_ran_out set when its 64 bytes are at most g_most) *)
Lemma vrd_iref_keys : forall (Pm : (word -> option byte) -> Prop)
    d CTX ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v
    P regsC MC mdc W2 ly2 S2 Hp2 regs2 mem2 md2 k1 k' Lam' peak' cnt' fail' ran',
  vrd_ipre d CTX true ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v ->
  (d < PjGrammar.MAXD)%nat ->
  vrd_imid d true e q text len v regs0 ly Sa Hp W mem0 md0 P regsC MC mdc ->
  p + 1 <= P <= text + len ->
  (forall r, PjGrammar.skip (tl (rest_atR tb text p)) <> PjGrammar.closer true :: r) ->
  ajournal_xR (SK := SK) segs B prh_pst ARx (wle' segs YGcfRehidePost.RZ_cf) (STK_parse_items d + e) (spZ regs0 + e)
    (rd_fp q v) ly Sa Hp W mem0 md0 [] ly2 S2 Hp2 W2 mem2 md2 (0 + k1) ->
  ajournal_xR (SK := SK) segs B prh_pst ARx (wle' segs YGcfRehidePost.RZ_cf) (STK_grow + (e + 144)) (spZ regs0 + e)
    (vrd_gfp 6 0 0 0 v) ly Sa Hp W MC mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  (forall a, spZ regs0 + e + - (e + 144) <= a < spZ regs0 + e -> ~ inFP (vrd_gfp 6 0 0 0 v) a ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W) MC a) ->
  aregs_preserved regsC regs2 ->
  getr regs2 10 = w64 (-1) -> cnt <> fail ->
  prhReader_swap B ly Sa Hp Lam ly2 S2 Hp2 Lam' (kids_blkR 0 0) [(k', 56 * cap2R 0)] ->
  prh_ledger B ly2 S2 Hp2 W2 mem2 Lam' peak' cnt' fail' ran' most own ->
  ((cnt + 1 = fail /\ peak' = Z.max peak (Ledger.lsum Lam') /\ cnt' = cnt + 2 /\ fail' = SIZE_MAXZ /\ ran' = ran) \/
   (cnt + 1 <> fail /\
    peak' = (if 0 =? 0 then Z.max (Z.max peak (Ledger.lsum Lam')) (Z.min SIZE_MAXZ (Ledger.lsum Lam' + 8 * cap2R 0))
             else Z.max (Z.max peak (Ledger.lsum Lam')) (Z.min SIZE_MAXZ (Ledger.lsum Lam' - 8 * 0 + 8 * cap2R 0))) /\
    cnt' = (cnt + 1 + 1) mod 2 ^ 64 /\ fail' = fail /\ ran' = (if 8 * cap2R 0 <=? most then 1 else ran))) ->
  pj_hdrR segs (mrestrict (w_H W2) mem2) v 6 0 0 k' 0 0 0 ->
  room_live_cf S2 ->
  (* grow's hull use over its all-granted events *)
  PresetHullBudget.hull_used Sa S2 (prhPg_evs (6 =? 6) 0 0 []) ->
  (* grow's arm: the kids realloc's event (outcomes [true; false]) *)
  Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S2))
    (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf Sa)) (prhPg_evs (6 =? 6) 0 0 [true; false])) ->
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist Sa ->
     PRH_Base.prh_run_at sm x os i (prhPg_evs (6 =? 6) 0 0 [true; false]) ->
     exists hist', PresetRoomPos.iface_room_pos sm x os
       (i + length (prhPg_evs (6 =? 6)%Z 0 0 [true; false]))%nat H0 hist' S2) ->
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist Sa ->
     PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs (prhPi_gtrace d true (rest_atR tb text p))) ->
     PRH_Base.prh_cons_from sm x os i (length (PresetReqAt.rd_hevs (prhPi_gtrace d true (rest_atR tb text p)))) ->
     (fail < cnt \/ cnt + Z.of_nat (PjGrammar.calls (prhPi_gtrace d true (rest_atR tb text p))) <= fail) -> False) ->
  (* the outcome of an injected reading at this arm (the post's conjunct at ok = [true; false]) *)
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist Sa ->
     PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs (snd (fst (jr_items prh_jr_strtod d true
       (rest_atR tb text p) (PresetReqAt.okk (Z.to_nat (fail - cnt))))))) ->
     PRH_Base.prh_cons_from sm x os i (length (PresetReqAt.rd_hevs (snd (fst (jr_items prh_jr_strtod d true
       (rest_atR tb text p) (PresetReqAt.okk (Z.to_nat (fail - cnt)))))))) ->
     cnt <= fail < cnt + Z.of_nat (PjGrammar.calls (prhPi_gtrace d true (rest_atR tb text p))) ->
     PRH_Base.prh_granted [true; false] cnt fail
       (PjGrammar.calls [PjGrammar.EGrow 0 448; PjGrammar.EFail 64])) ->
  Pm mem2 ->
  SRr' segs YGcfRehidePost.RZ_cf W2
    (mkCfg (YK11.mkst regs2 (Z_to_bv 64 (BASE + (PI_GROWRET - A_prog_base))) mem2 (YK11.seg_rom segs)) md2)
    (fun W' c' => vrd_iQall d true ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v W' c' /\
       Pm (ms_mem (cfg_ms c'))).
Proof.
intros Pm d CTX ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v P regsC MC mdc W2 ly2 S2
  Hp2 regs2 mem2 md2 k1 k' Lam' peak' cnt' fail' ran' HPRE Hd HMID HP Hnc HJ1 HJ2 HWIN2 HPR Ha0 Hcf HSW HLED2 HMODE
  Hhdr2 Hrl2 HHUg HLVg HXFg HEX HINJ HPM.
pose proof (vrd_ipre_prj d CTX true ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v HPRE)
  as (HAFN & HROD & Hshi64 & Hfrm & HAR & Hal16 & Hceil & Hslo & Hshi & H47 & Htop & Htop' & Hpres & He0 & He16 & Hetop &
      Hepres & Hspq & Hqe & Hq8 & Ht0 & Ht62 & Htp & Hlen & Hqt & Hd32 & Hv4096 & Hv8 & HAMv & HNv & HRAv & HZv & Hrwv &
      HATv & Hqv & Htv & Hvw & HLED & HdM & Hcnt & HSRC & HHOME & HRAq & HCE & H10 & H11 & H12 & Hpe & Hop & HROOM & HFR).
destruct (vrd_led_bounds _ _ _ _ _ _ _ _ _ _ _ _ HLED) as (HLp & HLpk & HLc & HLf & HLr).
destruct (vrd_imove_nil d CTX true ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v HPRE)
  as (HLM0 & HBM0 & _ & _).
pose proof (ajxR_ar HJ1) as HAR2. pose proof (ajxR_ly HJ1) as Hly2.
pose proof (ajxR_frs HJ2) as Hfrs2.
pose proof (@cf_head_nonneg cp) as Hcf0.
change (56 * cap2R 0) with 448 in HSW.
destruct HSW as ((bl & Hsw1 & Hsw2) & _ & (Lam1 & HL1a & HL1b)).
set (trR := [PjGrammar.EGrow 0 448; PjGrammar.EFail 64]).
assert (Htrp : hpeakR trR = 448) by (vm_compute; reflexivity).
assert (Htrh : PjGrammar.held trR = 448) by (vm_compute; reflexivity).
assert (Htrc : PjGrammar.calls trR = 2%nat) by reflexivity.
assert (Hrl1 : (1 <= length (rest_atR tb text p))%nat).
{ pose proof (vrd_rest_len tb text p ltac:(lia)) as Hr. lia. }
assert (HMX : (PjGrammar.MAXD - d)%nat = S (PjGrammar.MAXD - S d)) by lia.
assert (HLp' : Permutation Lam' ([(k', 448)] ++ Lam)).
{ eapply Permutation_trans; [exact HL1b|]. cbn [app]. apply perm_skip.
  apply Permutation_sym. cbn [kids_blkR Z.eqb app] in HL1a. exact HL1a. }
assert (HLs' : Ledger.lsum Lam' = Ledger.lsum Lam + 448).
{ rewrite (vi_lsum_perm _ _ HLp'). cbn [app Ledger.lsum]. lia. }
(* the call's granted trace begins with the object grow's two granted reallocs *)
destruct (vrd_gtrace_grow d true (rest_atR tb text p) Hd Hnc) as (tg & Htg).
assert (HG : prhPi_gtrace d true (rest_atR tb text p) =
  [] ++ [PjGrammar.EGrow 0 448; PjGrammar.EGrow 0 64] ++ tg) by (rewrite Htg; reflexivity).
(* the ledger move of the arm, by grow's step from the entry's empty move *)
assert (HSWm : rd_ledger_move Lam peak cnt fail ran most (repeat true (PjGrammar.calls []) ++ [true; false])
                 (prhPi_gtrace d true (rest_atR tb text p)) ([] ++ trR) ([(k', 448)] ++ []) Lam' peak' cnt' fail' ran' /\
               Ledger.lsum ([(k', 448)] ++ []) = PjGrammar.held ([] ++ trR)).
{ apply (vi_grow_swap_step Lam peak cnt fail ran most (prhPi_gtrace d true (rest_atR tb text p)) [] [] Lam peak cnt fail
           ran (kids_blkR 0 0) [(k', 448)] [] Lam1 Lam' [true; false]
           [PjGrammar.EGrow 0 448; PjGrammar.EGrow 0 64] trR tg peak' cnt' fail' ran' HLM0 eq_refl
           ltac:(cbn; apply perm_nil) HL1a HL1b ltac:(lia));
    [ rewrite Htrc; cbn [PjGrammar.calls]; lia | rewrite Htrc; reflexivity | | | | | reflexivity | reflexivity | |
      exact HG | rewrite Htrc; cbn; lia ].
  - (* the outcomes of the two reallocs *)
    rewrite Htrc. cbn [prh_ev_reqs PjGrammar.is_call filter map PjReqBound.ev_req trR].
    destruct HMODE as [(Hcf1 & _ & _ & _ & ->) | (Hcf1 & _ & _ & _ & ->)]; (split; [|split]).
    + intros i Hi He. destruct i as [|[|i]]; [cbn in He; lia | reflexivity | lia].
    + left. reflexivity.
    + intros i Hi Hr _. exfalso. destruct i as [|[|i]]; [|rewrite vrd_refused_f in Hr by reflexivity | lia].
      * rewrite vrd_refused_t in Hr by reflexivity. discriminate Hr.
      * change (Z.of_nat 1) with 1 in Hr. rewrite (proj2 (Z.eqb_eq _ _) Hcf1) in Hr. discriminate Hr.
    + intros i Hi He. destruct i as [|[|i]]; [cbn in He; lia | reflexivity | lia].
    + change (8 * cap2R 0) with 64. destruct (Z.leb_spec 64 most) as [Hm | Hm]; [right | left; reflexivity].
      split; [reflexivity|]. exists 1%nat. split; [lia|].
      split; [rewrite vrd_refused_f by reflexivity; change (Z.of_nat 1) with 1; destruct (Z.eqb_spec (cnt + 1) fail); [lia|];
              reflexivity | exact Hm].
    + intros i Hi Hr Hle. change (8 * cap2R 0) with 64.
      destruct i as [|[|i]]; [rewrite vrd_refused_t in Hr by reflexivity; discriminate Hr | | lia].
      assert (Hle' : 64 <= most) by exact Hle. destruct (Z.leb_spec 64 most); [reflexivity | lia].
  - rewrite Htrc. destruct HMODE as [(_ & _ & -> & _) | (_ & _ & -> & _)]; [reflexivity|].
    replace (cnt + 1 + 1) with (cnt + 2) by lia. rewrite Z.mod_small by lia. reflexivity.
  - rewrite Htrc. destruct HMODE as [(Hcf1 & _ & _ & -> & _) | (Hcf1 & _ & _ & -> & _)].
    + split; [intros _; reflexivity | intros Hno; exfalso; apply Hno; cbn [Z.of_nat]; lia].
    + split; [intros (H1 & H2); exfalso; cbn [Z.of_nat] in H2; lia | intros _; reflexivity].
  - intros s L Hs. cbn [trR fold_left lsz_evR kids_blkR Z.eqb map snd app] in Hs |- *.
    change (Z.of_nat 448) with 448. apply perm_skip. exact Hs.
  - (* the peak: the refusal peak of the keys realloc's request, read off the granted reallocs' held counts *)
    assert (Hh2 : prh_ev_helds [PjGrammar.EGrow 0 448; PjGrammar.EGrow 0 64] = [448; 512]) by reflexivity.
    rewrite Htrp, Htrc, vrd_rpeak2, (vrd_refused_t [true; false] cnt fail 0 eq_refl), vrd_refused_f by reflexivity.
    change (Z.of_nat 1) with 1. rewrite Hh2. cbn [map nth].
    destruct HMODE as [(Hcf1 & -> & _) | (Hcf1 & -> & _)].
    + rewrite (proj2 (Z.eqb_eq _ _) Hcf1). cbn [negb]. lia.
    + destruct (Z.eqb_spec (cnt + 1) fail); [lia|]. cbn [negb].
      change (0 =? 0) with true. change (8 * cap2R 0) with 64. cbv iota beta. lia. }
cbn [repeat PjGrammar.calls app] in HSWm. destruct HSWm as (HLM2 & HlsD).
assert (HBM2 : rd_blocks_move B ly Sa ly2 S2 [(k', 448)] trR (rest_atR tb text p) d).
{ apply (vi_swap_move B ARx LAWS ly Sa ly Sa ly2 S2 Hp2 W2 mem2 md2 [] [] trR (rest_atR tb text p) d (kids_blkR 0 0)
           [(k', 448)] [] bl HBM0 ltac:(cbn; apply perm_nil) Hsw1 Hsw2 HAR2).
  - intros b [<- | []]. cbn [snd]. lia.
  - intros b b' _ Hb'. cbn in Hb'. destruct Hb'.
  - rewrite Hfrs2. reflexivity.
  - rewrite Htrp. lia. }
pose proof (vrd_ient_ok_of_ipre d CTX true ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v ch
  HPRE) as HEN.
destruct (vrd_gevs_arm true) as (_ & _ & Hev & _). rewrite Hev in HLVg, HXFg.
apply (vrd_iref_inv Pm d CTX true ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v P regsC MC
  mdc W2 ly2 S2 Hp2 regs2 mem2 md2 k1 [true; false] trR [] [(k', 448)] Lam' peak' cnt' fail' ran'
  HPRE HMID HP HJ1 HWIN2 HPR Ha0); [ | exact HLED2 | exact Hrl2
  | exact (vrd_hull_gtrace d true (rest_atR tb text p) Sa S2 Hd Hnc HHUg) | exact HLVg | exact HXFg | exact HEX
  | exact HINJ
  | exact HLM2 | exact HBM2 | | exact HlsD | | | exact HPM].
- exact (vrd_items_keys_fail d (rest_atR tb text p) [] Hd Hnc).
- rewrite (vi_blocks_bytes_lsum B ly2 S2), (vi_blocks_bytes_lsum B ly Sa).
  rewrite (vi_lsum_perm _ _ Hsw1), (vi_lsum_perm _ _ Hsw2), !vi_lsum_app.
  unfold prh_held. rewrite Htrh, Htrc. cbn [kids_blkR Z.eqb prhReader_ab map Ledger.lsum fst snd]. lia.
- rewrite HMX.
  apply (vi_part_fd _ (prh_lin Lam') v 6 k' 0 0 0 false [(k', 448)] [] [] [(k', 448)] [] (PjGrammar.MAXD - S d)).
  + apply NoDup_ListNoDup. constructor; [intros [] | constructor].
  + exact (vi_apart_node B ARx LAWS CTX0 CW _ _ ly2 S2 Hp2 W2 mem2 md2 [(k', 448)] trR Lam' _ _ _ _ _ _ HEN HAR2 Hly2 HBM2
             HLED2 HLp').
  + exact Hhdr2.
  + right. exists 448. split; [|split; [lia | reflexivity]].
    unfold prh_lin. apply (Permutation_in _ (Permutation_sym HLp')). left. reflexivity.
  + left. split; [reflexivity|]. split; reflexivity.
  + apply Permutation_refl.
  + reflexivity.
  + reflexivity.
  + constructor.
- (* The kit's cut: the order list is the new kids block alone, the model's gheld first arm (the kids moved, the keys
     refused at cap 0) *)
  intros Hhd n _. exists [(k', 448)]. split.
  + apply (vrd_hdr_fo_kids _ (prh_lin Lam') v 6 k' 448 0 n Hhdr2).
    * unfold prh_lin. apply (Permutation_in _ (Permutation_sym HLp')). left. reflexivity.
    * lia.
    * exact (vi_apart_node B ARx LAWS CTX0 CW _ _ ly2 S2 Hp2 W2 mem2 md2 [(k', 448)] trR Lam' _ _ _ _ _ _ HEN HAR2 Hly2
               HBM2 HLED2 HLp').
  + rewrite (vrd_frees_keys_fail d (rest_atR tb text p) [] Hd Hnc). cbn [map snd]. rewrite Hhd. reflexivity.
Qed.

(* vrd_qchain at ANY later view and layout: the chain from s0 = q at the loop's sp reads the words at q - 16 and q - 8,
   which are parse_items' saved ra / s0 (vi_saved) or caller-window words agreeing with the entry view; the one at
   q - 16 is below alloc_ceiling by prh_cur_entry (VproC's vrd_cur_chain_call) *)
Lemma vrd_qchain_at : forall d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v
    (ly' : alayout) (W' : world segs) (M : word -> option byte),
  vrd_ipre d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v ->
  vi_saved W' M regs0 ->
  (forall a, spZ regs0 <= a < q -> aview segs (w_H W') M a = aview segs (w_H W) mem0 a) ->
  ly_top ly' = ly_top ly ->
  exists ch1, achain ly' (aview segs (w_H W') M) (spZ regs0 - 144) q ch1.
Proof.
intros d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v ly' W' M HPRE HSV HAG Hly.
pose proof (vrd_ipre_prj d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v HPRE)
  as (HAFN & HROD & Hshi64 & Hfrm & HAR & Hal16 & Hceil & Hslo & Hshi & H47 & Htop & Htop' & Hpres & He0 & He16 & Hetop &
      Hepres & Hspq & Hqe & Hq8 & Ht0 & Ht62 & Htp & Hlen & Hqt & Hd32 & Hv4096 & Hv8 & HAMv & HNv & HRAv & HZv & Hrwv &
      HATv & Hqv & Htv & Hvw & HLED & HdM & Hcnt & HSRC & HHOME & HRAq & HCE & H10 & H11 & H12 & Hpe & Hop & HROOM & HFR).
pose proof (vrd_stk_ge d) as HSTK. pose proof H_img as (Himg1 & Himg2 & Himg3). unfold PI_FRAME in HSTK.
destruct (Z_lt_le_dec q (ly_top ly - 16)) as [Hqt' | Hqt'].
2:{ exists []. left. split; [right; left; rewrite Hly; exact Hqt' | reflexivity]. }
assert (HW : forall a, a = q - 16 \/ a = q - 8 ->
  exists w, rdword (aview segs (w_H W') M) a = Some w /\ prh_word_entry W mem0 regs0 a w).
{ intros a Ha.
  destruct (Z.eq_dec a (spZ regs0 - 8)) as [E8|N8]; [| destruct (Z.eq_dec a (spZ regs0 - 16)) as [E16|N16]].
  - exists (raZ regs0). split.
    + rewrite E8. apply vrd_rdword_of_val_mem.
      * pose proof (HSV 0%nat ltac:(lia)) as V. cbn [nth vi_extras] in V.
        replace (spZ regs0 - 8 - 8 * Z.of_nat 0) with (spZ regs0 - 8) in V by lia. exact V.
      * pose proof (bv_unsigned_in_range 64 (getr regs0 1)) as Hb. change (bv_modulus 64) with (2 ^ 64) in Hb.
        exact Hb.
    + unfold prh_word_entry. rewrite E8, Z.eqb_refl. reflexivity.
  - exists (s0Z regs0). split.
    + rewrite E16. apply vrd_rdword_of_val_mem.
      * pose proof (HSV 1%nat ltac:(lia)) as V. cbn [nth vi_extras] in V.
        replace (spZ regs0 - 8 - 8 * Z.of_nat 1) with (spZ regs0 - 16) in V by lia. exact V.
      * pose proof (bv_unsigned_in_range 64 (getr regs0 8)) as Hb. change (bv_modulus 64) with (2 ^ 64) in Hb.
        exact Hb.
    + unfold prh_word_entry. rewrite (proj2 (Z.eqb_neq a (spZ regs0 - 8)) N8), E16, Z.eqb_refl. reflexivity.
  - assert (Ha0 : spZ regs0 <= a /\ a + 8 <= q) by lia.
    destruct (vrd_rdword_present (w_H W) mem0 a) as [w Hw].
    { intros k Hk. apply Hepres. lia. }
    exists w. split.
    + rewrite (rdword_ext (aview segs (w_H W) mem0) (aview segs (w_H W') M) a); [exact Hw|].
      intros k Hk. rewrite (HAG (a + k)) by lia. reflexivity.
    + unfold prh_word_entry. rewrite (proj2 (Z.eqb_neq a (spZ regs0 - 8)) N8),
        (proj2 (Z.eqb_neq a (spZ regs0 - 16)) N16). exact Hw. }
destruct (HW (q - 16) (or_introl eq_refl)) as (w16 & H16 & E16).
destruct (HW (q - 8) (or_intror eq_refl)) as (w8 & H8 & _).
assert (Hw16 : w16 < YM05.alloc_ceiling).
{ destruct HCE as (_ & HCE'). pose proof (HCE' F_parse_items (or_intror eq_refl)) as Hlo.
  unfold prh_s0 in Hlo. rewrite H_s0, Z.add_0_r in Hlo.
  exact (Hlo w16 E16). }
assert (Hcq : YM05.alloc_ceiling <= q) by lia.
exact (vrd_cur_chain_call ly' (w_H W') M (spZ regs0 - 144) q w16 Hcq ltac:(rewrite Hly; exact Hqt') Hq8 ltac:(lia) H16
         Hw16 (ex_intro _ w8 H8)).
Qed.

(* the stack top a callee's journal keeps (layout_le's ly_top conjunct), through one named projection *)
Lemma vrd_ll_top : forall n ly ly', layout_le n ly ly' -> ly_top ly' = ly_top ly.
Proof. intros n ly ly' (_ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

(* a raw-memory keep off a byte set gives the same reader view there *)
Lemma vrd_keep_av : forall (Hh : word -> bool) (m m' : word -> option byte) (X : Z -> Prop) a,
  (forall x : word, ~ X (bv_unsigned x) -> m' x = m x) -> 0 <= a < 2 ^ 64 -> ~ X a ->
  aview segs Hh m' a = aview segs Hh m a.
Proof.
intros Hh m m' X a HK Ha Hn. unfold aview, mbyte, mrestrict. rewrite HK; [reflexivity|].
rewrite unsigned_lit_small by lia. exact Hn.
Qed.

Lemma vrd_keep_mr : forall (Hh : word -> bool) (m m' : word -> option byte) (X : Z -> Prop),
  (forall x : word, ~ X (bv_unsigned x) -> m' x = m x) ->
  forall x : word, ~ X (bv_unsigned x) -> mrestrict Hh m' x = mrestrict Hh m x.
Proof. intros Hh m m' X HK x Hx. unfold mrestrict. rewrite (HK x Hx). reflexivity. Qed.

(* ==== FOUR MORE NAMED HYPOTHESES for the loop head's position facts after the first grow, each an instance / image
   fact, verbatim the four of IelemE's lib/A/VrdIStep.v (blob e3f3c9a5ef07, Section S :466-470), which
   vrd_icur_after_call / vrd_node_ra_after_call / vrd_lam_shadow take (a journal keeps no shadow of a heap block across
   a call; those facts are rebuilt from the AR_laws_x laws at the later state):
   - H_HL: the harness-block shadow law's head length is cf_head (AR_laws_x field 14; an identity at the cf instance);
   - H_zsal: the image's zero-shadow ranges are granule-aligned (asyms_ok's aso_zshadow, ARcf's amc_syms);
   - H_imgvis: the image's shadow is mapped at every state (a Theorem Labs lane's img_shadow_vis_cf, YGcfAmx2.v:47);
   - H_pst_ro: alloc.c's statics are not read-only (S1ImgA.v pst_not_ro_A at prh_img_A). ==== *)
Hypothesis H_HL : HL = cf_head.
Hypothesis H_zsal : Forall (fun r => fst r mod 8 = 0 /\ snd r mod 8 = 0) (as_zero_shadow B).
Hypothesis H_imgvis : forall ly S Hp W mem md a, ARx ly S Hp W mem md -> IMG_LO <= a < IMG_TOP ->
  aview segs (w_H W) mem (shadow_addr a) <> None.
Hypothesis H_pst_ro : forall a, Exists (in_zr a) prh_pst -> ~ in_roP segs pa_relro_lo pa_relro_hi a.

(* E. THE LOOP HEAD AFTER THE FIRST GROW: from the facts at row 92 (the call's re-entry facts, grow's journal and
   agreement clause), a granted grow (kids = k', keys, the ledger move by trg) and the run of rows 92..107 (registers,
   the four spill slots, the frame keep, the journal), the loop head vrd_ielem_a holds at the row-108 position, with
   the call chain ie_ch2 of the loop's own calls chosen as the chain at that position *)
Lemma vrd_ielem_entry : forall d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v
    P regsC MC mdc W2 ly2 S2 Hp2 regs2 mem2 md2 k1 regs' mem' md' kids keys D trg okg Lam' peak' cnt',
  vrd_ipre d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v ->
  (d < PjGrammar.MAXD)%nat ->
  vrd_imid d o e q text len v regs0 ly Sa Hp W mem0 md0 P regsC MC mdc ->
  p + 1 <= P <= text + len -> PjGrammar.skip (tl (rest_atR tb text p)) = rest_atR tb text P ->
  (forall r, PjGrammar.skip (tl (rest_atR tb text p)) <> PjGrammar.closer o :: r) ->
  ajournal_xR (SK := SK) segs B prh_pst ARx (wle' segs YGcfRehidePost.RZ_cf) (STK_parse_items d + e) (spZ regs0 + e)
    (rd_fp q v) ly Sa Hp W mem0 md0 [] ly2 S2 Hp2 W2 mem2 md2 (0 + k1) ->
  ajournal_xR (SK := SK) segs B prh_pst ARx (wle' segs YGcfRehidePost.RZ_cf) (STK_grow + (e + 144)) (spZ regs0 + e)
    (vrd_gfp (if o then 6 else 5) 0 0 0 v) ly Sa Hp W MC mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  (forall a, spZ regs0 + e + - (e + 144) <= a < spZ regs0 + e -> ~ inFP (vrd_gfp (if o then 6 else 5) 0 0 0 v) a ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W) MC a) ->
  aregs_preserved regsC regs2 ->
  (* the run of rows 92..107 (vrd_itail_inv's continuation) *)
  (forall r, In r [2; 3; 4; 8; 9; 19; 20; 23; 26; 27] -> getr regs' (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)) ->
  getr regs' 18 = w64 (shx (v + 40)) -> getr regs' 21 = w64 32 -> getr regs' 22 = w64 (v + 40) ->
  getr regs' 24 = w64 (v + 24) -> getr regs' 25 = w64 PI_WSMASK ->
  val_mem segs (mrestrict (w_H W2) mem') (spZ regs0 - 136) 8 (bv_unsigned (getr regs2 22)) ->
  val_mem segs (mrestrict (w_H W2) mem') (spZ regs0 - 128) 8 (bv_unsigned (getr regs2 21)) ->
  val_mem segs (mrestrict (w_H W2) mem') (spZ regs0 - 120) 8 (shx (v + 24)) ->
  val_mem segs (mrestrict (w_H W2) mem') (spZ regs0 - 112) 8 (v + 32) ->
  (forall x : word, ~ (spZ regs0 - 136 <= bv_unsigned x < spZ regs0 - 104) -> mem' x = mem2 x) ->
  ajournal_xR (SK := SK) segs B prh_pst ARx (wle' segs YGcfRehidePost.RZ_cf) (STK_parse_items d + e) (spZ regs0 + e)
    (rd_fp q v) ly Sa Hp W mem0 md0 [] ly2 S2 Hp2 W2 mem' md' (0 + k1) ->
  (* grow's grant *)
  pj_hdrR segs (mrestrict (w_H W2) mem2) v (if o then 6 else 5) 0 0 kids keys 0 8 ->
  prh_ledger B ly2 S2 Hp2 W2 mem2 Lam' peak' cnt' fail ran most own -> cnt' <= cnt + 2 ->
  rd_ledger_move Lam peak cnt fail ran most okg (prhPi_gtrace d o (rest_atR tb text p)) trg D Lam' peak' cnt' fail ran ->
  Ledger.lsum D = PjGrammar.held trg ->
  rd_blocks_move B ly Sa ly2 S2 D trg (rest_atR tb text p) d ->
  Permutation Lam' (D ++ Lam) ->
  Permutation D (kids_blkR kids 8 ++ keys_blkR (if o then 6 else 5) keys 8) ->
  okg = repeat true (PjGrammar.calls trg) ->
  (forall okt, PjGrammar.grow o 0 0 (okg ++ okt) = (Some 8%nat, trg, okt)) ->
  trg = prhPg_gtrace o 0 0 ->
  blocks_bytes S2 <= blocks_bytes Sa + prh_held trg -> room_live_cf S2 ->
  (* grow's grant: the position and the live requests moved by its events, from the call's entry state *)
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist Sa ->
     PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs trg) ->
     exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (PresetReqAt.rd_hevs trg))%nat H0 hist' S2) ->
  Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S2))
    (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf Sa)) (PresetReqAt.rd_hevs trg)) ->
  (* grow's grant: the hull meters moved by at most its events *)
  PresetHullBudget.hull_used Sa S2 (PresetReqAt.rd_hevs trg) ->
  (o = false -> keys = 0) ->
  exists ch2, vrd_ielem_a B ARx SK
    (vrd_ient_of d o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v ch2)
    (MkIPos fx ly2 S2 Hp2 W2 regs' mem' md' (0 + k1) 0 8 kids keys P [] (2 * length (rest_atR tb text p) + 1)
       (vrd_jtail (S d) o 0 8 [] (2 * length (rest_atR tb text p) + 1) (rest_atR tb text P))
       okg trg D Lam' peak' cnt' fail ran).
Proof.
intros d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v P regsC MC mdc W2 ly2 S2
  Hp2 regs2 mem2 md2 k1 regs' mem' md' kids keys D trg okg Lam' peak' cnt' HPRE Hd HMID HP Hsk Hnc HJ1 HJ2 HWIN2 HPR
  HKr R18 R21 R22 R24 R25 C8 C16 C24 C32 HKM HJ1' Hhdr2 HLED2 Hcnt' HLM2 HlsD HBM2 HLp' HDp Hokg HG Htrg Hbb2 Hrl2 HXF HLV
  HHU Hk0.
pose proof (vrd_ipre_prj d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v HPRE)
  as (HAFN & HROD & Hshi64 & Hfrm & HAR & Hal16 & Hceil & Hslo & Hshi & H47 & Htop & Htop' & Hpres & He0 & He16 & Hetop &
      Hepres & Hspq & Hqe & Hq8 & Ht0 & Ht62 & Htp & Hlen & Hqt & Hd32 & Hv4096 & Hv8 & HAMv & HNv & HRAv & HZv & Hrwv &
      HATv & Hqv & Htv & Hvw & HLED & HdM & Hcnt & HSRC & HHOME & HRAq & HCE & H10 & H11 & H12 & Hpe & Hop & HROOM & HFR).
destruct (vrd_after92 d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v P regsC MC mdc W2
  ly2 S2 Hp2 regs2 mem2 md2 (0 + k1) HPRE HMID HJ1 HWIN2 HPR)
  as (Hsp2 & HSV2 & Hgp2 & Htp2 & H182 & H82 & H92 & H192 & H202 & H212 & H222 & H232 & H262 & H272 & HWINe & Vq2 &
      Vq82 & Vq162 & RWq2 & Hpr2 & HFV).
pose proof (vrd_stk_ge d) as HSTK. pose proof H_img as (Himg1 & Himg2 & Himg3). unfold PI_FRAME in HSTK.
pose proof (ajxR_ar HJ1') as HAR'. pose proof (ajxR_ly HJ1') as Hly'.
pose proof (ajxR_frs HJ2) as Hfrs2.
pose proof (vrd_ll_top _ _ _ Hly') as Htop2.
pose proof (@cf_head_nonneg cp) as Hcf0.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold amem_range in HAMv.
assert (Rv : 4096 <= v /\ v + 56 <= 2 ^ 47) by lia.
set (x := rest_atR tb text p) in *.
set (y := rest_atR tb text P) in *.
assert (Hylen : (length y <= length x)%nat).
{ subst x y. pose proof (vrd_rest_len tb text p ltac:(lia)). pose proof (vrd_rest_len tb text P ltac:(lia)). lia. }
(* the frame window the run wrote is apart from everything else the position reads *)
set (X := fun a => spZ regs0 - 136 <= a < spZ regs0 - 104).
assert (KMr : forall z : word, ~ X (bv_unsigned z) -> mrestrict (w_H W2) mem' z = mrestrict (w_H W2) mem2 z)
  by exact (vrd_keep_mr (w_H W2) mem2 mem' X HKM).
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview segs (w_H W2) mem' a = aview segs (w_H W2) mem2 a)
  by (intros a Ha Hn; exact (vrd_keep_av (w_H W2) mem2 mem' X a HKM Ha Hn)).
assert (KK : forall Pz : Z -> Prop, (forall a, Pz a -> 0 <= a < 2 ^ 64 /\ ~ X a) ->
  rd_keep segs (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) mem') Pz)
  by (intros Pz HPz; exact (vrd_rdkeep_w (w_H W2) mem2 mem' X Pz KMr HPz)).
assert (Hsp' : spZ regs' = spZ regs0 - 144).
{ unfold spZ. change (getr regs' 2) with (getr regs' (Z_to_bv 5 2)).
  rewrite (HKr 2 ltac:(cbn; tauto)). exact Hsp2. }
assert (HSV' : vi_saved W2 mem' regs0).
{ intros j Hj. apply (val_mem_keep segs _ _ _ _ _ (HSV2 j Hj)). apply KK. intros a Ha. unfold X. lia. }
assert (HAG' : forall a, spZ regs0 <= a < q -> aview segs (w_H W2) mem' a = aview segs (w_H W) mem0 a).
{ intros a Ha. rewrite (KA a ltac:(lia) ltac:(unfold X; lia)). apply HWINe; [lia|].
  intros (r & Hin & Hr). cbn [rd_fp In] in Hin. destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr; lia. }
destruct (vrd_qchain_at d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v ly2 W2 mem'
  HPRE HSV' HAG' Htop2) as (ch1 & Hch1).
exists ch1.
assert (Hpr' : forall a, spZ regs0 - STK_parse_items d <= a < spZ regs0 + e -> apresent (w_H W2) mem' a).
{ intros a Ha. apply (ajxR_pres HJ1'). lia. }
assert (Hb21 : bv_unsigned (getr regs2 21) = shadow_addr (q + 16)).
{ rewrite H212. unfold w64, shx, shadow_addr. apply unsigned_lit_small.
  assert (0 <= (q + 16) / 8 <= 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  unfold SHADOW_OFF. lia. }
assert (Hb22 : bv_unsigned (getr regs2 22) = q + 8) by (rewrite H222; unfold w64; apply unsigned_lit_small; lia).
unfold vrd_ielem_a, vrd_ient_of.
split.
{ unfold vrd_iframe. cbv zeta.
  cbn [ie_ly ie_S ie_Hp ie_W ie_regs ie_mem ie_md ie_ch ie_Lam ie_peak ie_cnt ie_fail ie_ran ie_most ie_own ie_e ie_q ie_text ie_len
    ie_p ie_d ie_tb ie_v ie_o ie_ch2 ip_fx ip_ly ip_S ip_Hp ip_W ip_regs ip_mem ip_md ip_k ip_n ip_cap ip_kids ip_keys
    ip_p ip_acc ip_f ip_cont ip_ok ip_tr ip_D ip_Lam ip_peak ip_cnt ip_fail ip_ran].
  split; [exact Hsp'|].
  repeat match goal with |- val_mem _ _ (spZ regs0 - ?K) 8 _ /\ _ =>
    split; [let j := eval vm_compute in (Z.to_nat ((K - 8) / 8)) in
            let V := fresh "V" in pose proof (HSV' j ltac:(lia)) as V; cbn [nth vi_extras] in V;
            replace (spZ regs0 - 8 - 8 * Z.of_nat j) with (spZ regs0 - K) in V by lia; exact V|] end.
  split; [rewrite <- Hb22; exact C8|].
  split; [rewrite <- Hb21; exact C16|].
  split; [exact C24|].
  split; [exact C32|].
  intros a Ha. apply Hpr'. lia. }
split.
{ unfold vrd_iregs. cbn [ie_q ie_v ie_o ip_regs].
  assert (KR : forall r : nat, In (Z.of_nat r) [2; 3; 4; 8; 9; 19; 20; 23; 26; 27] ->
    getr regs' (Z_to_bv 5 (Z.of_nat r)) = getr regs2 (Z_to_bv 5 (Z.of_nat r))) by (intros r Hr; exact (HKr _ Hr)).
  split; [change (getr regs' 3) with (getr regs' (Z_to_bv 5 3)); rewrite (HKr 3 ltac:(cbn; tauto)); exact Hgp2|].
  split; [change (getr regs' 4) with (getr regs' (Z_to_bv 5 4)); rewrite (HKr 4 ltac:(cbn; tauto)); exact Htp2|].
  split; [change (getr regs' 8) with (getr regs' (Z_to_bv 5 8)); rewrite (HKr 8 ltac:(cbn; tauto)); exact H82|].
  split; [change (getr regs' 9) with (getr regs' (Z_to_bv 5 9)); rewrite (HKr 9 ltac:(cbn; tauto)); exact H92|].
  split; [rewrite R18; reflexivity|].
  split; [change (getr regs' 19) with (getr regs' (Z_to_bv 5 19)); rewrite (HKr 19 ltac:(cbn; tauto)); exact H192|].
  split; [change (getr regs' 20) with (getr regs' (Z_to_bv 5 20)); rewrite (HKr 20 ltac:(cbn; tauto)); exact H202|].
  split; [exact R21|]. split; [exact R22|].
  split; [change (getr regs' 23) with (getr regs' (Z_to_bv 5 23)); rewrite (HKr 23 ltac:(cbn; tauto)); exact H232|].
  split; [exact R24|]. split; [exact R25|].
  split; [change (getr regs' 26) with (getr regs' (Z_to_bv 5 26)); rewrite (HKr 26 ltac:(cbn; tauto)); exact H262|].
  change (getr regs' 27) with (getr regs' (Z_to_bv 5 27)); rewrite (HKr 27 ltac:(cbn; tauto)); exact H272. }
pose proof (ajxR_ar HJ1) as HAR2.
pose proof (vrd_ient_ok_of_ipre d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v ch1
  HPRE) as HEN.
assert (HXlo : forall a, a < YM05.alloc_ceiling -> ~ X a) by (intros a Ha; unfold X; lia).
assert (HLED' : prh_ledger B ly2 S2 Hp2 W2 mem' Lam' peak' cnt' fail ran most own).
{ apply (prh_ledger_kept_aview B ly2 S2 Hp2 W2 mem2 ly2 S2 Hp2 W2 mem' Lam' peak' cnt' fail ran most own HLED2);
    [ | | intros a0 k0 _ Hab; exact Hab | apply Permutation_refl].
  - intros a Ha. pose proof (H_pst_img a Ha) as Hi. pose proof (@pa_segs_low _ _ PI_prog_A a Hi) as Hlow.
    apply KA; [lia | apply HXlo; lia].
  - intros a0 k0 i Hin Hi.
    destruct (vrd_led_hblk _ _ _ _ _ _ _ _ _ _ _ _ a0 k0 HLED2 Hin) as (Hk0' & Hab & _).
    destruct (alx_blocks segs B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 Hab) as (_ & Hb4096 & Hbc & _).
    assert (Hrq : k0 + cf_head <= req_size (k0 + cf_head))
      by (unfold req_size; destruct (Z.eqb_spec (k0 + cf_head) 0); lia).
    apply KA; [lia | apply HXlo; lia]. }
assert (HinK : In (kids, 56 * 8) Lam').
{ apply (Permutation_in _ (Permutation_sym HLp')). apply in_or_app. left.
  apply (Permutation_in _ (Permutation_sym HDp)). apply in_or_app. left. left. reflexivity. }
assert (HinY : o = true -> In (keys, 8 * 8) Lam').
{ intros Ho. apply (Permutation_in _ (Permutation_sym HLp')). apply in_or_app. left.
  apply (Permutation_in _ (Permutation_sym HDp)). apply in_or_app. right. rewrite Ho. left. reflexivity. }
split.
{ unfold vrd_inode. cbv zeta.
  cbn [ie_ly ie_S ie_Hp ie_W ie_regs ie_mem ie_md ie_ch ie_Lam ie_peak ie_cnt ie_fail ie_ran ie_most ie_own ie_e ie_q ie_text ie_len
    ie_p ie_d ie_tb ie_v ie_o ie_ch2 ip_fx ip_ly ip_S ip_Hp ip_W ip_regs ip_mem ip_md ip_k ip_n ip_cap ip_kids ip_keys
    ip_p ip_acc ip_f ip_cont ip_ok ip_tr ip_D ip_Lam ip_peak ip_cnt ip_fail ip_ran].
  split.
  { apply (pj_hdrR_keep segs (mrestrict (w_H W2) mem2) _ _ _ _ _ _ _ _ _ Hhdr2). apply KK.
    intros a Ha. split; [lia|]. unfold X. intros Hx. apply (proj2 (HNv a Ha)). lia. }
  split; [lia|]. split; [lia|]. split; [intros Hc; lia|].
  split; [intros _; split; [exact HinK | exact HinY]|].
  split; [reflexivity|].
  split.
  { exists []. split; [rewrite app_nil_l, app_nil_r; exact HDp | destruct o; reflexivity]. }
  split.
  { intros a Ha. apply apresent_writable.
    apply (vi_lam_present B ARx LAWS ly2 S2 Hp2 W2 mem' md' Lam' peak' cnt' fail ran most own kids (56 * 8) a HAR' HLED' HinK).
    lia. }
  split.
  { exact (vrd_node_ra_after_call B ARx SK LAWS H_HL _ CTX0 CW _ ly2 S2 Hp2 W2 mem' md' (0 + k1) D trg Lam' peak' cnt'
             fail ran most own HEN HJ1' HBM2 HLED' HLp'). }
  split; [intros _; exact (proj1 (vrd_lam_shadow B ARx LAWS H_HL ly2 S2 Hp2 W2 mem' md' Lam' peak' cnt' fail ran most own _ _
                                    HAR' HLED' HinK))|].
  split; [intros Ho _; exact (proj1 (vrd_lam_shadow B ARx LAWS H_HL ly2 S2 Hp2 W2 mem' md' Lam' peak' cnt' fail ran most own _ _
                                       HAR' HLED' (HinY Ho)))|].
  exact Hk0. }
destruct (vrd_icur_after_call B ARx SK LAWS H_HL H_zsal H_imgvis H_pst_ro _ CTX0 CW _ ly2 S2 Hp2 W2 mem' md' (0 + k1) D trg
  Lam' peak' cnt' fail ran most own HEN HJ1' HBM2 HLED' HLp') as (Hsrc' & Hhome' & HRAq').
assert (Hlxy : Z.of_nat (length y) + 1 <= Z.of_nat (length x)).
{ subst x y. rewrite (vrd_rest_len tb text p) by lia. rewrite (vrd_rest_len tb text P) by lia. lia. }
assert (KQ : forall a (n : nat) vv, q <= a -> a + Z.of_nat n <= q + 24 ->
  val_mem segs (mrestrict (w_H W2) mem2) a n vv -> val_mem segs (mrestrict (w_H W2) mem') a n vv).
{ intros a n vv H1 H2 Hv. apply (val_mem_keep segs _ _ _ _ _ Hv). apply KK. intros z Hz. split; [lia|]. unfold X. lia. }
split.
{ unfold vrd_icur. cbv zeta.
  cbn [ie_ly ie_S ie_Hp ie_W ie_regs ie_mem ie_md ie_ch ie_Lam ie_peak ie_cnt ie_fail ie_ran ie_most ie_own ie_e ie_q ie_text ie_len
    ie_p ie_d ie_tb ie_v ie_o ie_ch2 ip_fx ip_ly ip_S ip_Hp ip_W ip_regs ip_mem ip_md ip_k ip_n ip_cap ip_kids ip_keys
    ip_p ip_acc ip_f ip_cont ip_ok ip_tr ip_D ip_Lam ip_peak ip_cnt ip_fail ip_ran].
  split.
  { split; [apply KQ; [lia | cbn; lia | exact Vq2]|].
    split; [apply KQ; [lia | cbn; lia | exact Vq82]|].
    split; [apply KQ; [lia | cbn; lia | exact Vq162]|].
    split; [apply (rd_rw_keep segs _ _ q 24 RWq2); apply KK; intros z Hz; split; [lia|]; unfold X; lia|].
    split; [exact Hq8|]. split; [exact Ht0|]. split; [exact Ht62|]. split; [lia|]. split; [exact Hlen|].
    split; [exact (proj1 Hsrc')|]. split; [exact Hqt|].
    unfold PjGrammar.MAXD in Hd. lia. }
  split; [exact HRAq'|]. split; [exact Hsrc'|]. split; [exact Hhome'|]. split; [exact HLED'|].
  split; [rewrite Hfrs2; exact HFR|].
  change (rest_atR tb text P) with y. lia. }
split.
{ unfold vrd_ijrn.
  cbn [ie_ly ie_S ie_Hp ie_W ie_regs ie_mem ie_md ie_ch ie_Lam ie_peak ie_cnt ie_fail ie_ran ie_most ie_own ie_e ie_q ie_text ie_len
    ie_p ie_d ie_tb ie_v ie_o ie_ch2 ie_CW ip_fx ip_ly ip_S ip_Hp ip_W ip_regs ip_mem ip_md ip_k ip_n ip_cap ip_kids ip_keys
    ip_p ip_acc ip_f ip_cont ip_ok ip_tr ip_D ip_Lam ip_peak ip_cnt ip_fail ip_ran].
  (* The kit's cut: the position's journal is at the budget CW (VrdIElem.vrd_ijrn); the prologue stored nothing, so the
     empty budget widens to it (YCbqG.ajx_budgetR over YCbqG.wild_incl_mono); both at wle' (grow's text) *)
  split; [exact (ajx_budgetR CW HJ1' (wild_incl_mono _ _ [] CW (incl_nil_l CW) (ajxR_wild HJ1')))|].
  split; [intros a Ha Hn; rewrite (KA a ltac:(lia) ltac:(unfold X; lia)); exact (HWINe a Ha Hn)|].
  split; [exact Hfrm|].
  split; [intros r _; reflexivity|].
  split.
  { intros a Hro Hno Herr.
    assert (Hi : in_img segs a).
    { destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (@pa_relro_img _ _ PI_prog_A a Hr)]. }
    assert (Hcl : ~ YI16.sink_open_fp (rd_fp q v)).
    { apply sink_closed_pos. unfold rd_fp. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; lia. }
    pose proof (ajxR_img HJ1') as Himgc.
    rewrite (Himgc a Hi Hno Herr (fun Hp => H_pst_ro a Hp Hro) (fp_spares_closed (rd_fp q v) a Hcl)).
    exact (HROD a Hro Hno Herr). }
  split; [exact HBM2|].
  exists ch1. split; [exact Hch1 | reflexivity]. }
assert (HM : forall okt r t ok2,
  PjGrammar.jrl prh_jr_strtod (S (2 * length x + 1)) (S d) o 0 0 [] y okt = (r, t, ok2) ->
  PjGrammar.jr_items prh_jr_strtod d o x ([] ++ okt) = (r, [] ++ t, ok2)).
{ intros okt r t ok2 Hj. cbn [app]. rewrite (vrd_items_go d o x okt Hd Hnc), Hsk. exact Hj. }
pose proof (vrd_jr_items_after_grow d o x [] okg [] trg (2 * length x + 1) 0 0 8 [] y HG HM) as Hfac.
assert (Hgr : PjGrammar.grow o 0 0 [] = (Some 8%nat, trg, [])) by (rewrite vi_grow_granted, Htrg; reflexivity).
assert (Hgt : prhPi_gtrace d o x =
  trg ++ snd (fst (vrd_jtail (S d) o 0 8 [] (2 * length x + 1) y []))).
{ unfold prhPi_gtrace. rewrite (vrd_items_go d o x [] Hd Hnc), Hsk.
  rewrite (vi_jrl_gsplit (2 * length x + 1) (S d) o 0 0 [] y 8 trg Hgr). reflexivity. }
split.
{ unfold vrd_imodel.
  cbn [ie_ly ie_S ie_Hp ie_W ie_regs ie_mem ie_md ie_ch ie_Lam ie_peak ie_cnt ie_fail ie_ran ie_most ie_own ie_e ie_q ie_text ie_len
    ie_p ie_d ie_tb ie_v ie_o ie_ch2 ip_fx ip_ly ip_S ip_Hp ip_W
    ip_regs ip_mem ip_md ip_k ip_n ip_cap ip_kids ip_keys ip_p ip_acc ip_f ip_cont ip_ok ip_tr ip_D ip_Lam ip_peak
    ip_cnt ip_fail ip_ran].
  split; [exact Hokg|].
  split; [intros okr; exact (Hfac okr)|].
  split; [exact HLM2|].
  split.
  { (* RBase's restated vi_room_after (the kit's cut: the live room moves by the live-request Permutation, grow's post) *)
    apply (vi_room_after Sa S2 trg); [rewrite <- Hgt; exact HROOM | exact Hrl2 | exact HLV]. }
  split; [change (rest_atR tb text P) with y; lia|].
  split; [exact Hbb2|].
  split; [constructor|].
  split; [exact HlsD|].
  split; [exact HXF|]. split; [exact HLV | exact HHU]. }
split; [cbn [ip_n ip_cap]; lia|].
split; [reflexivity|].
(* The kit's cut, THE BATCH KIT'S LAYER after the first grow: cap = 8 = ncap 1, no member yet, the order list empty, and the model's
   free list at jfl's body after the grow (jf_cont's loop arm, the grow granted) *)
split; [reflexivity|].
split; [unfold vrd_incaps; cbn [ip_acc rev pj_kidsR]; exact I|].
exists []. split.
- intros _ nn _. exists [], []. cbn [ip_D ip_kids ip_keys ip_cap ip_n ie_o vrd_ient_of].
  split; [rewrite app_nil_l, app_nil_r; exact HDp|].
  split; [cbn [Z.to_nat PRH_PjOrder.pf_oitemsR]; split; reflexivity | reflexivity].
- intros okr. cbn [ip_ok ip_f ip_n ip_cap ie_d ie_o ie_tb ie_text ie_p vrd_ient_of].
  transitivity (PresetReqAt.jfl ReaderRes.jr_strtod (S (2 * length x + 1)) (S d) o 0 0 [] (PjGrammar.skip (tl x))
                  (okg ++ okr)); [apply vrd_frees_go; [exact Hd | exact Hnc]|].
  rewrite Hsk, vrd_jfl_unfold, (HG okr). reflexivity.
Qed.

(* D3's GRANTED TAIL in the generic form: row 92 with a0 = 0 after a granted first grow, rows 92..107 by vrd_itail_inv
   (P carried by the run), then the loop head by vrd_ielem_entry *)
Lemma vrd_igrant_inv : forall (Pm : (word -> option byte) -> Prop), srr_inv_laws segs Pm ->
  forall d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v
    P regsC MC mdc W2 ly2 S2 Hp2 regs2 mem2 md2 k1 kids keys D trg okg Lam' peak' cnt',
  vrd_ipre d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v ->
  (d < PjGrammar.MAXD)%nat ->
  vrd_imid d o e q text len v regs0 ly Sa Hp W mem0 md0 P regsC MC mdc ->
  p + 1 <= P <= text + len -> PjGrammar.skip (tl (rest_atR tb text p)) = rest_atR tb text P ->
  (forall r, PjGrammar.skip (tl (rest_atR tb text p)) <> PjGrammar.closer o :: r) ->
  ajournal_xR (SK := SK) segs B prh_pst ARx (wle' segs YGcfRehidePost.RZ_cf) (STK_parse_items d + e) (spZ regs0 + e)
    (rd_fp q v) ly Sa Hp W mem0 md0 [] ly2 S2 Hp2 W2 mem2 md2 (0 + k1) ->
  ajournal_xR (SK := SK) segs B prh_pst ARx (wle' segs YGcfRehidePost.RZ_cf) (STK_grow + (e + 144)) (spZ regs0 + e)
    (vrd_gfp (if o then 6 else 5) 0 0 0 v) ly Sa Hp W MC mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  (forall a, spZ regs0 + e + - (e + 144) <= a < spZ regs0 + e -> ~ inFP (vrd_gfp (if o then 6 else 5) 0 0 0 v) a ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W) MC a) ->
  aregs_preserved regsC regs2 -> getr regs2 10 = w64 0 ->
  pj_hdrR segs (mrestrict (w_H W2) mem2) v (if o then 6 else 5) 0 0 kids keys 0 8 ->
  prh_ledger B ly2 S2 Hp2 W2 mem2 Lam' peak' cnt' fail ran most own -> cnt' <= cnt + 2 ->
  rd_ledger_move Lam peak cnt fail ran most okg (prhPi_gtrace d o (rest_atR tb text p)) trg D Lam' peak' cnt' fail ran ->
  Ledger.lsum D = PjGrammar.held trg ->
  rd_blocks_move B ly Sa ly2 S2 D trg (rest_atR tb text p) d ->
  Permutation Lam' (D ++ Lam) ->
  Permutation D (kids_blkR kids 8 ++ keys_blkR (if o then 6 else 5) keys 8) ->
  okg = repeat true (PjGrammar.calls trg) ->
  (forall okt, PjGrammar.grow o 0 0 (okg ++ okt) = (Some 8%nat, trg, okt)) ->
  trg = prhPg_gtrace o 0 0 ->
  blocks_bytes S2 <= blocks_bytes Sa + prh_held trg -> room_live_cf S2 ->
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist Sa ->
     PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs trg) ->
     exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (PresetReqAt.rd_hevs trg))%nat H0 hist' S2) ->
  Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S2))
    (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf Sa)) (PresetReqAt.rd_hevs trg)) ->
  PresetHullBudget.hull_used Sa S2 (PresetReqAt.rd_hevs trg) ->
  (o = false -> keys = 0) ->
  Pm mem2 ->
  SRr' segs YGcfRehidePost.RZ_cf W2
    (mkCfg (YK11.mkst regs2 (Z_to_bv 64 (BASE + (PI_GROWRET - A_prog_base))) mem2 (YK11.seg_rom segs)) md2)
    (fun W' c' => vrd_iQall d o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v W' c' /\
       Pm (ms_mem (cfg_ms c'))).
Proof.
intros Pm PLAW d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v P regsC MC mdc W2 ly2
  S2 Hp2 regs2 mem2 md2 k1 kids keys D trg okg Lam' peak' cnt' HPRE Hd HMID HP Hsk Hnc HJ1 HJ2 HWIN2 HPR Ha0 Hhdr2
  HLED2 Hcnt' HLM2 HlsD HBM2 HLp' HDp Hokg HG Htrg Hbb2 Hrl2 HXF HLV HHU Hk0 HPM.
pose proof (vrd_ipre_prj d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v HPRE)
  as (HAFN & HROD & Hshi64 & Hfrm & HAR & Hal16 & Hceil & Hslo & Hshi & H47 & Htop & Htop' & Hpres & He0 & He16 & Hetop &
      Hepres & Hspq & Hqe & Hq8 & Ht0 & Ht62 & Htp & Hlen & Hqt & Hd32 & Hv4096 & Hv8 & HAMv & HNv & HRAv & HZv & Hrwv &
      HATv & Hqv & Htv & Hvw & HLED & HdM & Hcnt & HSRC & HHOME & HRAq & HCE & H10 & H11 & H12 & Hpe & Hop & HROOM & HFR).
destruct (vrd_after92 d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v P regsC MC mdc W2
  ly2 S2 Hp2 regs2 mem2 md2 (0 + k1) HPRE HMID HJ1 HWIN2 HPR)
  as (Hsp2 & HSV2 & Hgp2 & Htp2 & H182 & H82 & H92 & H192 & H202 & H212 & H222 & H232 & H262 & H272 & HWINe & Vq2 &
      Vq82 & Vq162 & RWq2 & Hpr2 & HFV).
pose proof (vrd_stk_ge d) as HSTK. pose proof H_img as (Himg1 & Himg2 & Himg3). unfold PI_FRAME in HSTK.
pose proof HMID as (HAT & _).
pose proof HAT as (_ & Hs1 & Hs2 & Hs16 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold amem_range in HAMv.
apply (vrd_itail_inv Pm PLAW d e q v regs0 regs2 ly Sa Hp W mem0 md0 W2 ly2 S2 Hp2 mem2 md2 (0 + k1) _ Hsp2 Hs1 Hs2 Hs16
  Ha0 H202 H262 ltac:(lia) ltac:(lia) ltac:(lia) He0 HJ1 HPM).
intros regs' mem' md' HKr R18 R21 R22 R24 R25 C8 C16 C24 C32 HKM HJ1' HPM'.
destruct (vrd_ielem_entry d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v
  P regsC MC mdc W2 ly2 S2 Hp2 regs2 mem2 md2 k1 regs' mem' md' kids keys D trg okg Lam' peak' cnt'
  HPRE Hd HMID HP Hsk Hnc HJ1 HJ2 HWIN2 HPR HKr R18 R21 R22 R24 R25 C8 C16 C24 C32 HKM HJ1' Hhdr2 HLED2 Hcnt' HLM2
  HlsD HBM2 HLp' HDp Hokg HG Htrg Hbb2 Hrl2 HXF HLV HHU Hk0) as (ch2 & HE).
split; [|exact HPM'].
left. exists ch2, (MkIPos fx ly2 S2 Hp2 W2 regs' mem' md' (0 + k1) 0 8 kids keys P []
  (2 * length (rest_atR tb text p) + 1) (vrd_jtail (S d) o 0 8 [] (2 * length (rest_atR tb text p) + 1)
  (rest_atR tb text P)) okg trg D Lam' peak' cnt' fail ran).
split; [reflexivity|]. split; [reflexivity|]. split; [exact HE | exact Hnc].
Qed.

(* D3, grow's arm 4 (an array: the kids realloc granted to k'): the model's grant package, then vrd_igrant_inv *)
Lemma vrd_igrant_arr : forall (Pm : (word -> option byte) -> Prop), srr_inv_laws segs Pm ->
  forall d CTX ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v
    P regsC MC mdc W2 ly2 S2 Hp2 regs2 mem2 md2 k1 k' Lam',
  vrd_ipre d CTX false ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v ->
  (d < PjGrammar.MAXD)%nat ->
  vrd_imid d false e q text len v regs0 ly Sa Hp W mem0 md0 P regsC MC mdc ->
  p + 1 <= P <= text + len -> PjGrammar.skip (tl (rest_atR tb text p)) = rest_atR tb text P ->
  (forall r, PjGrammar.skip (tl (rest_atR tb text p)) <> PjGrammar.closer false :: r) ->
  ajournal_xR (SK := SK) segs B prh_pst ARx (wle' segs YGcfRehidePost.RZ_cf) (STK_parse_items d + e) (spZ regs0 + e)
    (rd_fp q v) ly Sa Hp W mem0 md0 [] ly2 S2 Hp2 W2 mem2 md2 (0 + k1) ->
  ajournal_xR (SK := SK) segs B prh_pst ARx (wle' segs YGcfRehidePost.RZ_cf) (STK_grow + (e + 144)) (spZ regs0 + e)
    (vrd_gfp 5 0 0 0 v) ly Sa Hp W MC mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  (forall a, spZ regs0 + e + - (e + 144) <= a < spZ regs0 + e -> ~ inFP (vrd_gfp 5 0 0 0 v) a ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W) MC a) ->
  aregs_preserved regsC regs2 -> getr regs2 10 = w64 0 -> cnt <> fail ->
  prhReader_swap B ly Sa Hp Lam ly2 S2 Hp2 Lam' (kids_blkR 0 0) [(k', 56 * cap2R 0)] ->
  prh_ledger B ly2 S2 Hp2 W2 mem2 Lam' (Z.max peak (Ledger.lsum Lam')) (cnt + 1) fail ran most own ->
  pj_hdrR segs (mrestrict (w_H W2) mem2) v 5 0 0 k' 0 0 (cap2R 0) ->
  blocks_bytes S2 <= blocks_bytes Sa + prh_held (prhPg_gtrace (5 =? 6) 0 0) -> room_live_cf S2 ->
  (* grow's hull use over its all-granted events *)
  PresetHullBudget.hull_used Sa S2 (prhPg_evs (5 =? 6) 0 0 []) ->
  (* grow's arm 4: the kids realloc's event (outcomes [true]) *)
  Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S2))
    (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf Sa)) (prhPg_evs (5 =? 6) 0 0 [true])) ->
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist Sa ->
     PRH_Base.prh_run_at sm x os i (prhPg_evs (5 =? 6) 0 0 [true]) ->
     exists hist', PresetRoomPos.iface_room_pos sm x os
       (i + length (prhPg_evs (5 =? 6)%Z 0 0 [true]))%nat H0 hist' S2) ->
  Pm mem2 ->
  SRr' segs YGcfRehidePost.RZ_cf W2
    (mkCfg (YK11.mkst regs2 (Z_to_bv 64 (BASE + (PI_GROWRET - A_prog_base))) mem2 (YK11.seg_rom segs)) md2)
    (fun W' c' => vrd_iQall d false ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v W' c' /\
       Pm (ms_mem (cfg_ms c'))).
Proof.
intros Pm PLAW d CTX ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v P regsC MC mdc W2 ly2
  S2 Hp2 regs2 mem2 md2 k1 k' Lam' HPRE Hd HMID HP Hsk Hnc HJ1 HJ2 HWIN2 HPR Ha0 Hcf HSW HLED2 Hhdr2 Hbb2 Hrl2 HHUg HLV
  HXF HPM.
pose proof (vrd_ipre_prj d CTX false ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v HPRE)
  as (HAFN & HROD & Hshi64 & Hfrm & HAR & Hal16 & Hceil & Hslo & Hshi & H47 & Htop & Htop' & Hpres & He0 & He16 & Hetop &
      Hepres & Hspq & Hqe & Hq8 & Ht0 & Ht62 & Htp & Hlen & Hqt & Hd32 & Hv4096 & Hv8 & HAMv & HNv & HRAv & HZv & Hrwv &
      HATv & Hqv & Htv & Hvw & HLED & HdM & Hcnt & HSRC & HHOME & HRAq & HCE & H10 & H11 & H12 & Hpe & Hop & HROOM & HFR).
destruct (vrd_led_bounds _ _ _ _ _ _ _ _ _ _ _ _ HLED) as (HLp & HLpk & HLc & HLf & HLr).
destruct (vrd_imove_nil d CTX false ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v HPRE)
  as (HLM0 & HBM0 & _ & _).
pose proof (ajxR_ar HJ1) as HAR2. pose proof (ajxR_ly HJ1) as Hly2.
pose proof (ajxR_frs HJ2) as Hfrs2.
pose proof (@cf_head_nonneg cp) as Hcf0.
change (56 * cap2R 0) with 448 in HSW. change (cap2R 0) with 8 in Hhdr2.
destruct HSW as ((bl & Hsw1 & Hsw2) & _ & (Lam1 & HL1a & HL1b)).
set (trg := [PjGrammar.EGrow 0 448]).
assert (Htrp : hpeakR trg = 448) by (vm_compute; reflexivity).
assert (Htrh : PjGrammar.held trg = 448) by (vm_compute; reflexivity).
assert (Htrc : PjGrammar.calls trg = 1%nat) by reflexivity.
assert (Hrl1 : (1 <= length (rest_atR tb text p))%nat).
{ pose proof (vrd_rest_len tb text p ltac:(lia)) as Hr. lia. }
assert (HLp' : Permutation Lam' ([(k', 448)] ++ Lam)).
{ eapply Permutation_trans; [exact HL1b|]. cbn [app]. apply perm_skip.
  apply Permutation_sym. cbn [kids_blkR Z.eqb app] in HL1a. exact HL1a. }
assert (HLs' : Ledger.lsum Lam' = Ledger.lsum Lam + 448).
{ rewrite (vi_lsum_perm _ _ HLp'). cbn [app Ledger.lsum]. lia. }
(* the call's granted trace begins with the array grow's granted realloc *)
destruct (vrd_gtrace_grow d false (rest_atR tb text p) Hd Hnc) as (tg & Htg).
assert (HG : prhPi_gtrace d false (rest_atR tb text p) = [] ++ trg ++ tg) by (rewrite Htg; reflexivity).
assert (HSWm : rd_ledger_move Lam peak cnt fail ran most (repeat true (PjGrammar.calls []) ++ [true])
                 (prhPi_gtrace d false (rest_atR tb text p)) ([] ++ trg)
                 ([(k', 448)] ++ []) Lam' (Z.max peak (Ledger.lsum Lam')) (cnt + 1) fail ran /\
               Ledger.lsum ([(k', 448)] ++ []) = PjGrammar.held ([] ++ trg)).
{ apply (vi_grow_swap_step Lam peak cnt fail ran most (prhPi_gtrace d false (rest_atR tb text p)) [] [] Lam peak cnt
           fail ran (kids_blkR 0 0) [(k', 448)] [] Lam1 Lam' [true] trg trg tg (Z.max peak (Ledger.lsum Lam'))
           (cnt + 1) fail ran HLM0 eq_refl ltac:(cbn; apply perm_nil) HL1a HL1b ltac:(lia));
    [ | | | | | | | | | exact HG | lia ].
  - rewrite Htrc. cbn [PjGrammar.calls]. lia.
  - rewrite Htrc. reflexivity.
  - rewrite Htrc. apply vi_oks_true. intros i Hi He. assert (i = 0%nat) by lia. subst i. cbn in He. lia.
  - rewrite Htrc. reflexivity.
  - rewrite Htrc. apply vi_fa_none. intros i Hi He. assert (i = 0%nat) by lia. subst i. cbn in He. lia.
  - intros s L Hs. cbn [trg fold_left lsz_evR kids_blkR Z.eqb map snd app] in Hs |- *.
    change (Z.of_nat 448) with 448. apply perm_skip. exact Hs.
  - reflexivity.
  - reflexivity.
  - rewrite Htrp, Htrc, vrd_rpeak1, (vrd_refused_t [true] cnt fail 0 eq_refl), HLs'. cbv iota beta. lia. }
cbn [repeat PjGrammar.calls app] in HSWm. destruct HSWm as (HLM2 & HlsD).
assert (HBM2 : rd_blocks_move B ly Sa ly2 S2 [(k', 448)] trg (rest_atR tb text p) d).
{ apply (vi_swap_move B ARx LAWS ly Sa ly Sa ly2 S2 Hp2 W2 mem2 md2 [] [] trg (rest_atR tb text p) d (kids_blkR 0 0)
           [(k', 448)] [] bl HBM0 ltac:(cbn; apply perm_nil) Hsw1 Hsw2 HAR2).
  - intros b [<- | []]. cbn [snd]. lia.
  - intros b b' _ Hb'. cbn in Hb'. destruct Hb'.
  - rewrite Hfrs2. reflexivity.
  - rewrite Htrp. lia. }
assert (Hev : prhPg_evs (5 =? 6) 0 0 [true] = PresetReqAt.rd_hevs trg) by exact (proj1 (proj2 (vrd_gevs_arm false))).
rewrite Hev in HLV, HXF.
(* the array's all-granted list is its one granted realloc: grow's hull use is over trg's events *)
change (prhPg_evs (5 =? 6) 0 0 []) with (prhPg_evs (5 =? 6) 0 0 [true]) in HHUg. rewrite Hev in HHUg.
apply (vrd_igrant_inv Pm PLAW d CTX false ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v
  P regsC MC mdc W2 ly2 S2 Hp2 regs2 mem2 md2 k1 k' 0 [(k', 448)] trg [true] Lam' (Z.max peak (Ledger.lsum Lam'))
  (cnt + 1) HPRE Hd HMID HP Hsk Hnc HJ1 HJ2 HWIN2 HPR Ha0 Hhdr2 HLED2 ltac:(lia) HLM2 HlsD HBM2 HLp'
  ltac:(apply Permutation_refl) eq_refl ltac:(intros okt; reflexivity) eq_refl Hbb2 Hrl2 HXF HLV HHUg (fun _ => eq_refl)
  HPM).
Qed.

(* D3, grow's arm 7 (an object: the kids realloc granted to k', the keys realloc to y'): the model's grant package,
   then vrd_igrant_inv *)
Lemma vrd_igrant_obj : forall (Pm : (word -> option byte) -> Prop), srr_inv_laws segs Pm ->
  forall d CTX ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v
    P regsC MC mdc W2 ly2 S2 Hp2 regs2 mem2 md2 k1 k' y' Lam',
  vrd_ipre d CTX true ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v ->
  (d < PjGrammar.MAXD)%nat ->
  vrd_imid d true e q text len v regs0 ly Sa Hp W mem0 md0 P regsC MC mdc ->
  p + 1 <= P <= text + len -> PjGrammar.skip (tl (rest_atR tb text p)) = rest_atR tb text P ->
  (forall r, PjGrammar.skip (tl (rest_atR tb text p)) <> PjGrammar.closer true :: r) ->
  ajournal_xR (SK := SK) segs B prh_pst ARx (wle' segs YGcfRehidePost.RZ_cf) (STK_parse_items d + e) (spZ regs0 + e)
    (rd_fp q v) ly Sa Hp W mem0 md0 [] ly2 S2 Hp2 W2 mem2 md2 (0 + k1) ->
  ajournal_xR (SK := SK) segs B prh_pst ARx (wle' segs YGcfRehidePost.RZ_cf) (STK_grow + (e + 144)) (spZ regs0 + e)
    (vrd_gfp 6 0 0 0 v) ly Sa Hp W MC mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  (forall a, spZ regs0 + e + - (e + 144) <= a < spZ regs0 + e -> ~ inFP (vrd_gfp 6 0 0 0 v) a ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W) MC a) ->
  aregs_preserved regsC regs2 -> getr regs2 10 = w64 0 -> cnt <> fail -> cnt + 1 <> fail ->
  prhReader_swap B ly Sa Hp Lam ly2 S2 Hp2 Lam' (kids_blkR 0 0 ++ keys_blkR 6 0 0)
    [(y', 8 * cap2R 0); (k', 56 * cap2R 0)] ->
  prh_ledger B ly2 S2 Hp2 W2 mem2 Lam'
    (Z.max peak (Z.max (Ledger.lsum Lam + 56 * (cap2R 0 - 0)) (Ledger.lsum Lam'))) (cnt + 2) fail ran most own ->
  pj_hdrR segs (mrestrict (w_H W2) mem2) v 6 0 0 k' y' 0 (cap2R 0) ->
  blocks_bytes S2 <= blocks_bytes Sa + prh_held (prhPg_gtrace (6 =? 6) 0 0) -> room_live_cf S2 ->
  (* grow's hull use over its all-granted events *)
  PresetHullBudget.hull_used Sa S2 (prhPg_evs (6 =? 6) 0 0 []) ->
  (* grow's arm 7: both reallocs' events (outcomes [true; true]) *)
  Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S2))
    (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf Sa)) (prhPg_evs (6 =? 6) 0 0 [true; true])) ->
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist Sa ->
     PRH_Base.prh_run_at sm x os i (prhPg_evs (6 =? 6) 0 0 [true; true]) ->
     exists hist', PresetRoomPos.iface_room_pos sm x os
       (i + length (prhPg_evs (6 =? 6)%Z 0 0 [true; true]))%nat H0 hist' S2) ->
  Pm mem2 ->
  SRr' segs YGcfRehidePost.RZ_cf W2
    (mkCfg (YK11.mkst regs2 (Z_to_bv 64 (BASE + (PI_GROWRET - A_prog_base))) mem2 (YK11.seg_rom segs)) md2)
    (fun W' c' => vrd_iQall d true ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v W' c' /\
       Pm (ms_mem (cfg_ms c'))).
Proof.
intros Pm PLAW d CTX ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v P regsC MC mdc W2 ly2
  S2 Hp2 regs2 mem2 md2 k1 k' y' Lam' HPRE Hd HMID HP Hsk Hnc HJ1 HJ2 HWIN2 HPR Ha0 Hcf Hcf1 HSW HLED2 Hhdr2 Hbb2
  Hrl2 HHUg HLV HXF HPM.
pose proof (vrd_ipre_prj d CTX true ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v HPRE)
  as (HAFN & HROD & Hshi64 & Hfrm & HAR & Hal16 & Hceil & Hslo & Hshi & H47 & Htop & Htop' & Hpres & He0 & He16 & Hetop &
      Hepres & Hspq & Hqe & Hq8 & Ht0 & Ht62 & Htp & Hlen & Hqt & Hd32 & Hv4096 & Hv8 & HAMv & HNv & HRAv & HZv & Hrwv &
      HATv & Hqv & Htv & Hvw & HLED & HdM & Hcnt & HSRC & HHOME & HRAq & HCE & H10 & H11 & H12 & Hpe & Hop & HROOM & HFR).
destruct (vrd_led_bounds _ _ _ _ _ _ _ _ _ _ _ _ HLED) as (HLp & HLpk & HLc & HLf & HLr).
destruct (vrd_imove_nil d CTX true ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v HPRE)
  as (HLM0 & HBM0 & _ & _).
pose proof (ajxR_ar HJ1) as HAR2. pose proof (ajxR_ly HJ1) as Hly2.
pose proof (ajxR_frs HJ2) as Hfrs2.
pose proof (@cf_head_nonneg cp) as Hcf0.
change (8 * cap2R 0) with 64 in HSW. change (56 * cap2R 0) with 448 in HSW.
change (56 * (cap2R 0 - 0)) with 448 in HLED2. change (cap2R 0) with 8 in Hhdr2.
destruct HSW as ((bl & Hsw1 & Hsw2) & _ & (Lam1 & HL1a & HL1b)).
set (trg := [PjGrammar.EGrow 0 448; PjGrammar.EGrow 0 64]).
assert (Htrp : hpeakR trg = 512) by (vm_compute; reflexivity).
assert (Htrh : PjGrammar.held trg = 512) by (vm_compute; reflexivity).
assert (Htrc : PjGrammar.calls trg = 2%nat) by reflexivity.
assert (Hrl1 : (1 <= length (rest_atR tb text p))%nat).
{ pose proof (vrd_rest_len tb text p ltac:(lia)) as Hr. lia. }
assert (HLp' : Permutation Lam' ([(y', 64); (k', 448)] ++ Lam)).
{ eapply Permutation_trans; [exact HL1b|]. cbn [app]. apply perm_skip. apply perm_skip.
  apply Permutation_sym. cbn [kids_blkR keys_blkR Z.eqb orb negb app] in HL1a. exact HL1a. }
assert (HLs' : Ledger.lsum Lam' = Ledger.lsum Lam + 512).
{ rewrite (vi_lsum_perm _ _ HLp'). cbn [app Ledger.lsum]. lia. }
(* the call's granted trace begins with the object grow's two granted reallocs *)
destruct (vrd_gtrace_grow d true (rest_atR tb text p) Hd Hnc) as (tg & Htg).
assert (HG : prhPi_gtrace d true (rest_atR tb text p) = [] ++ trg ++ tg) by (rewrite Htg; reflexivity).
assert (HSWm : rd_ledger_move Lam peak cnt fail ran most (repeat true (PjGrammar.calls []) ++ [true; true])
                 (prhPi_gtrace d true (rest_atR tb text p)) ([] ++ trg)
                 ([(y', 64); (k', 448)] ++ []) Lam' (Z.max peak (Z.max (Ledger.lsum Lam + 448) (Ledger.lsum Lam')))
                 (cnt + 2) fail ran /\
               Ledger.lsum ([(y', 64); (k', 448)] ++ []) = PjGrammar.held ([] ++ trg)).
{ apply (vi_grow_swap_step Lam peak cnt fail ran most (prhPi_gtrace d true (rest_atR tb text p)) [] [] Lam peak cnt
           fail ran (kids_blkR 0 0 ++ keys_blkR 6 0 0) [(y', 64); (k', 448)] [] Lam1 Lam' [true; true] trg trg tg
           (Z.max peak (Z.max (Ledger.lsum Lam + 448) (Ledger.lsum Lam'))) (cnt + 2) fail ran HLM0 eq_refl
           ltac:(cbn; apply perm_nil) HL1a HL1b ltac:(lia));
    [ | | | | | | | | | exact HG | lia ].
  - rewrite Htrc. cbn [PjGrammar.calls]. lia.
  - rewrite Htrc. reflexivity.
  - rewrite Htrc. apply vi_oks_true. intros i Hi He. destruct i as [|[|i]]; cbn in He; lia.
  - rewrite Htrc. reflexivity.
  - rewrite Htrc. apply vi_fa_none. intros i Hi He. destruct i as [|[|i]]; cbn in He; lia.
  - intros s L Hs. cbn [trg fold_left lsz_evR kids_blkR keys_blkR Z.eqb orb negb map snd app] in Hs |- *.
    change (Z.of_nat 448) with 448. change (Z.of_nat 64) with 64. apply perm_skip. apply perm_skip. exact Hs.
  - reflexivity.
  - reflexivity.
  - rewrite Htrp, Htrc, vrd_rpeak2, (vrd_refused_t [true; true] cnt fail 0 eq_refl),
      (vrd_refused_t [true; true] cnt fail 1 eq_refl), HLs'. cbv iota beta. lia. }
cbn [repeat PjGrammar.calls app] in HSWm. destruct HSWm as (HLM2 & HlsD).
assert (HBM2 : rd_blocks_move B ly Sa ly2 S2 [(y', 64); (k', 448)] trg (rest_atR tb text p) d).
{ apply (vi_swap_move B ARx LAWS ly Sa ly Sa ly2 S2 Hp2 W2 mem2 md2 [] [] trg (rest_atR tb text p) d
           (kids_blkR 0 0 ++ keys_blkR 6 0 0) [(y', 64); (k', 448)] [] bl HBM0 ltac:(cbn; apply perm_nil) Hsw1 Hsw2 HAR2).
  - intros b [<- | [<- | []]]; cbn [snd]; lia.
  - intros b b' _ Hb'. cbn in Hb'. destruct Hb'.
  - rewrite Hfrs2. reflexivity.
  - rewrite Htrp. lia. }
assert (Hev : prhPg_evs (6 =? 6) 0 0 [true; true] = PresetReqAt.rd_hevs trg)
  by exact (proj2 (proj2 (proj2 (vrd_gevs_arm true)))).
rewrite Hev in HLV, HXF.
(* the object's all-granted list is its two granted reallocs: grow's hull use is over trg's events *)
change (prhPg_evs (6 =? 6) 0 0 []) with (prhPg_evs (6 =? 6) 0 0 [true; true]) in HHUg. rewrite Hev in HHUg.
apply (vrd_igrant_inv Pm PLAW d CTX true ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v
  P regsC MC mdc W2 ly2 S2 Hp2 regs2 mem2 md2 k1 k' y' [(y', 64); (k', 448)] trg [true; true] Lam'
  (Z.max peak (Z.max (Ledger.lsum Lam + 448) (Ledger.lsum Lam'))) (cnt + 2) HPRE Hd HMID HP Hsk Hnc HJ1 HJ2 HWIN2
  HPR Ha0 Hhdr2 HLED2 ltac:(lia) HLM2 HlsD HBM2 HLp' ltac:(apply perm_swap) eq_refl ltac:(intros okt; reflexivity)
  eq_refl Hbb2 Hrl2 HXF HLV HHUg (fun Hf => match Hf with eq_refl => I end) HPM).
Qed.

(* D3 = vrd_iRet in the generic form: the state at row 92 after the first grow returned, by grow's seven arms at
   n = cap = 0 (arm 1, room left, is refuted by 0 < 0): the four refusals (arms 2, 3, 5, 6) through row 310 to the
   record post (vrd_iref_kids / vrd_iref_keys), the two grants (arms 4, 7) through rows 92..107 to the loop head
   (vrd_igrant_arr / vrd_igrant_obj). Call-free: the single srr_inv_laws premise. *)
Lemma vrd_iRet_inv : forall (Pm : (word -> option byte) -> Prop), srr_inv_laws segs Pm ->
  forall d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v,
  vrd_ipre d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v ->
  (d < PjGrammar.MAXD)%nat ->
  vrd_iRet_P Pm d o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v.
Proof.
intros Pm PLAW d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v HPRE Hd
  P regsC MC mdc W2 ly2 S2 Hp2 regs2 mem2 md2 k1 HMID HP Hsk Hnc Hle HJ1 HJ2 HWIN2 HPR HQ HPM.
unfold vrd_gpost, tgrP_Q, tgrP_A1, tgrP_A2, tgrP_A3, tgrP_A4, tgrP_A5, tgrP_A6, tgrP_A7 in HQ.
pose proof (vrd_ipre_prj d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v HPRE)
  as (HAFN & HROD & Hshi64 & Hfrm & HAR & Hal16 & Hceil & Hslo & Hshi & H47 & Htop & Htop' & Hpres & He0 & He16 & Hetop &
      Hepres & Hspq & Hqe & Hq8 & Ht0 & Ht62 & Htp & Hlen & Hqt & Hd32 & Hv4096 & Hv8 & HAMv & HNv & HRAv & HZv & Hrwv &
      HATv & Hqv & Htv & Hvw & HLED & HdM & Hcnt & HSRC & HHOME & HRAq & HCE & H10 & H11 & H12 & Hpe & Hop & HROOM & HFR).
destruct (vrd_led_bounds _ _ _ _ _ _ _ _ _ _ _ _ HLED) as (HLp & HLpk & HLc & HLf & HLr).
destruct HQ as (Hrl2 & Hhu2 & Hbb2 & [A1 | [A2 | [A3 | [A4 | [A5 | [A6 | A7]]]]]]).
- (* arm 1: n < cap, false at n = cap = 0 *)
  destruct A1 as (Hlt & _). lia.
- (* arm 2: the kids realloc set to fail *)
  destruct A2 as (_ & Hcf & Ha0 & _ & Eab & Ebb & HLED2 & Hhdr2 & _ & _ & HLV & HXF).
  apply (vrd_iref_kids Pm d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v P regsC MC
    mdc W2 ly2 S2 Hp2 regs2 mem2 md2 k1 peak (cnt + 1) SIZE_MAXZ ran HPRE Hd HMID HP Hnc HJ1 HJ2 HWIN2 HPR Ha0 Eab Ebb HLED2
    Hhdr2 Hrl2 Hhu2 HLV HXF); [ | | | exact HPM].
  + intros sm x0 os i H0 hist. exact (vrd_excl_fail d o (rest_atR tb text p) Sa cnt fail 0 Hd Hnc ltac:(cbn; lia)
      ltac:(destruct o; lia) sm x0 os i H0 hist).
  + exact (vrd_inj_kids_fail d o (rest_atR tb text p) Sa cnt fail Hcf).
  + exact (vrd_lm_kids_fail d o (rest_atR tb text p) Lam peak cnt fail ran most Hd Hnc ltac:(lia) ltac:(lia)
      ltac:(lia) Hcf).
- (* arm 3: the kids realloc refused by the allocator *)
  destruct A3 as (_ & Hcf & Ha0 & _ & Eab & Ebb & _ & _ & HEXg & HINJg & HLED2 & Hhdr2 & _ & _ & HLV & HXF).
  apply (vrd_iref_kids Pm d CTX o ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v P regsC MC
    mdc W2 ly2 S2 Hp2 regs2 mem2 md2 k1 _ _ _ _ HPRE Hd HMID HP Hnc HJ1 HJ2 HWIN2 HPR Ha0 Eab Ebb HLED2
    Hhdr2 Hrl2 Hhu2 HLV HXF); [ | | | exact HPM].
  + intros sm x0 os i H0 hist. exact (vrd_excl_grow d o (rest_atR tb text p) Sa Hd Hnc HEXg cnt fail sm x0 os i H0 hist).
  + exact (vrd_inj_kids_ref d o (rest_atR tb text p) Sa cnt fail Hd Hnc HEXg HINJg [false] [PjGrammar.EFail 448]).
  + exact (vrd_lm_kids_ref d o (rest_atR tb text p) Lam peak cnt fail ran most Hd Hnc ltac:(lia) ltac:(lia)
      ltac:(lia) Hcf).
- (* arm 4: an array's kids realloc granted *)
  destruct A4 as (_ & Hcf & Hty & Ha0 & k' & Lam' & _ & _ & HSW & HLED2 & _ & _ & _ & Hhdr2 & _ & HLV & HXF).
  destruct o; [exfalso; exact (Hty eq_refl)|].
  exact (vrd_igrant_arr Pm PLAW d CTX ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v
    P regsC MC mdc W2 ly2 S2 Hp2 regs2 mem2 md2 k1 k' Lam' HPRE Hd HMID HP Hsk Hnc HJ1 HJ2 HWIN2 HPR Ha0 Hcf HSW
    HLED2 Hhdr2 Hbb2 Hrl2 Hhu2 HLV HXF HPM).
- (* arm 5: an object's kids granted, its keys realloc set to fail *)
  destruct A5 as (_ & Hcf & Hty & Hcf1 & Ha0 & k' & Lam' & _ & _ & HSW & HLED2 & _ & _ & _ & Hhdr2 & HLV & HXF).
  destruct o; [|exfalso; discriminate Hty].
  apply (vrd_iref_keys Pm d CTX ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v P regsC MC
    mdc W2 ly2 S2 Hp2 regs2 mem2 md2 k1 k' Lam' _ _ _ _ HPRE Hd HMID HP Hnc HJ1 HJ2 HWIN2 HPR Ha0 Hcf HSW HLED2);
    [ | exact Hhdr2 | exact Hrl2 | exact Hhu2 | exact HLV | exact HXF | | | exact HPM].
  + left. split; [exact Hcf1|]. repeat split.
  + intros sm x0 os i H0 hist. exact (vrd_excl_fail d true (rest_atR tb text p) Sa cnt fail 1 Hd Hnc ltac:(cbn; lia)
      ltac:(cbn; lia) sm x0 os i H0 hist).
  + exact (vrd_inj_keys_fail d (rest_atR tb text p) Sa cnt fail Hcf1).
- (* arm 6: an object's kids granted, its keys realloc refused by the allocator *)
  destruct A6 as (_ & Hcf & Hty & Hcf1 & Ha0 & k' & Lam' & _ & _ & HSW & _ & _ & HEXg & HLED2 & _ & _ & _ & Hhdr2 &
    HLV & HXF).
  destruct o; [|exfalso; discriminate Hty].
  apply (vrd_iref_keys Pm d CTX ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v P regsC MC
    mdc W2 ly2 S2 Hp2 regs2 mem2 md2 k1 k' Lam' _ _ _ _ HPRE Hd HMID HP Hnc HJ1 HJ2 HWIN2 HPR Ha0 Hcf HSW HLED2);
    [ | exact Hhdr2 | exact Hrl2 | exact Hhu2 | exact HLV | exact HXF | | | exact HPM].
  + right. split; [exact Hcf1|]. repeat split.
  + intros sm x0 os i H0 hist. exact (vrd_excl_grow d true (rest_atR tb text p) Sa Hd Hnc HEXg cnt fail sm x0 os i H0 hist).
  + exact (vrd_inj_keys_ref d (rest_atR tb text p) Sa cnt fail Hd Hnc Hcf Hcf1 HEXg [true; false]
      [PjGrammar.EGrow 0 448; PjGrammar.EFail 64]).
- (* arm 7: an object's kids and keys reallocs granted *)
  destruct A7 as (_ & Hcf & Hty & Hcf1 & Ha0 & k' & y' & Lam' & _ & _ & _ & _ & HSW & HLED2 & _ & _ & _ & _ & _ & Hhdr2
    & _ & HLV & HXF).
  destruct o; [|exfalso; discriminate Hty].
  exact (vrd_igrant_obj Pm PLAW d CTX ly Sa Hp W regs0 mem0 md0 ch Lam peak cnt fail ran most own e q text len p tb v
    P regsC MC mdc W2 ly2 S2 Hp2 regs2 mem2 md2 k1 k' y' Lam' HPRE Hd HMID HP Hsk Hnc HJ1 HJ2 HWIN2 HPR Ha0 Hcf Hcf1
    HSW HLED2 Hhdr2 Hbb2 Hrl2 Hhu2 HLV HXF HPM).
Qed.

(* D3 as vrd_ipro_ok_of_iRet consumes it: vrd_iRet_inv at P := fun _ => True *)
Lemma vrd_iRet_ok : forall d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v,
  vrd_ipre d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v ->
  (d < PjGrammar.MAXD)%nat ->
  vrd_iRet d o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v.
Proof.
intros d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v HPRE Hd
  P regsC MC mdc W2 ly2 S2 Hp2 regs2 mem2 md2 k1 HMID HP Hsk Hnc Hle HJ1 HJ2 HWIN2 HPR HQ.
eapply (SRrG_mono segs (wle' segs YGcfRehidePost.RZ_cf)).
- exact (vrd_iRet_inv (fun _ => True) vrd_inv_true d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len
    p tb v HPRE Hd P regsC MC mdc W2 ly2 S2 Hp2 regs2 mem2 md2 k1 HMID HP Hsk Hnc Hle HJ1 HJ2 HWIN2 HPR HQ I).
- intros W' c' _ (H & _). exact H.
Qed.

(* F. THE SEGMENT LEMMA of this lane: parse_items' entry segment reaches the loop head or returns with the call's
   post (vrd_ipro_ok_of_iRet, closed by D3) *)
(* F IN THE GENERIC FORM: the segment master, crossing the first grow (srr_inv_call there) *)
Lemma vrd_ipro_ok_inv : forall (Pm : (word -> option byte) -> Prop), srr_inv_laws segs Pm -> srr_inv_call segs Pm ->
  forall d CTX, vrd_ipro_stmt_P Pm d CTX.
Proof.
intros Pm PLAW PCALL d CTX. apply (vrd_ipro_ok_of_iRet_inv Pm PLAW PCALL).
intros ly Sa Hp W regs mem md ch e q text len p tb v o Lam peak cnt fail ran most own HPRE Hd.
exact (vrd_iRet_inv Pm PLAW d CTX o ly Sa Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v HPRE Hd).
Qed.

Lemma vrd_ipro_ok : forall d CTX, vrd_ipro_stmt d CTX.
Proof.
intros d CTX ly Sa Hp W regs mem md ch e q text len p tb v o Lam peak cnt fail ran most own HPRE.
eapply (SRrG_mono segs (wle' segs YGcfRehidePost.RZ_cf));
  [exact (vrd_ipro_ok_inv (fun _ => True) vrd_inv_true vrd_inv_call_true d CTX ly Sa Hp W regs mem md ch e
  q text len p tb v o Lam peak cnt fail ran most own HPRE I)|].
intros W' c' _ (H & _). exact H.
Qed.

End a.
