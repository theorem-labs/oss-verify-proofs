(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACer.v, with its module paths and module names changed; 1338 of its 1373 lines of code are new or changed and 261 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_K.v; 1536 of its 1692 lines of code are new or changed and 1217 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_write_value.v, with its numbers changed; 107 of its 179 lines of code are new or changed and 1620 lines of the source are left out. *)
(* write_value's CONTAINER arms (array / object), fs.asan image A: the walk's symbolic states and the two call
   composition steps. MEASURED with the engine on the original fs.asan (a build machine, sha256 64b53ff8...): from the entry
   state the arms call put at 0x8418c (returning to 0x83e3c), then indent (0x8400c), per item put_string (0x84058),
   put of the separator (0x84068), write_value of the item (0x84088), put of the comma (0x83ffc), the closing indent
   (0x840cc), and TAIL-jump to put with the closing bracket.
   Rule 24 (proof-index v5 built 2026-10-28T21:58:24Z, exit 0): write_value has RELEASED proofs for fs's PLAIN
   and UBSAN builds only (lib/Prog, lib/U/Prog), none for ASan; they are templates, not drop-ins. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_rres FSW_ret
FSW_writer_tbl FSH_Fn_writer.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSH_Fn_reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterApp WriterValue PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ================= the container arms' constants (MEASURED) ================= *)
Definition WVC_F : Z := 176.                      (* FSH_Base.FRAME_write_value *)
Definition WVC_CEIL : Z := 140737479966720.       (* 0x7fffff800000: alloc_ceiling's bound (YCbq.v asan_consts) *)
Definition WVC_R_OPEN  : Z := 0x83e3c.            (* return of the put of '[' / '{' *)
Definition WVC_R_IND   : Z := 0x8400c.            (* return of the per-item indent *)
Definition WVC_R_KEY   : Z := 0x84058.            (* return of put_string of the key (object) *)
Definition WVC_R_SEP   : Z := 0x84068.            (* return of the put of ':' / ': ' (object) *)
Definition WVC_R_ITEM  : Z := 0x84088.            (* return of the recursive write_value of the item *)
Definition WVC_R_COMMA : Z := 0x83ffc.            (* return of the put of ',' *)
Definition WVC_R_CLOSE : Z := 0x840cc.            (* return of the closing indent *)
Definition WV_CONT_RAS : list Z :=
  [WVC_R_OPEN; WVC_R_IND; WVC_R_KEY; WVC_R_SEP; WVC_R_ITEM; WVC_R_COMMA; WVC_R_CLOSE].
(* the read-only literals the arms put (FSH_Rt.FS_RO_STRS) *)
Definition WVC_LBRACKET : Z := 0x21180.
Definition WVC_LBRACE   : Z := 0x21160.
Definition WVC_RBRACKET : Z := 0x21220.
Definition WVC_RBRACE   : Z := 0x21200.
Definition WVC_COMMA    : Z := 0x211a0.
Definition WVC_COLON    : Z := 0x211e0.
Definition WVC_COLON_SP : Z := 0x211c0.
Definition wvc_open  (ty : Z) : Z := if ty =? 6 then WVC_LBRACE else WVC_LBRACKET.
Definition wvc_close (ty : Z) : Z := if ty =? 6 then WVC_RBRACE else WVC_RBRACKET.
Definition wvc_sep    (p : Z) : Z := if p =? 0 then WVC_COLON else WVC_COLON_SP.
Definition wvc_seplen (p : Z) : Z := if p =? 0 then 1 else 2.

(* ================= the resumed states ================= *)
(* the env at a resume: fs_extraT (atom 32 = the shadow base) ++ wvc_xs, i.e.
   xatom 0 .. 3 = the node's str / kids / keys / n, xatom 4 = the entry depth d,
   xatom 5 .. 17 = the thirteen saved entry registers in the order of the frame slots 72 .. 168
   (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra), xatom 18 = the address keys + 8 * i of the object key slot,
   xatom 19 = the key pointer read from it *)
Definition wvc_saved : list (bv 5) := [27; 26; 25; 24; 23; 22; 21; 20; 19; 18; 9; 8; 1]%bv.
Definition wvc_xs (regs : bvmap 5 word) (str kids keys n d ke key : Z) : list word :=
  [Z_to_bv 64 str; Z_to_bv 64 kids; Z_to_bv 64 keys; Z_to_bv 64 n; Z_to_bv 64 d]
  ++ map (fun r => YK11.getr regs r) wvc_saved
  ++ [Z_to_bv 64 ke; Z_to_bv 64 key].
(* the ASan shadow address of v + c, as the walk computes it *)
Definition wvc_shv (b : nat) (c : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff b c) (SLit 3)) (SOff 32 0).
(* the frame slots the prologue wrote (64: the shadow base; 72 .. 168: the saved registers) *)
Definition wvc_cs0 : list YP09.chunk :=
  YP09.mkChunk 64 (CVal 8 (SOff 32 0))
  :: map (fun k => YP09.mkChunk (72 + 8 * Z.of_nat k) (CVal 8 (SOff (xatom (5 + k)) 0))) (seq 0 13).
(* ... and the slots the container arm's prelude adds before the item loop (MEASURED at 0x83e68 .. 0x83ea4) *)
Definition wvc_csL (p : Z) : list YP09.chunk :=
  [YP09.mkChunk 8 (CVal 8 (SLit 3)); YP09.mkChunk 16 (CVal 8 (SOff (xatom 4) 0));
   YP09.mkChunk 24 (CVal 8 (wvc_shv 9 32)); YP09.mkChunk 32 (CVal 8 (SLit (wvc_seplen p)));
   YP09.mkChunk 40 (CVal 8 (SLit (wvc_sep p))); YP09.mkChunk 48 (CVal 8 (SOff 9 32));
   YP09.mkChunk 56 (CVal 8 (SLit WVC_COMMA))] ++ wvc_cs0.
(* the root node, based at the resumed s1 (atom 9) *)
Definition wvc_node (ty : Z) : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0 56 0 0
    [YP09.mkChunk 0 (CVal 4 (SLit ty)); YP09.mkChunk 16 (CVal 8 (SOff (xatom 0) 0));
     YP09.mkChunk 24 (CVal 8 (SOff (xatom 1) 0)); YP09.mkChunk 32 (CVal 8 (SOff (xatom 2) 0));
     YP09.mkChunk 40 (CVal 8 (SOff (xatom 3) 0))].
(* the object's key slot keys + 8 * i, based at its own atom *)
Definition wvc_keyR : YP09.region :=
  YP09.mkRegion (Some (xatom 18)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff (xatom 19) 0))].
Definition wvc_gf0 : list (nat * afact) := [(9%nat, mkAF 4096 (WVC_CEIL - 56) 3)].
Definition wvc_gfK : list (nat * afact) :=
  (xatom 18, mkAF 4096 (WVC_CEIL - 8) 3) :: (xatom 19, mkAF 0 (2 ^ 64 - 1) 0) :: wvc_gf0.
Definition wvc_SH0 : list shent := [mkSHE 9 0 56].
Definition wvc_SHK : list shent := [mkSHE 9 0 56; mkSHE (xatom 18) 0 8].
Definition wvc_setr (ss : sstate) (l : list (bv 5 * sv)) : sstate :=
  mkSS (ss_pc ss) (fold_left (fun r q => sr_set r (fst q) (snd q)) l (ss_regs ss)) (ss_mem ss) (ss_resv ss)
    (ss_facts ss).
(* the state at WVC_R_OPEN: the frame, the node, and s11 = the shadow address of the node *)
Definition wvc_ssO (ty : Z) : sstate :=
  wvc_setr (fss_retT WVC_R_OPEN WVC_F wvc_cs0 [wvc_node ty] wvc_gf0) [(27%bv, wvc_shv 9 0)].
(* the state at a loop resume point r (WVC_R_IND, _KEY, _SEP, _ITEM, _COMMA, _CLOSE): the prelude's slots, the key
   slot's region (OBJECT only), and the loop's registers; the two conditions the arm already took (pretty, n <> 0).
   The key slot keys + 8 * i is a region for the object (ty = 6) only: an array node's keys field is 0, so the slot
   would sit at address 8 * i, which no live memory holds; the array state carries the node alone (and atom 9's fact
   only). The loop's key cursor (reg 22 = xatom 18 - xatom 2) is computed on both arms. *)
Definition wvc_rsL (ty : Z) : list YP09.region := if ty =? 6 then [wvc_node ty; wvc_keyR] else [wvc_node ty].
Definition wvc_gfL (ty : Z) : list (nat * afact) := if ty =? 6 then wvc_gfK else wvc_gf0.
Definition wvc_SHL (ty : Z) : list shent := if ty =? 6 then wvc_SHK else wvc_SH0.
Definition wvc_ssL (ty p r : Z) : sstate :=
  add_cond
    (add_cond
      (wvc_setr (fss_retT r WVC_F (wvc_csL p) (wvc_rsL ty) (wvc_gfL ty))
        [(18%bv, wvc_shv 9 40); (20%bv, SOff 9 40);
         (22%bv, SAlu ALU_SUB (SOff (xatom 18) 0) (SOff (xatom 2) 0));
         (23%bv, SOff 9 24);
         (24%bv, SAlu ALU_ADD (SAluw ALU_ADD (SOff (xatom 4) 0) (SLit 1)) (SLit 0));
         (26%bv, wvc_shv 9 24); (27%bv, wvc_shv 9 0)])
      (mkAC (if p =? 0 then BC_EQ else BC_NE) (SOff 19 0) (SLit 0)))
    (mkAC BC_NE (SOff (xatom 3) 0) (SLit 0)).
(* the state at WVC_R_CLOSE (after the closing indent): the loop state with the NODE ALONE for both arms. After the
   last item the loop's key cursor is keys + 8 * n (reg 22 = 8 * n), which may lie past the object's keys block
   (cap = n), so the close point carries no key-slot region; the close run reads none. *)
Definition wvc_ssN (ty p : Z) : sstate :=
  add_cond
    (add_cond
      (wvc_setr (fss_retT WVC_R_CLOSE WVC_F (wvc_csL p) [wvc_node ty] wvc_gf0)
        [(18%bv, wvc_shv 9 40); (20%bv, SOff 9 40);
         (22%bv, SAlu ALU_SUB (SOff (xatom 18) 0) (SOff (xatom 2) 0));
         (23%bv, SOff 9 24);
         (24%bv, SAlu ALU_ADD (SAluw ALU_ADD (SOff (xatom 4) 0) (SLit 1)) (SLit 0));
         (26%bv, wvc_shv 9 24); (27%bv, wvc_shv 9 0)])
      (mkAC (if p =? 0 then BC_EQ else BC_NE) (SOff 19 0) (SLit 0)))
    (mkAC BC_NE (SOff (xatom 3) 0) (SLit 0)).

(* ---- what a walk holds at a point of the run: the symbolic state on the machine's memory, the shadow entries for
   the token run, the caller's journal over the unpoisoned memory, and ARU ---- *)
Definition wvc_at {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}
    (B : asyms) (E : env) (ss : sstate) (SH : list shent) (W : world tfibsegs) (ms : machine_state)
    (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world tfibsegs)
    (mem : word -> option byte) (md : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
    (U : list (Z * Z)) (mdc : Model) (k : Z) : Prop :=
  st_ok tfibsegs E ss (restrict (w_H W) ms) /\
  sh_ok tfibsegs fs_Bx SH E (mrestrict (w_H W) (ms_mem ms)) /\
  ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison U (ms_mem ms)) mdc k /\
  ARU tfibsegs B lyc Sc U W (ms_mem ms) mdc.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis HSS : FsShadowSyms B.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* ================= the two call-composition steps ================= *)
(* KIT ITEM (the container arms' after-call step; proved here from FSW_K3.fsw_ajournal_sub4 and
   FSW_rres.fsw_resume_after_rtU_args_chunks, so no hypothesis is taken): resume after a PROGRAM call whose post has
   a RAISED window top ot (FSH_Fn_FORM.md 3a: the callee writes the caller's pj_out above its sp), in the T resumed
   state fss_retT (the shadow-base cells, the extra regions rs and their atom facts gf). It is
   FSW_K3.fsw_after_callFPU_ot with FSW_rres's _args_chunks resume in place of the plain one; a Theorem Labs lane may lift it
   into FSW_K3 as fsw_after_callFPU_args_ot. *)
Lemma wvc_after_call_ot : forall STK sp0 FP own ly S U (W0 W : world tfibsegs) mem md lyc Sc Uc memC mdC k
    STKc FP1 ot f regsC ly' S' U' W' regs' mem' md' kc xs cs rs gf r,
  ajournal tfibsegs B STK sp0 FP ly S W0 (unpoison U mem) md own lyc Sc W (unpoison Uc memC) mdC k ->
  ARU tfibsegs B lyc Sc Uc W memC mdC ->
  ajournal tfibsegs B (STKc + (ot - spZ regsC)) ot FP1 lyc Sc W (unpoison Uc memC) mdC []
    ly' S' W' (unpoison U' mem') md' kc ->
  fsw_fp_sub B ly S lyc Sc own FP FP1 ->
  upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  aregs_preserved regsC regs' ->
  spZ regsC = sp0 - f -> 0 < f -> 0 <= STKc -> STKc + f <= STK -> f mod 16 = 0 ->
  spZ regsC <= ot -> ot <= sp0 ->
  regions_wf (fsT_ret_regions f cs rs) = true ->
  Forall (fun c => 0 <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= f) cs ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs' (fs_extraT ++ xs)) (rdW W' mem') (sp0 - f)) cs ->
  Forall (region_ok tfibsegs (Ereg regs' (fs_extraT ++ xs)) (rdW W' mem')) rs ->
  pairwise_disjoint (Ereg regs' (fs_extraT ++ xs)) (fsT_ret_regions f cs rs) ->
  atoms_ok (Ereg regs' (fs_extraT ++ xs)) gf ->
  ajournal tfibsegs B STK sp0 FP ly S W0 (unpoison U mem) md own ly' S' W' (unpoison U' mem') md' (k + kc) /\
  ARU tfibsegs B ly' S' U' W' mem' md' /\
  st_ok tfibsegs (Ereg regs' (fs_extraT ++ xs)) (fss_retT r f cs rs gf)
    (restrict (w_H W') (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs))).
Proof.
intros STK sp0 FP own ly S U W0 W mem md lyc Sc Uc memC mdC k STKc FP1 ot f regsC ly' S' U' W' regs' mem' md' kc
  xs cs rs gf r HJ HARU HJc HFP OK' PO' HP Hsp Hf HSc Hbud Hal Hot1 Hot2 Hwf Hin Hcs Hrs Hpd Hgf.
destruct HSS as [HBgot HBcell].
assert (HJ2 : ajournal tfibsegs B STK sp0 FP ly S W0 (unpoison U mem) md ([] ++ own)
  ly' S' W' (unpoison U' mem') md' (k + kc)).
{ apply (fsw_ajournal_sub5 B STK sp0 FP ly S W0 (unpoison U mem) md own lyc Sc W (unpoison Uc memC) mdC k
    (STKc + (ot - spZ regsC)) ot FP1 [] ly' S' W' (unpoison U' mem') md' kc HJ HJc); [lia | lia | exact HFP]. }
cbn [app] in HJ2.
assert (HARU' : ARU tfibsegs B ly' S' U' W' mem' md')
  by (pose proof HJ2 as (HAR2 & _); split; [exact HAR2 | split; [exact OK' | exact PO']]).
split; [exact HJ2|]. split; [exact HARU'|].
assert (Esp : spZ regs' = sp0 - f).
{ unfold spZ. rewrite (fsw_pres regsC regs' 2%bv HP ltac:(unfold acallee_saved; vm_compute; lia)). exact Hsp. }
exact (fsw_resume_after_rtU_args_chunks B STK sp0 FP ly S W0 (unpoison U mem) md own ly' S' U' W' mem' md' (k + kc)
  regs' f xs cs rs gf r HBgot HBcell HJ2 HARU' Esp Hf ltac:(lia) Hal Hwf Hcs Hrs Hpd Hgf).
Qed.

(* KIT ITEM (the arms' TAIL step, also proved here from fsw_ajournal_sub4): the caller's journal from entry to the
   jump may already hold the calls the container arm made (k > 0, the state and the buffer moved); the callee,
   entered at the jump with the caller's ra and callee-saved registers, returns to the caller's caller. *)
Lemma wvc_tail_otJ : forall STK STKc sp0 FP FP1 ly S U (W0 W : world tfibsegs) mem md lyc Sc Uc memJ mdJ
    (regs regsJ : bvmap 5 word) k kc U'
    (Q : alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop) W' c',
  ajournal tfibsegs B STK sp0 FP ly S W0 (unpoison U mem) md [] lyc Sc W (unpoison Uc memJ) mdJ k ->
  ARU tfibsegs B lyc Sc Uc W memJ mdJ ->
  0 <= STKc <= STK ->
  getr regsJ 1 = getr regs 1 -> aregs_preserved regs regsJ ->
  fsw_fp_sub B ly S lyc Sc [] FP FP1 ->
  fpostU tfibsegs B STKc sp0 FP1 regsJ lyc Sc Uc W memJ mdJ kc U' Q W' c' ->
  fpostU tfibsegs B STK sp0 FP regs ly S U W0 mem md (k + kc) U' Q W' c'.
Proof.
intros STK STKc sp0 FP FP1 ly S U W0 W mem md lyc Sc Uc memJ mdJ regs regsJ k kc U' Q W' c'
  HJ HARU HSTK R1 HP HFP (ly' & S' & regs' & mem' & md' & Ec & HJc & OK' & PO' & HPc & HQ).
exists ly', S', regs', mem', md'.
split; [rewrite Ec, R1; reflexivity|].
split.
{ assert (H : ajournal tfibsegs B STK sp0 FP ly S W0 (unpoison U mem) md ([] ++ [])
    ly' S' W' (unpoison U' mem') md' (k + kc)).
  { apply (fsw_ajournal_sub5 B STK sp0 FP ly S W0 (unpoison U mem) md [] lyc Sc W (unpoison Uc memJ) mdJ k
      STKc sp0 FP1 [] ly' S' W' (unpoison U' mem') md' kc HJ HJc); [lia | lia | exact HFP]. }
  cbn [app] in H. exact H. }
split; [exact OK'|]. split; [exact PO'|].
split; [|exact HQ].
intros rr Hrr. rewrite (HPc rr Hrr). exact (HP rr Hrr).
Qed.
End W.
