(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the IMAGE B (fs.asan-ubsan, UBSan trap mode) walk of parse_value against
   lib/B/FSH_Fn_reader.v parse_value_spec (CTX-free; the text of a working branch 035561e0fd4 = a working branch
   311139dc663: skip_ws_spec's post keeps [sp, ot) but [q, q + 8), parse_value_spec's k = 0 arm
   `q = spZ regs + 8 /\ raZ regs <= q`; both rulings a Theorem Labs lane and after the k = 0 gap report): the
   COMPOSITION, parse_value_holds : parse_value_spec tfibsegs B k (stages: FSW_parse_value.v; decode table:
   FSW_parse_value_tbl.v).
   rule 24 (lane brief (internal path), CONFIRM a Theorem Labs lane): proves function
   parse_value - fuzz_state image B asan-ubsan, entry 0x82fcc, level-indexed k = 0..2, narrow success form. Reuse search
   (run by a Theorem Labs lane, verbatim in the lane brief), the three result lines:
     proof-index: parse_value: 14 named, 35 by address, 0 related, 13 released lemma(s), an earlier delivery 58 named and 794
       name(s) holding it, 17 UNRELEASED working-branch file(s) in the lemma index, 0 UNRELEASED hit(s) on live working heads
     proof-index: parse_value_spec: 0 named, 0 by address, 0 related, 6 released lemma(s), 0 by file name, an earlier delivery 51
       named and 12 name(s) holding it, 2 UNRELEASED working-branch file(s) in the lemma index, 0 UNRELEASED hit(s) on live
       working heads
     proof-index: 0x82fcc: 0 named, 0 by address, 0 related, 0 released lemma(s), 0 by file name, an earlier delivery 0 named and
       0 name(s) holding it, 0 UNRELEASED working-branch file(s) in the lemma index, 105 UNRELEASED hit(s) on live working heads
   Port source (Lookup result): ported from a working branch 75e39a1f41d:proofs/omx-clap-core/fuzz_state/lib/
   B/Prog/{parse_value_disp,PvStr,PvItems,PvJoin,PvStep,PvHolds,ParseUnit}.v (COMPLETE old-form image-B walk of
   parse_value: entry/fake frame/skip_ws call pv_pro + pv_disp, parse_string arm pv_str_ok, parse_items arm pv_items_ok,
   epilogue pv_join + pvs_none, composition parse_value_step / parse_value_holds_b; all Qed, no admit), restated against
   parse_value_spec's frame lemma by lemma, NOT Required, NOT bridged; new-frame shape from image A's walk
   a working branch (ebb53c68f7d .. 00c6d1886e6: lib/A/FSH_parse_value.v pv_grant / pv_resume_sm /
   pv_seg0 / pv_sm / pv_epi / pv_strcall, lib/A/FSW_parse_value_calls.v pvc_objcall), copied and re-measured for B. *)
(* the IMAGE B (fs.asan-ubsan, UBSan trap mode) walk of parse_value against lib/B/FSH_Fn_reader.v parse_value_spec (CTX-free; the text of a working branch 035561e0fd4 = a working branch 311139dc663: skip_ws_spec's post keeps [sp, ot) but [q, q + 8), parse_value_spec's k = 0 arm `q = spZ regs + 8 /\ raZ regs <= q`; both rulings a Theorem Labs lane, 09:09Z and after the k = 0 gap report): the COMPOSITION, parse_value_holds : parse_value_spec tfibsegs B k (stages: FSW_parse_value.v; decode table: FSW_parse_value_tbl.v).   What is ported from the old B walk is its CONTENT on B's code: pv_pro's prologue / class-0 grant / frame setup
   (here pv_seg0, pv_sm, pv_seg1), the skip_ws call (pv_wscall), pv_disp's dispatch (q's alignment and shadow checks,
   in->p < in->end, in->p <> 0, the byte's shadow check, the byte tests; here FSW_parse_value.pv_disp), pv_str_ok (v's
   UBSan checks, v->type := 4, parse_string, v->str; here pv_disp + pv_strcall + pv_str1), pv_items_ok (a2 := 1,
   parse_items; here pv_disp + pv_objcall), pv_join / pvs_none (the epilogue and the flag release; here pv_epi).

   B's CODE, MEASURED (capstone 5.0.7, CS_ARCH_RISCV, CS_MODE_RISCV64 | CS_MODE_RISCVC, over the pinned
   projects/omx-clap-core/bin/fuzz_state/fuzz_state.asan-ubsan, sha256 5ac5ce0954f87e2d050c481b7b0599cfd55ef554eadc008e
   51491f44c053d204; 0x82fcc .. 0x83598 = 371 four-byte instructions, FSW_parse_value_tbl.v):
   PCS WALKED (every other pc of the range is never executed by a run the theorem covers):
     0x82fcc .. 0x8303c   prologue (frame 0xa0: ra s0 .. s11 at sp0 - 8 .. sp0 - 104, 0 at sp0 - 160), the 32-byte
                          re-align of s1, the use-after-return flag test (`beqz a2` 0x83034 not taken), the call of
                          __asan_stack_malloc_0 0x8303c (pv_seg0, pv_sm; resume 0x83040);
     0x83040 .. 0x830d0   F := a0, `bnez s2` 0x83050 taken (the real-stack fallback 0x83048 / 0x83054 .. 0x8306c is not
                          reached), the slot 0x30(s1), F's header, F's shadow f1 f1 f1 f1 f8 f3 f3 f3, a0 := q,
                          `jal skip_ws` 0x830d0 (pv_seg1; pv_wscall; resume 0x830d4);
     0x830d4 .. 0x83128   q's alignment and two shadow checks, the two loads, `bgeu in->p, in->end` 0x83108,
                          `beqz in->p` 0x8310c, the byte's shadow check, the byte (pv_disp); then the dispatch: string
                          0x83128 / 0x8312c / 0x83130 -> 0x83184; object 0x83128 -> 0x8315c .. 0x83170 -> 0x83174;
     0x83184 .. 0x831ac   v's two UBSan checks, v's shadow check, v->type := 4, a0 := q, `jal parse_string` 0x831ac
                          (pv_disp; pv_strcall; resume 0x831b0);
     0x831b0 .. 0x831d0   v + 16's shadow check, v->str := a0, s5 := (a0 <> 0) - 1, `j` 0x8329c (pv_str1);
     0x83174 .. 0x83180, 0x83278   a2 := 1, a0 := q, a1 := v, `jal parse_items` 0x83278 (pv_disp; pv_objcall; resume
                          0x8327c), `j` 0x83298, s5 := a0;
     0x8329c .. 0x8333c   F's magic 0x45e0360e, `beqz s2` 0x832a8 not taken (the real-stack exit 0x832dc .. 0x832f8 is
                          not reached), F's shadow f5 x 8, the flag byte := 0 (0x832d4, the frame's release), a0 := s5,
                          the restores, `ret` 0x8333c (pv_epi).
   DEAD ARMS (narrow form): the dispatch's SRr_sym_branch refutations (pv_disp: the byte is 34 or 123, from
   pv_u_cases / FS_DOC_STRS (i)) send no run into the literal arms ('f' 0x83144, 'n' 0x831d4, 't' 0x83280, all calling
   literal 0x83294), the array arm ('[' 0x8326c) or the number arm (0x831e8 .., with parse_number's fuzz_malloc 0x833c4,
   __asan_memcpy 0x8340c, strtod 0x83468).
   REPORT SITES (the binding checklist (internal path) rows 55-72,
   parse_value's 18 sites; site <- deciding edge: the step that refutes it, or the arm that is not reached):
     0x833b4 load1   <- 0x83374 bne: number arm, not reached.
     0x834e8 unimp (the UBSan trap) <- 0x830d8 bnez (q & 7): pv_disp, decided by atom 20's alignment fact;
                     0x8310c beqz in->p: pv_disp, decided by atom 33's fact (in->p >= 4096); 0x83184 beqz v and
                     0x8318c bnez (v & 7): pv_disp's string arm, decided by atom 19's facts (v >= 4096, 8-aligned);
                     0x831fc, 0x83238, 0x833c8, 0x833d4, 0x83428, 0x83438, 0x8343c, 0x83488: number arm, not reached.
     0x834f4 load1   <- 0x8311c bnez (the byte's shadow): pv_disp, token run, covered by pd_SH's byte entry (the text
                     block's body is addressable, FSW_rd.fsw_block_body_addressable).
     0x83504 store4  <- 0x8319c bnez (v's shadow): pv_disp, covered by pd_SH's v entry (pv_ra_v).
     0x83514 load1   <- 0x83218: number arm, not reached.
     0x83520 store1  <- 0x83450: number arm, not reached.
     0x8352c load1   <- 0x83498: number arm, not reached.
     0x83540 store4  <- 0x834c0: number arm, not reached.
     0x83550 load1   <- 0x83250: number arm, not reached.
     0x83558 load8   <- 0x830e8 bnez (q's shadow): pv_disp, covered by pd_SH's q entry (the stack's zero shadow).
     0x8355c load8   <- 0x830fc bnez (q + 8's shadow): pv_disp, the same entry.
     0x83564 store8  <- 0x831c0 bnez (v + 16's shadow): pv_str1, covered by ps2_SH's v entry.
     0x8356c store8  <- 0x833e8: number arm, not reached.
     0x83574 load8   <- 0x83400: number arm, not reached.
     0x8357c load8   <- 0x83418: number arm, not reached.
     0x83584 load8   <- 0x8345c: number arm, not reached.
     0x8358c store8  <- 0x8347c: number arm, not reached.
     0x83594 store8  <- 0x834d0: number arm, not reached.
   THE FRAME CHAINS at the two callee entries (pv_call_chains): fpreU's chain at the entry s0 (the spec's ch) and the
   chain at q survive the one stack word that changes before the calls, in->p [q, q + 8), because its old and new
   values are text pointers in [4096, alloc_ceiling) (pv_fpchain_x). MEASURED for the k >= 1 caller (B parse_items
   0x84e70): s0 saved at 0x84e78, `mv s1, a0` 0x84eb0 (q), `addi s0, s1, 0x10` 0x84ef0, no s0 write before
   `jal parse_value` 0x851cc, so s0Z regs = q + 16 there; the chain at s0 is [] or the record (q + 16, in->end, in->p),
   and pv_fpchain_x covers it (in->p is that record's NEXT, a stop before and after). k = 0: the chain at q is [] or
   (q, the word at spZ regs, raZ regs), stopped by the arm's raZ regs <= q (pv_chainq_k0).
   SECTION HYPOTHESES (Section H): the lane's fixed ones, FsShadowSyms B and the three callee specs (skip_ws_spec,
   parse_string_spec, parse_items_spec k when k <= 1), and the runtime facts the walk's own steps use: fs_img_facts
   (the spec Section's IMG; the statics across the class-0 grant, as crcs does), the use-after-return flag's GOT word
   and cell (FSW_K.v fs_D_GOT_uar / fs_D_uar_cell), the class-0 fake-frame call (FsRt's fr_stack_malloc_0 field text),
   and FSW_frame.v's unit laws (api_env, model_laws, stack_malloc_progressP for the grant; model_laws,
   astack_free_law, frame_flag_lawP for the release, as image A's pv_epi). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSW_K FSW_ret FSPstat FSH_Fn_reader FSW_rd FSW_pj FSW_K3 FSW_frame FSW_frame3.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require ReaderRes PjStruct PjIn WriterValue WriterSpec.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjGrammar PjTree PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Prog Require FSDocStrs.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require YF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.Prog Require Import FSW_parse_value_tbl FSW_parse_value.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YI14.
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ================= the text and the trace of the two arms (pure) ================= *)
Section F.
Lemma pv_spr_plain : forall bs run, plain_bytes bs -> concat (WriterSpec.spieces_run run bs) = run ++ bs.
Proof.
induction bs as [|c bs IH]; intros run Hp.
- cbn. rewrite !app_nil_r. reflexivity.
- inversion Hp as [|c0 bs0 Hc Hbs]; subst. unfold plain_byte in Hc.
  assert (Hs : WriterSpec.special c = false).
  { unfold WriterSpec.special. destruct Hc as (H1 & H2 & H3).
    apply orb_false_intro; [apply orb_false_intro; apply Z.eqb_neq; lia | apply Z.ltb_ge; lia]. }
  cbn [WriterSpec.spieces_run]. rewrite Hs, IH by exact Hbs. rewrite <- app_assoc. reflexivity.
Qed.
Lemma pv_wt_str : forall s pr d, plain_bytes s ->
  concat (WriterValue.wvpieces (PjTree.JStr s) pr d) = 34 :: s ++ [34].
Proof.
intros s pr d Hp. cbn [WriterValue.wvpieces]. unfold WriterSpec.spieces.
rewrite concat_cons, concat_app, pv_spr_plain by exact Hp. simpl. rewrite ?app_nil_r. reflexivity.
Qed.
Lemma pv_wt_obj : forall ms pr d, exists r, concat (WriterValue.wvpieces (PjTree.JObj ms) pr d) = 123 :: r.
Proof. intros ms pr d. exists (concat (tl (WriterValue.wvpieces (PjTree.JObj ms) pr d))). reflexivity. Qed.
Lemma pv_ech_plain : forall s, plain_bytes s -> flat_map PjRoundTrip.ech s = s.
Proof.
induction s as [|c s IH]; intros Hp; [reflexivity|].
inversion Hp as [|c0 s0 Hc Hs]; subst. unfold plain_byte in Hc. cbn [flat_map]. rewrite IH by exact Hs.
unfold PjRoundTrip.ech. replace (WriterSpec.special c) with false; [reflexivity|].
symmetry. unfold WriterSpec.special. destruct Hc as (H1 & H2 & H3).
apply orb_false_intro; [apply orb_false_intro; apply Z.eqb_neq; lia | apply Z.ltb_ge; lia].
Qed.
Lemma pv_tr_str : forall s, plain_bytes s ->
  PjRoundTrip.ttrace (PjTree.JStr s) = [PjGrammar.EAlloc (S (length s))].
Proof. intros s Hp. cbn [PjRoundTrip.ttrace]. rewrite pv_ech_plain by exact Hp. reflexivity. Qed.
Lemma pv_str_plain : forall s, FSDocStrs.fs_doc_strings (PjTree.JStr s) -> plain_bytes s.
Proof. intros s H. apply H. cbn. left. reflexivity. Qed.
(* the root is a string or an object (FS_DOC_STRS (i)), so the text starts with a quote or a brace *)
Lemma pv_u_cases : forall (u : PjTree.jv),
  (forall x, In x (u :: FSDocStrs.jv_vals u) -> FSDocStrs.str_or_obj x) ->
  (exists s, u = PjTree.JStr s) \/ (exists ms, u = PjTree.JObj ms).
Proof.
intros u H. specialize (H u (or_introl eq_refl)). unfold FSDocStrs.str_or_obj in H.
destruct u; try contradiction; [left; eexists; reflexivity | right; eexists; reflexivity].
Qed.
(* the i-th value of rest_at is the byte at p + i *)
Lemma pv_nth_map_skipn : forall (l : list byte) n i,
  nth_error (map (fun b : byte => bv_unsigned b) (skipn n l)) i = option_map (fun b : byte => bv_unsigned b) (nth_error l (n + i)).
Proof.
induction l as [|x l IH]; intros n i; destruct n as [|n]; cbn [skipn]; try (destruct i; reflexivity).
- rewrite Nat.add_0_l. destruct i as [|i]; cbn [map nth_error]; [reflexivity|].
  rewrite <- (Nat.add_0_l i) at 2. exact (IH 0%nat i).
- cbn [Nat.add nth_error]. exact (IH n i).
Qed.
Lemma pv_rest_byte : forall tb text p (l : list Z) (i : nat) c,
  ReaderRes.rest_at tb text p = l -> nth_error l i = Some c ->
  exists b : byte, nth_error tb (Z.to_nat (p - text) + i) = Some b /\ bv_unsigned b = c.
Proof.
intros tb text p l i c Hr Hi. unfold ReaderRes.rest_at, ReaderRes.zb in Hr. rewrite <- Hr in Hi.
rewrite pv_nth_map_skipn in Hi. destruct (nth_error tb (Z.to_nat (p - text) + i)) as [b|]; [|discriminate].
exists b. injection Hi as Hi. split; [reflexivity | exact Hi].
Qed.
Lemma pv_byte_eq : forall b : byte, bv_unsigned b = 34 -> b = Z_to_bv 8 34.
Proof. intros b H. apply bv_eq. rewrite H. reflexivity. Qed.
Lemma pv_firstn_map : forall (f : byte -> Z) n (l : list byte), firstn n (map f l) = map f (firstn n l).
Proof. intros f n. induction n as [|n IH]; intros [|x l]; cbn; try reflexivity. rewrite IH. reflexivity. Qed.
Lemma pv_skipn_map : forall (f : byte -> Z) n (l : list byte), skipn n (map f l) = map f (skipn n l).
Proof. intros f n. induction n as [|n IH]; intros [|x l]; cbn; try reflexivity. apply IH. Qed.
Lemma pv_skipn_skipn : forall {A} n m (l : list A), skipn n (skipn m l) = skipn (n + m) l.
Proof.
intros A n m. revert n. induction m as [|m IH]; intros n l; [rewrite Nat.add_0_r; reflexivity|].
destruct l as [|x l]; cbn [skipn]; [rewrite !skipn_nil; reflexivity|].
rewrite IH. replace (n + S m)%nat with (S (n + m)) by lia. reflexivity.
Qed.
Lemma pv_firstn_app_len : forall {A} (s l : list A), firstn (length s) (s ++ l) = s.
Proof. intros A s. induction s as [|x s IH]; intros l; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.
Lemma pv_skipn_app_len : forall {A} (s l : list A), skipn (length s) (s ++ l) = l.
Proof. intros A s. induction s as [|x s IH]; intros l; [reflexivity|]. cbn. apply IH. Qed.
(* the string arm's text facts: in->p + |ws| is the quote, the plain run of |s| bytes, and the closing quote *)
Lemma pv_str_text : forall tb text len p (ws s rest : list Z),
  Z.of_nat (length tb) = len -> text <= p <= text + len ->
  ReaderRes.rest_at tb text p = ws ++ (34 :: s ++ [34]) ++ rest -> plain_bytes s ->
  let p' := p + Z.of_nat (length ws) in
  p' < text + len /\ nth_error tb (Z.to_nat (p' - text)) = Some (Z_to_bv 8 34) /\
  plain_run tb text len p' (Z.of_nat (length s)) /\ run_at tb text p' (Z.of_nat (length s)) = s.
Proof.
intros tb text len p ws s rest Hl Hp Hr Hs p'.
assert (HL : Z.of_nat (length (ReaderRes.rest_at tb text p)) = text + len - p).
{ unfold ReaderRes.rest_at, ReaderRes.zb. rewrite length_map, length_skipn. lia. }
rewrite Hr in HL. rewrite !length_app in HL. cbn [length] in HL. rewrite length_app in HL. cbn [length] in HL.
assert (B1 : exists b, nth_error tb (Z.to_nat (p - text) + length ws) = Some b /\ bv_unsigned b = 34).
{ apply (pv_rest_byte tb text p _ _ 34 Hr). rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. }
destruct B1 as (b1 & Hb1 & Eb1).
split; [unfold p'; lia|].
split.
{ replace (Z.to_nat (p' - text)) with (Z.to_nat (p - text) + length ws)%nat by (unfold p'; lia).
  rewrite Hb1, (pv_byte_eq b1 Eb1). reflexivity. }
split.
- split; [lia|]. split; [unfold p'; lia|]. split.
  + destruct (pv_rest_byte tb text p _ (length ws + S (length s)) 34 Hr) as (b2 & Hb2 & Eb2).
    { rewrite nth_error_app2 by lia. replace (length ws + S (length s) - length ws)%nat with (S (length s)) by lia.
      cbn [app nth_error]. rewrite nth_error_app1 by (rewrite length_app; cbn [length]; lia).
      rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. }
    replace (Z.to_nat (p' + 1 + Z.of_nat (length s) - text)) with (Z.to_nat (p - text) + (length ws + S (length s)))%nat
      by (unfold p'; lia).
    rewrite Hb2, (pv_byte_eq b2 Eb2). reflexivity.
  + intros i Hi.
    assert (Hin : (Z.to_nat i < length s)%nat) by lia.
    destruct (nth_error s (Z.to_nat i)) as [ci|] eqn:Eci; [|apply nth_error_None in Eci; lia].
    destruct (pv_rest_byte tb text p _ (length ws + S (Z.to_nat i)) ci Hr) as (bi & Hbi & Ebi).
    { rewrite nth_error_app2 by lia. replace (length ws + S (Z.to_nat i) - length ws)%nat with (S (Z.to_nat i)) by lia.
      cbn [app nth_error]. rewrite nth_error_app1 by (rewrite length_app; cbn [length]; lia).
      rewrite nth_error_app1 by lia. exact Eci. }
    exists bi. split.
    * replace (Z.to_nat (p' + 1 + i - text)) with (Z.to_nat (p - text) + (length ws + S (Z.to_nat i)))%nat by (unfold p'; lia).
      exact Hbi.
    * rewrite Ebi. apply (proj1 (Forall_forall _ _) Hs). apply (nth_error_In _ _ Eci).
- unfold run_at, ReaderRes.zb. rewrite <- pv_firstn_map.
  replace (Z.to_nat (p' + 1 - text)) with (S (length ws) + Z.to_nat (p - text))%nat by (unfold p'; lia).
  rewrite <- (pv_skipn_skipn (S (length ws)) (Z.to_nat (p - text)) tb), <- pv_skipn_map.
  change (map (fun b : byte => bv_unsigned b) (skipn (Z.to_nat (p - text)) tb)) with (ReaderRes.rest_at tb text p).
  rewrite Hr. replace (S (length ws)) with (1 + length ws)%nat by lia. rewrite <- pv_skipn_skipn.
  rewrite pv_skipn_app_len.
  change (skipn 1 ((34 :: s ++ [34]) ++ rest)) with ((s ++ [34]) ++ rest).
  rewrite Nat2Z.id, <- app_assoc, pv_firstn_app_len. reflexivity.
Qed.
End F.

(* ================= memory transport: pointwise agreement of the restricted memory ================= *)
Definition pv_eqon (M M' : word -> option byte) (lo hi : Z) : Prop :=
  forall a, lo <= a < hi -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).

Section M. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Lemma pv_eqon_sub : forall M M' lo hi lo' hi', pv_eqon M M' lo hi -> lo <= lo' -> hi' <= hi -> pv_eqon M M' lo' hi'.
Proof. intros M M' lo hi lo' hi' E H1 H2 a Ha. apply E. lia. Qed.
Lemma pv_eqon_trans : forall M1 M2 M3 lo hi, pv_eqon M1 M2 lo hi -> pv_eqon M2 M3 lo hi -> pv_eqon M1 M3 lo hi.
Proof. intros M1 M2 M3 lo hi E1 E2 a Ha. rewrite (E2 a Ha). exact (E1 a Ha). Qed.
Lemma pv_eqon_refl : forall M lo hi, pv_eqon M M lo hi.
Proof. intros M lo hi a _. reflexivity. Qed.
Lemma pv_eqon_keep : forall M M' (P : Z -> Prop) lo hi,
  (forall x : word, ~ P (bv_unsigned x) -> M' x = M x) -> 0 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> ~ P a) -> pv_eqon M M' lo hi.
Proof. intros M M' P lo hi K H0 H1 HP a Ha. apply K. rewrite wz by lia. apply HP. exact Ha. Qed.
Lemma pv_eqon_val : forall M M' a (n : nat) v, pv_eqon M M' a (a + Z.of_nat n) ->
  val_mem tfibsegs M a n v -> val_mem tfibsegs M' a n v.
Proof. intros M M' a n v E V k Hk. pose proof (V k Hk) as Vk. unfold mbyte in *. rewrite E by lia. exact Vk. Qed.
Lemma pv_eqon_bytes : forall M M' a bs, pv_eqon M M' a (a + Z.of_nat (length bs)) ->
  Mem.bytes_at tfibsegs M a bs -> Mem.bytes_at tfibsegs M' a bs.
Proof.
intros M M' a bs E (H0 & H1 & H). split; [exact H0|]. split; [exact H1|]. intros i Hi.
pose proof (H i Hi) as Hh. unfold Mem.mrd, Mem.wa in *. rewrite E by lia. exact Hh.
Qed.
Lemma pv_eqon_wrat : forall M M' a, pv_eqon M M' a (a + 1) -> writable_at tfibsegs M a -> writable_at tfibsegs M' a.
Proof. intros M M' a E H. apply (proj1 (pv_wr_keep M M' a (E a ltac:(lia)))). exact H. Qed.
Lemma pv_eqon_wr : forall M M' a n, pv_eqon M M' a (a + n) -> Mem.wr_at tfibsegs M a n -> Mem.wr_at tfibsegs M' a n.
Proof.
intros M M' a n E (H0 & H1 & H). split; [exact H0|]. split; [exact H1|]. intros i Hi.
pose proof (H i Hi) as Hh. change (writable_at tfibsegs M' (a + i)). change (writable_at tfibsegs M (a + i)) in Hh.
exact (pv_eqon_wrat M M' (a + i) ltac:(eapply pv_eqon_sub; [exact E | lia | lia]) Hh).
Qed.
Lemma pv_eqon_in : forall M M' q text len p d tb, pv_eqon M M' q (q + 24) -> pv_eqon M M' text (text + len) ->
  PjIn.pj_in_ok tfibsegs M q text len p d tb -> PjIn.pj_in_ok tfibsegs M' q text len p d tb.
Proof.
intros M M' q text len p d tb Eq Et (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12).
refine (conj _ (conj _ (conj _ (conj _ (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj _ (conj H11 H12))))))))))).
- apply (pv_eqon_bytes M M' q); [|exact H1]. rewrite Mem.length_le8. eapply pv_eqon_sub; [exact Eq | lia | lia].
- apply (pv_eqon_bytes M M' (q + 8)); [|exact H2]. rewrite Mem.length_le8. eapply pv_eqon_sub; [exact Eq | lia | lia].
- apply (pv_eqon_bytes M M' (q + 16)); [|exact H3]. rewrite Mem.length_le4. eapply pv_eqon_sub; [exact Eq | lia | lia].
- exact (pv_eqon_wr M M' q 24 Eq H4).
- apply (pv_eqon_bytes M M' text); [|exact H10]. rewrite H9. exact Et.
Qed.
Lemma pv_eqon_zero : forall M M' v, pv_eqon M M' v (v + 56) -> PjStruct.pj_zero tfibsegs M v -> PjStruct.pj_zero tfibsegs M' v.
Proof.
intros M M' v E ((H8 & (S0 & S1 & S2)) & Hb). split; [split; [exact H8|]|].
- split; [exact S0|]. split; [exact S1|]. intros a Ha. destruct (S2 a Ha) as (Hw & b & Hr).
  split.
  + change (writable_at tfibsegs M' a). change (writable_at tfibsegs M a) in Hw.
    exact (pv_eqon_wrat M M' a ltac:(eapply pv_eqon_sub; [exact E | lia | lia]) Hw).
  + exists b. change (mbyte tfibsegs M' a = Some b). change (mbyte tfibsegs M a = Some b) in Hr.
    unfold mbyte in *. rewrite E by lia. exact Hr.
- apply (pv_eqon_bytes M M' v); [|exact Hb]. rewrite repeat_length. exact E.
Qed.
Lemma pv_eqon_RA : forall H H' m m' x n,
  (forall a, x <= a < x + n ->
     mrestrict H' m' (Z_to_bv 64 (shadow_of_addr SHADOW_OFF a)) = mrestrict H m (Z_to_bv 64 (shadow_of_addr SHADOW_OFF a))) ->
  range_addressable (aview tfibsegs H m) SHADOW_OFF x n -> range_addressable (aview tfibsegs H' m') SHADOW_OFF x n.
Proof.
intros H H' m m' x n E R y Hy. destruct (R y Hy) as (s & Es & Ok). exists s. split; [|exact Ok].
rewrite <- Es. unfold aview, mbyte. rewrite (E y Hy). reflexivity.
Qed.
(* an aview equality of the unpoisoned memories at an application or stack byte is one of the restricted memories *)
Lemma pv_M_of_aviewU : forall B ly S U (W : world tfibsegs) m md ly' S' U' (W' : world tfibsegs) m' md' a,
  ARU tfibsegs B ly S U W m md -> ARU tfibsegs B ly' S' U' W' m' md' ->
  0 <= a < 2 ^ 64 -> ~ in_img tfibsegs a -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44) ->
  aview tfibsegs (w_H W') (unpoison U' m') a = aview tfibsegs (w_H W) (unpoison U m) a ->
  mrestrict (w_H W') m' (Z_to_bv 64 a) = mrestrict (w_H W) m (Z_to_bv 64 a).
Proof.
intros B ly S U W m md ly' S' U' W' m' md' a H1 H2 Ha Hi Hs E.
apply (fsw_restrict_of_aview (w_H W) (w_H W') m m' a Ha Hi).
rewrite (aview_at tfibsegs (w_H W') m' (unpoison U' m') a (eq_sym (fsw_unpoison_app B ly' S' U' W' m' md' a H2 Ha Hs))).
rewrite (aview_at tfibsegs (w_H W) m (unpoison U m) a (eq_sym (fsw_unpoison_app B ly S U W m md a H1 Ha Hs))).
exact E.
Qed.
(* image bytes are no user-poisoned shadow bytes (a Theorem Labs lane's crcs_aview_low) *)
Lemma pv_aview_low : forall B ly S U (W : world tfibsegs) mem md a,
  ARU tfibsegs B ly S U W mem md -> 0 <= a < SHADOW_OFF ->
  aview tfibsegs (w_H W) (unpoison U mem) a = aview tfibsegs (w_H W) mem a.
Proof.
intros B ly S U W mem md a H Ha. apply (aview_at tfibsegs). apply unpoison_out.
rewrite (wz a ltac:(unfold SHADOW_OFF in Ha; lia)).
destruct (in_ush U a) eqn:E; [|reflexivity]. exfalso.
assert (UF : aowned B ly S a /\ SHADOW_OFF <= a < kHighMemBeg) by (eapply ush_facts; eassumption). lia.
Qed.
(* fuzz/alloc.c's statics are image bytes (grow walk's fs_pstat_img) *)
Lemma pv_pstat_img : forall a, inFP FS_PSTAT_FP a -> in_img tfibsegs a.
Proof.
intros a ((lo & hi) & Hin & Ha). cbn [fst snd] in Ha.
assert (HB : forall lo hi, In (lo, hi) FS_PSTAT_FP ->
  existsb (fun s => (Z.of_N (seg_base s) <=? lo) && (hi <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) tfibsegs = true).
{ intros lo' hi' H. unfold FS_PSTAT_FP in H. cbn [In] in H.
  repeat (destruct H as [H|H]; [injection H as <- <-; vm_compute; reflexivity|]); destruct H. }
apply HB in Hin. apply existsb_exists in Hin as (s & Hs & Hss). apply andb_prop in Hss as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. exists s. split; [exact Hs | lia].
Qed.
(* fs_glob reads only the four statics *)
Lemma pv_glob_eqon : forall (W W' : world tfibsegs) m m' live peak cnt fail,
  (forall a, inFP FS_PSTAT_FP a -> mrestrict (w_H W') m' (Z_to_bv 64 a) = mrestrict (w_H W) m (Z_to_bv 64 a)) ->
  fs_glob tfibsegs W m live peak cnt fail -> fs_glob tfibsegs W' m' live peak cnt fail.
Proof.
intros W W' m m' live peak cnt fail Hk (G1 & G2 & G3 & G4 & R).
assert (VB : forall g v, In (g, g + 8) FS_PSTAT_FP ->
  val_mem tfibsegs (mrestrict (w_H W) m) g 8 v -> val_mem tfibsegs (mrestrict (w_H W') m') g 8 v).
{ intros g v Hg Hv. apply (pv_eqon_val (mrestrict (w_H W) m) (mrestrict (w_H W') m') g 8 v); [|exact Hv].
  intros a Ha. apply Hk. exists (g, g + 8). split; [exact Hg | cbn [fst snd]; lia]. }
unfold fs_glob, fs_glob_at in *.
split; [apply VB; [right; left; reflexivity | exact G1]|]. split; [apply VB; [right; right; left; reflexivity | exact G2]|].
split; [apply VB; [right; right; right; left; reflexivity | exact G3]|]. split; [apply VB; [left; reflexivity | exact G4]|].
exact R.
Qed.
(* ... through any change that keeps the four cells' views (a Theorem Labs lane's crcs_glob_aview) *)
Lemma pv_glob_aview : forall (W W' : world tfibsegs) m m' live peak cnt fail,
  (forall a, inFP FS_PSTAT_FP a -> aview tfibsegs (w_H W') m' a = aview tfibsegs (w_H W) m a) ->
  fs_glob tfibsegs W m live peak cnt fail -> fs_glob tfibsegs W' m' live peak cnt fail.
Proof.
intros W W' m m' live peak cnt fail Hk (G1 & G2 & G3 & G4 & R).
assert (VB : forall g v, In (g, g + 8) FS_PSTAT_FP ->
  val_mem tfibsegs (mrestrict (w_H W) m) g 8 v -> val_mem tfibsegs (mrestrict (w_H W') m') g 8 v).
{ intros g v Hg Hv k Hkk.
  assert (Hin : inFP FS_PSTAT_FP (g + Z.of_nat k)) by (exists (g, g + 8); split; [exact Hg | cbn [fst snd]; lia]).
  rewrite (mbyte_of_aview tfibsegs (w_H W) (w_H W') m m' (g + Z.of_nat k) (Hk _ Hin)).
  exact (Hv k Hkk). }
unfold fs_glob, fs_glob_at in *.
split; [apply VB; [right; left; reflexivity | exact G1]|]. split; [apply VB; [right; right; left; reflexivity | exact G2]|].
split; [apply VB; [right; right; right; left; reflexivity | exact G3]|]. split; [apply VB; [left; reflexivity | exact G4]|].
exact R.
Qed.
End M.

(* the write windows of the entry state pv_ss0: the frame's 160 bytes below the entry sp *)
Ltac pv_wr0_tac :=
  let a := fresh "a" in let Ha := fresh "Ha" in
  intros a Ha; cbv beta;
  unfold pv_ss0, fss0T_args, fsT_regions_args, fsT_regions, fs_uar_regions in Ha; cbn [ss_mem app] in Ha;
  repeat (apply pv_wrange_cases in Ha; destruct Ha as [Ha|Ha];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val fstk fs_got_region fs_bcell_region fs_got_uar_region
          fs_uar_cell_region] in Ha;
     rewrite ?(ew_Ereg_nat _ fs_extraT 2 2%bv eq_refl) in Ha; unfold spZ; lia|]);
  exfalso; exact (pv_wrange_nil _ _ Ha).

(* ================= the three program calls through their callee hypotheses =================
   Ported from image A's walk (a working branch c778809c93e: lib/A/FSH_parse_value.v pv_strcall,
   lib/A/FSW_parse_value_calls.v pvc_objcall), with any journal start (W0 mem0 md0) and B's return addresses; skip_ws is
   B's own call (A inlines the loop). The callee's fpreU at its entry is FSW_ret.fsw_fpreU_atFP from the caller's
   journal; the callee's window [sp1 - STK_callee, ot) lies inside the caller's [ot - STK, ot), so the journals
   compose by FSW_K3.fsw_rt_atU3 (no footprint, or the statics) or FSW_K3.fsw_ajournal_sub5 (v and the statics). *)
Section C. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.

Lemma pv_inFP_nil : forall a, ~ inFP [] a.
Proof. intros a (r & Hr & _). destruct Hr. Qed.
Lemma pv_ot16 : forall STK ot FP ly S W0 mem0 md0 own lyc Sc W memc mdc k,
  ajournal tfibsegs B STK ot FP ly S W0 mem0 md0 own lyc Sc W memc mdc k -> ot mod 16 = 0.
Proof.
intros STK ot FP ly S W0 mem0 md0 own lyc Sc W memc mdc k HJ.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _). exact (proj1 Hstk).
Qed.

Section WS.
Hypothesis skip_ws_holds : @skip_ws_spec fx rc SK tfibsegs B.
(* the skip_ws call 0x830d0 -> 0x830d4 (FP = [], no tick, U unchanged) *)
Lemma pv_wscall : forall STK ot FP ly0 S0 U (W0 : world tfibsegs) mem0 md0 ly S2 (W : world tfibsegs) regsC memC mdC
    pos q sp1 text len p d (tb : list byte) tcap (ws rest : list Z) live peak cnt fail
    (Qp : world tfibsegs -> config -> Prop),
  spZ regsC = sp1 -> YK11.getr regsC 10%bv = Z_to_bv 64 q -> YK11.getr regsC 1%bv = Z_to_bv 64 0x830d4 ->
  YK11.getr regsC 3%bv = w64 (as_gp B) -> YK11.getr regsC 4%bv = w64 (as_tp B) ->
  sp1 mod 16 = 0 -> ot - STK <= sp1 - STK_skip_ws -> sp1 <= ot ->
  (exists ch0, achain ly (aview tfibsegs (w_H W) (unpoison U memC)) sp1 (s0Z regsC) ch0) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) memC) ->
  FSupoisonU.fs_heads B ly S2 U ->
  PjIn.pj_in_ok tfibsegs (mrestrict (w_H W) memC) q text len p d tb -> rd_win tfibsegs regsC ly W memC q ot ->
  rd_text tfibsegs B ly S2 W memC text len tcap ->
  ReaderRes.rest_at tb text p = ws ++ rest -> Forall (fun c => PjGrammar.ws c = true) ws ->
  (forall c r, rest = c :: r -> PjGrammar.ws c = false) ->
  fs_glob tfibsegs W memC live peak cnt fail ->
  ajournal tfibsegs B STK ot FP ly0 S0 W0 (unpoison U mem0) md0 [(0, pos)] ly S2 W (unpoison U memC) mdC 0 ->
  ARU tfibsegs B ly S2 U W memC mdC ->
  (forall ly2 S3 W2 regs2 mem2 md2,
     ajournal tfibsegs B STK ot FP ly0 S0 W0 (unpoison U mem0) md0 [(0, pos)] ly2 S3 W2 (unpoison U mem2) md2 0 ->
     ARU tfibsegs B ly2 S3 U W2 mem2 md2 ->
     ajournal tfibsegs B (STK_skip_ws + (ot - sp1)) ot [] ly S2 W (unpoison U memC) mdC [] ly2 S3 W2 (unpoison U mem2)
       md2 0 ->
     upoison_ok B ly2 S3 U -> upoisoned tfibsegs W2 mem2 U ->
     aregs_preserved regsC regs2 ->
     PjIn.pj_in_ok tfibsegs (mrestrict (w_H W2) mem2) q text len (p + Z.of_nat (length ws)) d tb ->
     wkeep tfibsegs W W2 memC mem2 sp1 ot q 8 ->
     ablocks B ly2 S3 = ablocks B ly S2 ->
     rd_text tfibsegs B ly2 S3 W2 mem2 text len tcap ->
     fs_glob tfibsegs W2 mem2 live peak cnt fail ->
     SRr tfibsegs W2 (YG0d.cfg_at tfibsegs 0x830d4 regs2 mem2 md2) Qp) ->
  SRr tfibsegs W (YG0d.cfg_at tfibsegs A_skip_ws regsC memC mdC) Qp.
Proof.
intros STK ot FP ly0 S0 U W0 mem0 md0 ly S2 W regsC memC mdC pos q sp1 text len p d tb tcap ws rest live peak cnt
  fail Qp Csp C10 C1 C3 C4 Hal16 Hwin Hsp1ot HCH0 HRO FH HIN HWIN HTX Hrest Hws Hstop HGL HJ HARU K.
destruct HCH0 as [ch0 HCH0q].
assert (HPREc : fpreU tfibsegs B STK_skip_ws ly S2 U W regsC memC mdC ch0).
{ apply (fsw_fpreU_atFP B STK ot FP ly0 S0 U W0 (unpoison U mem0) md0 [(0, pos)] ly S2 W memC mdC 0 regsC
    STK_skip_ws (sp1 - ot) ch0 HJ HARU HRO);
    [rewrite Csp; lia | | lia | vm_compute; discriminate | lia | rewrite C1; vm_compute; reflexivity | | rewrite C3; reflexivity
     | rewrite C4; reflexivity | rewrite Csp; exact HCH0q].
  - rewrite Zminus_mod, Hal16, (pv_ot16 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). reflexivity.
  - unfold raZ. rewrite C1. rewrite (unsigned_lit_small 0x830d4) by lia. lia. }
eapply SRr_bind.
{ exact (skip_ws_holds ly S2 U W regsC memC mdC ch0 q ot text len p d tb tcap ws rest live peak cnt fail
    HPREc FH C10 HIN HWIN HTX Hrest Hws Hstop HGL). }
cbv beta. intros W' c' _ (ly' & S' & regs' & mem' & md' & Ec & HJc & OK' & PO' & HP & HQ').
destruct HQ' as (QIN & QWK & QAB & QTX & QGL).
subst c'. rewrite C1.
destruct (fsw_rt_atU3 B STK ot FP ly0 S0 W0 (unpoison U mem0) md0 [(0, pos)] ly S2 U W memC mdC 0
  (STK_skip_ws + (ot - spZ regsC)) ot [] [] ly' S' U W' mem' md' 0
  HJ HJc OK' PO' ltac:(rewrite Csp; lia) ltac:(lia) ltac:(intros a Ha; exfalso; exact (pv_inFP_nil a Ha)))
  as (HJ2 & HARU2).
cbn [app] in HJ2.
rewrite Csp in HJc.
apply (K ly' S' W' regs' mem' md');
  [exact HJ2 | exact HARU2 | exact HJc | exact OK' | exact PO' | exact HP | exact QIN | rewrite Csp in QWK; exact QWK
   | exact QAB | exact QTX | exact QGL].
Qed.
End WS.

Section PS.
Hypothesis parse_string_holds : @parse_string_spec fx rc SK tfibsegs B.
(* the parse_string call 0x831ac -> 0x831b0 *)
Lemma pv_strcall : forall STK ot FP ly0 S0 U (W0 : world tfibsegs) mem0 md0 ly S2 (W : world tfibsegs) regsC memC mdC
    pos q sp1 text len p d (tb : list byte) tcap Q live peak cnt fail (Qp : world tfibsegs -> config -> Prop),
  spZ regsC = sp1 -> YK11.getr regsC 10%bv = Z_to_bv 64 q -> YK11.getr regsC 1%bv = Z_to_bv 64 0x831b0 ->
  YK11.getr regsC 3%bv = w64 (as_gp B) -> YK11.getr regsC 4%bv = w64 (as_tp B) ->
  sp1 mod 16 = 0 -> ot - STK <= sp1 - STK_parse_string -> sp1 <= ot -> sp1 + 16 <= q ->
  (exists ch0, achain ly (aview tfibsegs (w_H W) (unpoison U memC)) sp1 (s0Z regsC) ch0) ->
  (exists chq, achain ly (aview tfibsegs (w_H W) (unpoison U memC)) (sp1 - FRAME_parse_string) q chq) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) memC) ->
  FSupoisonU.fs_heads B ly S2 U ->
  PjIn.pj_in_ok tfibsegs (mrestrict (w_H W) memC) q text len p d tb -> rd_win tfibsegs regsC ly W memC q ot ->
  rd_text tfibsegs B ly S2 W memC text len tcap ->
  p < text + len -> nth_error tb (Z.to_nat (p - text)) = Some (Z_to_bv 8 34) -> plain_run tb text len p Q ->
  fs_glob tfibsegs W memC live peak cnt fail -> quiet cnt fail 1 ->
  Q + 1 + HEAD < MALLOC_MAX -> live + Q + 1 < 2 ^ 64 ->
  st_nev S2 + EV_fuzz_malloc <= EV_MAX -> blocks_bytes S2 + (Q + 1 + HEAD) <= LIVE_MAX ->
  ajournal tfibsegs B STK ot FP ly0 S0 W0 (unpoison U mem0) md0 [(0, pos)] ly S2 W (unpoison U memC) mdC 0 ->
  ARU tfibsegs B ly S2 U W memC mdC ->
  (forall a, inFP FS_PSTAT_FP a -> inFP FP a) ->
  (forall ly2 S3 W2 regs2 mem2 md2 a,
     ajournal tfibsegs B STK ot FP ly0 S0 W0 (unpoison U mem0) md0 [(0, pos)] ly2 S3 W2
       (unpoison (U ++ [(a - HEAD, HEAD)]) mem2) md2 EV_fuzz_malloc ->
     ARU tfibsegs B ly2 S3 (U ++ [(a - HEAD, HEAD)]) W2 mem2 md2 ->
     ajournal tfibsegs B (STK_parse_string + (ot - sp1)) ot FS_PSTAT_FP ly S2 W (unpoison U memC) mdC [] ly2 S3 W2
       (unpoison (U ++ [(a - HEAD, HEAD)]) mem2) md2 EV_fuzz_malloc ->
     upoison_ok B ly2 S3 (U ++ [(a - HEAD, HEAD)]) -> upoisoned tfibsegs W2 mem2 (U ++ [(a - HEAD, HEAD)]) ->
     aregs_preserved regsC regs2 ->
     YK11.getr regs2 10%bv = w64 a -> 4096 + HEAD <= a ->
     ablocks B ly2 S3 = ablocks B ly S2 ++ [(a - HEAD, Q + 1 + HEAD)] ->
     fs_rblock tfibsegs B ly2 S3 W2 mem2 a (Q + 1) ->
     PjStruct.pj_cbytes tfibsegs (mrestrict (w_H W2) mem2) a (run_at tb text p Q) ->
     PjIn.pj_in_ok tfibsegs (mrestrict (w_H W2) mem2) q text len (p + Q + 2) d tb ->
     wkeep tfibsegs W W2 memC mem2 sp1 ot q 24 ->
     rd_text tfibsegs B ly2 S3 W2 mem2 text len tcap ->
     fs_glob tfibsegs W2 mem2 (live + Q + 1) (Z.max peak (live + Q + 1)) (cnt + 1) fail ->
     SRr tfibsegs W2 (YG0d.cfg_at tfibsegs 0x831b0 regs2 mem2 md2) Qp) ->
  SRr tfibsegs W (YG0d.cfg_at tfibsegs A_parse_string regsC memC mdC) Qp.
Proof.
intros STK ot FP ly0 S0 U W0 mem0 md0 ly S2 W regsC memC mdC pos q sp1 text len p d tb tcap Q live peak cnt fail Qp
  Csp C10 C1 C3 C4 Hal16 Hwin Hsp1ot Hq16 HCH0 HCH HRO FH HIN HWIN HTX Hplen Hquote HPR HGL Hquiet HQm Hlive Hnev Hbb
  HJ HARU HFP K.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
destruct HCH as [chq HCHq]. destruct HCH0 as [ch0 HCH0q].
assert (HPREc : fpreU tfibsegs B STK_parse_string ly S2 U W regsC memC mdC ch0).
{ apply (fsw_fpreU_atFP B STK ot FP ly0 S0 U W0 (unpoison U mem0) md0 [(0, pos)] ly S2 W memC mdC 0 regsC
    STK_parse_string (sp1 - ot) ch0 HJ HARU HRO);
    [rewrite Csp; lia | | lia | vm_compute; discriminate | lia | rewrite C1; vm_compute; reflexivity | | rewrite C3; reflexivity
     | rewrite C4; reflexivity | rewrite Csp; exact HCH0q].
  - rewrite Zminus_mod, Hal16, (pv_ot16 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). reflexivity.
  - unfold raZ. rewrite C1. rewrite (unsigned_lit_small 0x831b0) by lia. lia. }
eapply SRr_bind.
{ exact (parse_string_holds ly S2 U W regsC memC mdC ch0 q ot text len p d tb tcap Q live peak cnt fail
    HPREc FH ltac:(exists chq; rewrite Csp; exact HCHq) ltac:(rewrite Csp; lia) C10 HIN HWIN HTX Hplen Hquote HPR HGL
    Hquiet HQm Hlive Hnev Hbb). }
cbv beta. intros W' c' _ (a & ly' & S' & regs' & mem' & md' & Ec & HJc & OK' & PO' & HP & HQ').
destruct HQ' as (Q10 & Q4096 & Qab & QRB & Qcb & QIN & QWK & QTX & QGL).
subst c'. rewrite C1.
destruct (fsw_rt_atU3 B STK ot FP ly0 S0 W0 (unpoison U mem0) md0 [(0, pos)] ly S2 U W memC mdC 0
  (STK_parse_string + (ot - spZ regsC)) ot FS_PSTAT_FP [] ly' S' (U ++ [(a - HEAD, HEAD)]) W' mem' md' EV_fuzz_malloc
  HJ HJc OK' PO' ltac:(rewrite Csp; lia) ltac:(lia)) as (HJ2 & HARU2).
{ intros x Hx. right; right. split; [exact (HFP x Hx) | exact (pv_pstat_img x Hx)]. }
cbn [app] in HJ2. rewrite Z.add_0_l in HJ2.
rewrite Csp in HJc.
apply (K ly' S' W' regs' mem' md' a);
  [exact HJ2 | exact HARU2 | exact HJc | exact OK' | exact PO' | exact HP | exact Q10 | exact Q4096 | exact Qab
   | exact QRB | exact Qcb | exact QIN | rewrite Csp in QWK; exact QWK | exact QTX | exact QGL].
Qed.
End PS.

Section PI.
(* parse_value's level, = parse_items' level at this call (FSH_Fn_reader.v: parse_value at level k calls parse_items at
   level k) *)
Variable k : nat.
Hypothesis parse_items_holds : @parse_items_spec fx rc SK tfibsegs B k.
(* the parse_items call 0x83278 -> 0x8327c *)
Lemma pv_objcall : forall STK ot FP ly0 S0 U (W0 : world tfibsegs) mem0 md0 ly S S2 (W : world tfibsegs) regsC memC
    mdC pos q sp1 v text len p (tb : list byte) tcap (ms : list (list Z * PjTree.jv)) (pr : bool) (rest : list Z)
    live peak cnt fail (Qp : world tfibsegs -> config -> Prop),
  let tr := PjRoundTrip.ttrace (PjTree.JObj ms) in
  let wt := concat (WriterValue.wvpieces (PjTree.JObj ms) pr (Z.of_nat k)) in
  (k <= 1)%nat ->
  spZ regsC = sp1 -> YK11.getr regsC 10%bv = Z_to_bv 64 q -> YK11.getr regsC 11%bv = Z_to_bv 64 v ->
  YK11.getr regsC 12%bv = Z_to_bv 64 1 -> YK11.getr regsC 1%bv = Z_to_bv 64 0x8327c ->
  YK11.getr regsC 3%bv = w64 (as_gp B) -> YK11.getr regsC 4%bv = w64 (as_tp B) ->
  sp1 mod 16 = 0 -> ot - STK <= sp1 - STK_parse_items (1 - k) -> sp1 <= ot -> sp1 + 16 <= q ->
  (exists ch0, achain ly (aview tfibsegs (w_H W) (unpoison U memC)) sp1 (s0Z regsC) ch0) ->
  (exists chq, achain ly (aview tfibsegs (w_H W) (unpoison U memC)) sp1 q chq /\
     Forall (fun r => bad_next (fst (fst r)) (ly_top ly) (snd r) = true \/ q + 40 <= snd r) chq) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) memC) ->
  FSupoisonU.fs_heads B ly S2 U ->
  frames S2 = (0, pos) :: frames S ->
  Z.of_nat (length (frames S)) <= FRL_parse_value (Z.of_nat k) ->
  PjIn.pj_in_ok tfibsegs (mrestrict (w_H W) memC) q text len p (Z.of_nat k) tb ->
  rd_win tfibsegs regsC ly W memC q ot ->
  rd_text tfibsegs B ly S2 W memC text len tcap ->
  ReaderRes.rest_at tb text p = wt ++ rest ->
  FSDocStrs.fs_doc_values (PjTree.JObj ms) -> FSDocStrs.fs_doc_strings (PjTree.JObj ms) ->
  PjRoundTrip.pj_wf ReaderRes.jr_strtod (PjTree.JObj ms) -> (PjTree.depth (PjTree.JObj ms) <= 2 - k)%nat ->
  pobj tfibsegs B ly S2 W memC v -> PjStruct.pj_zero tfibsegs (mrestrict (w_H W) memC) v ->
  (v + 56 <= sp1 - STK_parse_items (1 - k) \/ ot <= v) -> (v + 56 <= text - HEAD \/ text + tcap <= v) ->
  fs_glob tfibsegs W memC live peak cnt fail -> quiet cnt fail (Z.of_nat (length tr)) ->
  rd_sizes_ok tr -> live + rd_live tr < 2 ^ 64 ->
  st_nev S2 + rd_ev tr <= EV_MAX -> blocks_bytes S2 + rd_live tr <= LIVE_MAX ->
  ajournal tfibsegs B STK ot FP ly0 S0 W0 (unpoison U mem0) md0 [(0, pos)] ly S2 W (unpoison U memC) mdC 0 ->
  ARU tfibsegs B ly S2 U W memC mdC ->
  (* v's bytes: a byte of a live block or of a frame of the entry frames, inside FP *)
  (forall a, v <= a < v + 56 ->
     (inFP FP a /\ exists b n, In (b, n) (ablocks B ly S2) /\ b <= a < b + req_size n) \/
     (inFP FP a /\ exists cid pos', In (cid, pos') (frames S0) /\ in_zr a (frame_rng ly0 (cid, pos')))) ->
  (forall a, inFP FS_PSTAT_FP a -> inFP FP a) ->
  (forall ly2 S3 W2 regs2 mem2 md2 (D Da : list (Z * Z)),
     Permutation Da D ->
     ajournal tfibsegs B STK ot FP ly0 S0 W0 (unpoison U mem0) md0 [(0, pos)] ly2 S3 W2
       (unpoison (U ++ rd_heads Da) mem2) md2 (rd_ev tr) ->
     ARU tfibsegs B ly2 S3 (U ++ rd_heads Da) W2 mem2 md2 ->
     ajournal tfibsegs B (STK_parse_items (1 - k) + (ot - sp1)) ot ([(v, v + 56)] ++ FS_PSTAT_FP) ly S2 W
       (unpoison U memC) mdC [] ly2 S3 W2 (unpoison (U ++ rd_heads Da) mem2) md2 (rd_ev tr) ->
     upoison_ok B ly2 S3 (U ++ rd_heads Da) -> upoisoned tfibsegs W2 mem2 (U ++ rd_heads Da) ->
     aregs_preserved regsC regs2 ->
     YK11.getr regs2 10%bv = w64 0 ->
     PjIn.pj_in_ok tfibsegs (mrestrict (w_H W2) mem2) q text len (p + Z.of_nat (length wt)) (Z.of_nat k) tb ->
     wkeep tfibsegs W W2 memC mem2 sp1 ot q 24 ->
     Permutation (ablocks B ly2 S3) (ablocks B ly S2 ++ rd_hblocks D) ->
     rtree tfibsegs B ly2 S3 W2 mem2 v (PjTree.JObj ms) D -> rd_sum D = PjGrammar.held tr ->
     (length D <= length tr)%nat ->
     pobj tfibsegs B ly2 S3 W2 mem2 v -> rd_text tfibsegs B ly2 S3 W2 mem2 text len tcap ->
     (exists peak', peak <= peak' /\
        fs_glob tfibsegs W2 mem2 (live + PjGrammar.held tr) peak' (cnt + Z.of_nat (length tr)) fail) ->
     SRr tfibsegs W2 (YG0d.cfg_at tfibsegs 0x8327c regs2 mem2 md2) Qp) ->
  SRr tfibsegs W (YG0d.cfg_at tfibsegs A_parse_items regsC memC mdC) Qp.
Proof.
intros STK ot FP ly0 S0 U W0 mem0 md0 ly S S2 W regsC memC mdC pos q sp1 v text len p tb tcap ms pr rest live peak
  cnt fail Qp tr wt Hk Csp C10 C11 C12 C1 C3 C4 Hal16 Hwin Hsp1ot Hq16 HCH0 HCHq HRO FH Hfrs Hfr0 HIN HWIN HTX
  Hrest Hvals Hstrs Hwf Hdep HPo HZo Hvst Hvtx HGL Hquiet Hsz Hlive Hnev Hbb HJ HARU HVFP HFP K.
destruct HCH0 as [ch0 HCH0q].
assert (Hk01 : (1 - k = 0 \/ 1 - k = 1)%nat) by lia.
assert (HSTK0 : 0 <= STK_parse_items (1 - k)) by (destruct Hk01 as [E | E]; rewrite E; vm_compute; discriminate).
assert (HPREc : fpreU tfibsegs B (STK_parse_items (1 - k)) ly S2 U W regsC memC mdC ch0).
{ apply (fsw_fpreU_atFP B STK ot FP ly0 S0 U W0 (unpoison U mem0) md0 [(0, pos)] ly S2 W memC mdC 0 regsC
    (STK_parse_items (1 - k)) (sp1 - ot) ch0 HJ HARU HRO);
    [rewrite Csp; lia | | lia | exact HSTK0 | lia | rewrite C1; vm_compute; reflexivity | | rewrite C3; reflexivity
     | rewrite C4; reflexivity | rewrite Csp; exact HCH0q].
  - rewrite Zminus_mod, Hal16, (pv_ot16 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). reflexivity.
  - unfold raZ. rewrite C1. rewrite (unsigned_lit_small 0x8327c) by lia. lia. }
assert (HFR : Z.of_nat (length (frames S2)) <= FRL_parse_value (Z.of_nat k + 1))
  by (rewrite Hfrs; cbn [length]; unfold FRL_parse_value in *; lia).
assert (HCHq' : exists chq, achain ly (aview tfibsegs (w_H W) (unpoison U memC)) (spZ regsC) q chq /\
  Forall (fun r => bad_next (fst (fst r)) (ly_top ly) (snd r) = true \/ q + 40 <= snd r) chq)
  by (rewrite Csp; exact HCHq).
assert (Hsp16 : spZ regsC + 16 <= q) by (rewrite Csp; exact Hq16).
assert (Hvst' : v + 56 <= spZ regsC - STK_parse_items (1 - k) \/ ot <= v) by (rewrite Csp; exact Hvst).
eapply SRr_bind.
{ exact (parse_items_holds ly S2 U W regsC memC mdC ch0 q ot v text len p tb tcap ms pr rest live peak cnt fail
    Hk HPREc FH HFR C10 C11 C12 HIN HWIN Hsp16 HCHq' HTX Hrest Hvals Hstrs Hwf Hdep HPo HZo Hvst' Hvtx HGL
    Hquiet Hsz Hlive Hnev Hbb). }
cbv beta. intros W' c' _ (D & Da & HDa & (ly' & S' & regs' & mem' & md' & Ec & HJc & OK' & PO' & HP & HQ')).
destruct HQ' as (Q10 & QIN & QWK & QPERM & QT & QSUM & QLEN & QPO & QTX & QGL).
subst c'. rewrite C1.
assert (HJ2 : ajournal tfibsegs B STK ot FP ly0 S0 W0 (unpoison U mem0) md0 ([] ++ [(0, pos)]) ly' S' W'
  (unpoison (U ++ rd_heads Da) mem') md' (0 + rd_ev tr)).
{ apply (fsw_ajournal_sub5 B STK ot FP ly0 S0 W0 (unpoison U mem0) md0 [(0, pos)] ly S2 W (unpoison U memC) mdC 0
    (STK_parse_items (1 - k) + (ot - spZ regsC)) ot ([(v, v + 56)] ++ FS_PSTAT_FP) [] ly' S' W'
    (unpoison (U ++ rd_heads Da) mem') md' (rd_ev tr) HJ HJc); [rewrite Csp; lia | lia |].
  intros a Ha. destruct Ha as ((rlo, rhi) & Hr & Har). cbn [fst snd] in Har.
  apply in_app_or in Hr as [Hr | Hr].
  - cbn [In] in Hr. destruct Hr as [E | []]. injection E as <- <-.
    destruct (HVFP a Har) as [H1 | H1]; [left; exact H1 | right; right; right; right; exact H1].
  - right; right; left. pose proof (ex_intro (fun r => In r FS_PSTAT_FP /\ fst r <= a < snd r) (rlo, rhi) (conj Hr Har))
      as Hin. split; [exact (HFP a Hin) | exact (pv_pstat_img a Hin)]. }
cbn [app] in HJ2. rewrite Z.add_0_l in HJ2.
assert (HARU2 : ARU tfibsegs B ly' S' (U ++ rd_heads Da) W' mem' md')
  by (split; [exact (proj1 HJ2) | split; [exact OK' | exact PO']]).
rewrite Csp in QWK. rewrite Csp in HJc.
exact (K ly' S' W' regs' mem' md' D Da HDa HJ2 HARU2 HJc OK' PO' HP Q10 QIN QWK QPERM QT QSUM QLEN QPO QTX QGL).
Qed.
End PI.
End C.

(* ================= the frame chains the callees' premises read =================
   (1) fpreU's chain at each callee's entry runs from parse_value's s0 = its entry sp: the record parse_value's prologue
   saved at sp - 8 / sp - 16 (entry ra, entry s0), then the entry chain (fpreU's ch), whose words lie at or above the
   entry sp; between the entry and the parse_string / parse_items call only in->p [q, q + 8) of those changes
   (skip_ws_spec's post keeps [sp, ot) except [q, q + 8), FSH_Fn_reader.v at a working branch), and both
   its old and its new value are text pointers in [4096, alloc_ceiling): as a record's ra it stays >= 4096, as a next
   pointer it stops the chain (it is below every stack fp). pv_fpchain_x / pv_achain_x carry a chain across such a
   change; pv_chain_push adds the saved record on top (Reusable/YCbq.v achain_push).
   (2) the chain at q (parse_string's C5 premise, parse_items' premise): k >= 1, the entry chain at q carried the same
   way (its next-pointer clause too, pv_forall_bad_x); k = 0 (q = spZ + 8), pv_chainq_k0: [] or the one record
   (q, word at spZ, saved ra), which raZ regs <= q (parse_value_spec's k = 0 arm) stops. *)
Section CH. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma pv_bad_next_le : forall fp top nfp, nfp <= fp -> bad_next fp top nfp = true.
Proof. intros fp top nfp H. unfold bad_next. replace (nfp <=? fp) with true by (symmetry; apply Z.leb_le; lia). reflexivity. Qed.
Lemma pv_bad_next_false : forall fp top nfp, bad_next fp top nfp = false -> fp < nfp /\ nfp < top - 16 /\ nfp mod 8 = 0.
Proof.
intros fp top nfp H. unfold bad_next in H.
destruct (nfp <=? fp) eqn:E1; [discriminate|]. destruct (top - 16 <=? nfp) eqn:E2; [cbn in H; discriminate|].
destruct (nfp mod 8 =? 0) eqn:E3; [|cbn in H; discriminate].
apply Z.leb_gt in E1. apply Z.leb_gt in E2. apply Z.eqb_eq in E3. lia.
Qed.
Definition pv_rx (r r' : Z * Z * Z) : Prop :=
  fst (fst r') = fst (fst r) /\ (snd r' = snd r \/ snd r' < alloc_ceiling).
Lemma pv_fpchain_x : forall (rd rd' : reader) top q ch bp,
  fpchain (rdword rd) bp top ch -> alloc_ceiling <= bp -> bp mod 8 = 0 -> bp < top - 16 ->
  (forall a, bp - 16 <= a -> a + 8 <= top -> a mod 8 = 0 -> a <> q -> rdword rd' a = rdword rd a) ->
  (forall w, rdword rd q = Some w -> 4096 <= w < alloc_ceiling) ->
  (exists w', rdword rd' q = Some w' /\ 4096 <= w' < alloc_ceiling) ->
  exists ch', fpchain (rdword rd') bp top ch' /\ Forall2 pv_rx ch ch'.
Proof.
intros rd rd' top q ch. induction ch as [|[[fp ra] nfp] rest IH]; intros bp Hc Hbp Hal Htop Heq Hold Hnew.
- destruct Hc as (r & Hr & Hr0).
  assert (Hne : bp - 8 <> q) by (intros E; rewrite E in Hr; pose proof (Hold r Hr); lia).
  exists []. split; [|constructor].
  exists r. rewrite Heq by first [lia | rewrite Zminus_mod, Hal; reflexivity | exact Hne]. split; [exact Hr | exact Hr0].
- cbn [fpchain] in Hc. destruct Hc as (-> & Hal' & Hra & Hnfp & Hra4 & Hrest).
  destruct Hnew as (w' & Hw' & Hw'r).
  assert (RA : exists ra', rdword rd' (bp - 8) = Some ra' /\ 4096 <= ra').
  { destruct (Z.eq_dec (bp - 8) q) as [E|E].
    - exists w'. rewrite E. split; [exact Hw' | lia].
    - exists ra. rewrite Heq by first [lia | rewrite Zminus_mod, Hal; reflexivity | exact E]. split; [exact Hra | exact Hra4]. }
  destruct RA as (ra' & Hra' & Hra'4).
  destruct (Z.eq_dec (bp - 16) q) as [E|E].
  + (* the next pointer is the changed word: its old and new values both stop the chain *)
    rewrite E in Hnfp. pose proof (Hold nfp Hnfp) as Hn.
    rewrite (pv_bad_next_le bp top nfp ltac:(lia)) in Hrest. subst rest.
    exists [(bp, ra', w')]. split.
    * cbn [fpchain]. split; [reflexivity|]. split; [exact Hal|]. split; [exact Hra'|]. split; [rewrite E; exact Hw'|].
      split; [exact Hra'4|]. rewrite (pv_bad_next_le bp top w' ltac:(lia)). reflexivity.
    * constructor; [unfold pv_rx; cbn [fst snd]; split; [reflexivity | right; lia] | constructor].
  + assert (Hn' : rdword rd' (bp - 16) = Some nfp)
      by (rewrite Heq by first [lia | rewrite Zminus_mod, Hal; reflexivity | exact E]; exact Hnfp).
    destruct (bad_next bp top nfp) eqn:Eb.
    * subst rest. exists [(bp, ra', nfp)]. split.
      -- cbn [fpchain]. split; [reflexivity|]. split; [exact Hal|]. split; [exact Hra'|]. split; [exact Hn'|].
         split; [exact Hra'4|]. rewrite Eb. reflexivity.
      -- constructor; [unfold pv_rx; cbn [fst snd]; split; [reflexivity | left; reflexivity] | constructor].
    * destruct (pv_bad_next_false bp top nfp Eb) as (N1 & N2 & N3).
      destruct (IH nfp Hrest ltac:(lia) N3 N2 ltac:(intros a Ha Htp Ha8 Hq; apply Heq; [lia | exact Htp | exact Ha8 | exact Hq])
        Hold
        (ex_intro _ w' (conj Hw' Hw'r))) as (ch' & Hc' & HF).
      exists ((bp, ra', nfp) :: ch'). split.
      -- cbn [fpchain]. split; [reflexivity|]. split; [exact Hal|]. split; [exact Hra'|]. split; [exact Hn'|].
         split; [exact Hra'4|]. rewrite Eb. exact Hc'.
      -- constructor; [unfold pv_rx; cbn [fst snd]; split; [reflexivity | left; reflexivity] | exact HF].
Qed.
Lemma pv_achain_x : forall ly (rd rd' : reader) sp v ch q,
  achain ly rd sp v ch -> alloc_ceiling <= sp ->
  (forall a, sp <= a -> a + 8 <= ly_top ly -> a mod 8 = 0 -> a <> q -> rdword rd' a = rdword rd a) ->
  (forall w, rdword rd q = Some w -> 4096 <= w < alloc_ceiling) ->
  (exists w', rdword rd' q = Some w' /\ 4096 <= w' < alloc_ceiling) ->
  exists ch', achain ly rd' sp v ch' /\ Forall2 pv_rx ch ch'.
Proof.
intros ly rd rd' sp v ch q [(Hv & ->) | (H1 & H2 & H3 & H4 & H5)] Hsp Heq Hold Hnew.
- exists []. split; [left; split; [exact Hv | reflexivity] | constructor].
- destruct (pv_fpchain_x rd rd' (ly_top ly) q ch v H4 ltac:(lia) H3 H2
    ltac:(intros a Ha Htp Ha8 Hq; apply Heq; [lia | exact Htp | exact Ha8 | exact Hq]) Hold Hnew) as (ch' & Hc' & HF).
  exists ch'. split; [|exact HF]. right. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact Hc'|].
  pose proof (fpchain_fps_increase _ _ _ _ Hc') as Hinc. eapply Forall_impl; [|exact Hinc]. intros r Hr. cbn beta in Hr. lia.
Qed.
(* the k >= 1 next-pointer clause survives the change *)
Lemma pv_forall_bad_x : forall top q ch ch',
  Forall (fun r => alloc_ceiling <= fst (fst r)) ch ->
  Forall (fun r => bad_next (fst (fst r)) top (snd r) = true \/ q + 40 <= snd r) ch -> Forall2 pv_rx ch ch' ->
  Forall (fun r => bad_next (fst (fst r)) top (snd r) = true \/ q + 40 <= snd r) ch'.
Proof.
intros top q ch ch' Hlo Hb HF. induction HF as [|r r' l l' Hr HF IH]; [constructor|].
inversion Hlo as [|r0 l0 Hlo1 Hlo2]; subst. inversion Hb as [|r1 l1 Hb1 Hb2]; subst.
constructor; [|exact (IH Hlo2 Hb2)].
destruct Hr as (E1 & [E2|E2]); rewrite E1.
- rewrite E2. exact Hb1.
- left. apply pv_bad_next_le. lia.
Qed.
Lemma pv_chain_push : forall ly (rd : reader) sp sp' s0 ch ra,
  achain ly rd sp s0 ch -> ly_top ly <= 2 ^ 64 -> rdword rd (sp - 8) = Some ra -> rdword rd (sp - 16) = Some s0 ->
  4096 <= ra -> alloc_ceiling <= sp -> sp mod 8 = 0 -> sp' + 16 <= sp -> exists ch1, achain ly rd sp' sp ch1.
Proof.
intros ly rd sp sp' s0 ch ra Hc Htop H8 H16 Hra Hceil Hal Hsp.
destruct (Z_lt_le_dec sp (ly_top ly - 16)) as [Ht|Ht].
- exists ((sp, ra, s0) :: ch). exact (achain_push ly rd rd sp s0 ra ch sp' Hc Htop (fun a _ => eq_refl) H8 H16 Hra Hceil Hal Ht Hsp).
- exists []. left. split; [right; left; lia | reflexivity].
Qed.
Lemma pv_chainq_k0 : forall ly (rd : reader) sp' q w ra,
  rdword rd (q - 8) = Some w -> 0 <= w -> rdword rd (q - 16) = Some ra -> ra <= q ->
  sp' + 16 <= q -> q < ly_top ly - 16 -> q mod 8 = 0 ->
  exists chq, achain ly rd sp' q chq /\
    Forall (fun r => bad_next (fst (fst r)) (ly_top ly) (snd r) = true \/ q + 40 <= snd r) chq.
Proof.
intros ly rd sp' q w ra H8 Hw H16 Hra Hsp Htop Hal.
destruct (Z_lt_le_dec w 4096) as [Hl|Hl].
- exists []. split; [|constructor]. right. split; [exact Hsp|]. split; [exact Htop|]. split; [exact Hal|].
  split; [exists w; split; [exact H8 | lia] | constructor].
- exists [(q, w, ra)]. split.
  + right. split; [exact Hsp|]. split; [exact Htop|]. split; [exact Hal|]. split.
    * cbn [fpchain]. split; [reflexivity|]. split; [exact Hal|]. split; [exact H8|]. split; [exact H16|].
      split; [exact Hl|]. rewrite (pv_bad_next_le q (ly_top ly) ra Hra). reflexivity.
    * constructor; [cbn; lia | constructor].
  + constructor; [left; cbn [fst snd]; exact (pv_bad_next_le q (ly_top ly) ra Hra) | constructor].
Qed.
(* a restricted-memory agreement is a view agreement, across worlds *)
Lemma pv_aview_eq2 : forall (H H' : word -> bool) (m m' : word -> option byte) a,
  mrestrict H' m' (Z_to_bv 64 a) = mrestrict H m (Z_to_bv 64 a) -> aview tfibsegs H' m' a = aview tfibsegs H m a.
Proof. intros H H' m m' a E. unfold aview, mbyte. rewrite E. reflexivity. Qed.
Lemma pv_aview_nonneg : forall H m a z, aview tfibsegs H m a = Some z -> 0 <= z.
Proof.
intros H m a z E. unfold aview in E. destruct (mbyte tfibsegs (mrestrict H m) a) as [b|]; [|discriminate].
cbn in E. injection E as <-. pose proof (bv_unsigned_in_range 8 b). lia.
Qed.
Lemma pv_rdword_some : forall H m a, (forall i, 0 <= i < 8 -> aview tfibsegs H m (a + i) <> None) ->
  exists w, rdword (aview tfibsegs H m) a = Some w /\ 0 <= w.
Proof.
intros H m a Hs. unfold rdword.
assert (G : forall i, 0 <= i < 8 -> exists z, aview tfibsegs H m (a + i) = Some z /\ 0 <= z).
{ intros i Hi. destruct (aview tfibsegs H m (a + i)) as [z|] eqn:E; [|exfalso; exact (Hs i Hi E)].
  exists z. split; [reflexivity | exact (pv_aview_nonneg H m (a + i) z E)]. }
destruct (G 0 ltac:(lia)) as (z0 & E0 & P0). rewrite Z.add_0_r in E0. rewrite E0.
destruct (G 1 ltac:(lia)) as (z1 & E1 & P1). rewrite E1.
destruct (G 2 ltac:(lia)) as (z2 & E2 & P2). rewrite E2.
destruct (G 3 ltac:(lia)) as (z3 & E3 & P3). rewrite E3.
destruct (G 4 ltac:(lia)) as (z4 & E4 & P4). rewrite E4.
destruct (G 5 ltac:(lia)) as (z5 & E5 & P5). rewrite E5.
destruct (G 6 ltac:(lia)) as (z6 & E6 & P6). rewrite E6.
destruct (G 7 ltac:(lia)) as (z7 & E7 & P7). rewrite E7.
eexists. split; [reflexivity | lia].
Qed.
(* the live blocks' request sum (blocks_bytes) is rd_sum of ablocks (copied from the accepted B grow walk,
   a working branch 8c301ffdfdb lib/B/Prog/FSW_grow_holds.v grow_bb) *)
Lemma pv_bb : forall B ly S, blocks_bytes S = rd_sum (ablocks B ly S).
Proof.
intros B ly S. unfold blocks_bytes, rd_sum, ablocks, blocks.
induction (st_chunks S) as [|c cs IH]; [reflexivity|].
cbn [List.filter fold_right]. destruct (is_alloc c); cbn [map fold_right snd]; rewrite IH; reflexivity.
Qed.
(* in->p moved past the white space *)
Lemma pv_rest_skip : forall tb text p (ws r : list Z), text <= p ->
  ReaderRes.rest_at tb text p = ws ++ r -> ReaderRes.rest_at tb text (p + Z.of_nat (length ws)) = r.
Proof.
intros tb text p ws r Hp E. unfold ReaderRes.rest_at, ReaderRes.zb in *.
replace (Z.to_nat (p + Z.of_nat (length ws) - text)) with (length ws + Z.to_nat (p - text))%nat by lia.
rewrite <- pv_skipn_skipn, <- pv_skipn_map, E. apply pv_skipn_app_len.
Qed.
(* ---- small transports ---- *)
Lemma pv_mb_of_mr : forall (H H' : word -> bool) (m m' : word -> option byte) a,
  mrestrict H' m' (Z_to_bv 64 a) = mrestrict H m (Z_to_bv 64 a) -> mbyte tfibsegs (mrestrict H' m') a = mbyte tfibsegs (mrestrict H m) a.
Proof. intros H H' m m' a E. unfold mbyte. rewrite E. reflexivity. Qed.
Lemma pv_val_mb : forall (M M' : word -> option byte) a (n : nat) v,
  (forall i, 0 <= i < Z.of_nat n -> mbyte tfibsegs M' (a + i) = mbyte tfibsegs M (a + i)) ->
  val_mem tfibsegs M a n v -> val_mem tfibsegs M' a n v.
Proof. intros M M' a n v E V j Hj. rewrite (E (Z.of_nat j) ltac:(lia)). exact (V j Hj). Qed.
Lemma pv_saved_mb : forall (M M' : word -> option byte) s regs0,
  (forall a, s - 104 <= a < s -> mbyte tfibsegs M' a = mbyte tfibsegs M a) ->
  pv_saved_ok M s regs0 -> pv_saved_ok M' s regs0.
Proof.
intros M M' s regs0 E V j Hj. apply (pv_val_mb M M' _ 8 _); [|exact (V j Hj)].
intros i Hi. apply E. cbn in Hi. lia.
Qed.
Lemma pv_ly_F : forall n ly ly' c p, layout_le n ly ly' ->
  frame_addr ly' c p = frame_addr ly c p /\ flag_addr ly' c p = flag_addr ly c p.
Proof.
intros n ly ly' c p (_ & _ & _ & _ & _ & EF & _). unfold frame_addr, flag_addr. rewrite EF. split; reflexivity.
Qed.
Lemma pv_ly_top : forall n ly ly', layout_le n ly ly' -> ly_top ly' = ly_top ly /\ ly_stk_lo ly' = ly_stk_lo ly /\
  ly_stk_hi ly' = ly_stk_hi ly.
Proof. intros n ly ly' (_ & _ & _ & _ & _ & _ & _ & _ & ET & EL & EH & _). split; [exact ET|]. split; [exact EL | exact EH]. Qed.
Lemma pv_rdword_U : forall B ly S U (W : world tfibsegs) m md a, ARU tfibsegs B ly S U W m md ->
  kHighMemBeg <= a -> a + 8 <= 2 ^ 64 ->
  rdword (aview tfibsegs (w_H W) (unpoison U m)) a = rdword (aview tfibsegs (w_H W) m) a.
Proof.
intros B ly S U W m md a HU H1 H2. apply rdword_ext. intros i Hi.
apply (fsw_aview_unpoison_high B ly S U W m md (a + i) HU). lia.
Qed.
Lemma pv_sink_nil : ~ YI16.sink_open_fp [].
Proof. intros (r & Hr & _). destruct Hr. Qed.
Lemma pv_stk_rel : forall k, (k <= 2)%nat ->
  176 + STK_skip_ws <= STK_parse_value (2 - k) /\ 176 + STK_parse_string <= STK_parse_value (2 - k) /\
  ((k <= 1)%nat -> 176 + STK_parse_items (1 - k) <= STK_parse_value (2 - k)).
Proof.
intros k Hk. destruct k as [|[|[|k]]].
- split; [vm_compute; discriminate|]. split; [vm_compute; discriminate|]. intros _. vm_compute; discriminate.
- split; [vm_compute; discriminate|]. split; [vm_compute; discriminate|]. intros _. vm_compute; discriminate.
- split; [vm_compute; discriminate|]. split; [vm_compute; discriminate|]. intros H. lia.
- lia.
Qed.
Lemma pv_achain_fps : forall ly (rd : reader) sp v ch, achain ly rd sp v ch -> alloc_ceiling <= sp ->
  Forall (fun r => alloc_ceiling <= fst (fst r)) ch.
Proof.
intros ly rd sp v ch [(_ & ->) | (_ & _ & _ & _ & H5)] Hsp; [constructor|].
eapply Forall_impl; [|exact H5]. intros r Hr. cbn beta in Hr. lia.
Qed.
(* both chains at a callee's entry (fpreU's from s0 = the entry sp, and the callee's own at q), from the entry's and
   a view that agrees with the entry's on the stack at and above the entry sp, in->p [q, q + 8) apart *)
Lemma pv_call_chains : forall ly lyc (rd0 rdc : reader) sp s0 ra ch q sp',
  achain ly rd0 sp s0 ch ->
  (q = sp + 8 /\ ra <= q \/ sp + 16 <= q /\ exists chq, achain ly rd0 sp q chq /\
     Forall (fun r => bad_next (fst (fst r)) (ly_top ly) (snd r) = true \/ q + 40 <= snd r) chq) ->
  ly_top lyc = ly_top ly -> ly_top ly <= 2 ^ 47 -> q + 24 <= ly_top ly ->
  alloc_ceiling <= sp -> sp mod 8 = 0 -> q mod 8 = 0 -> sp' + 16 <= sp ->
  (forall b, sp <= b < ly_top ly -> ~ (q <= b < q + 8) -> rdc b = rd0 b) ->
  rdword rdc (sp - 8) = Some ra -> rdword rdc (sp - 16) = Some s0 -> 4096 <= ra ->
  (forall w, rdword rd0 q = Some w -> 4096 <= w < alloc_ceiling) ->
  (exists w', rdword rdc q = Some w' /\ 4096 <= w' < alloc_ceiling) ->
  (q = sp + 8 -> exists w, rdword rdc sp = Some w /\ 0 <= w) ->
  (exists ch0, achain lyc rdc sp' sp ch0) /\
  (forall sq, sq + 16 <= q -> sq <= sp -> exists chq, achain lyc rdc sq q chq /\
     Forall (fun r => bad_next (fst (fst r)) (ly_top lyc) (snd r) = true \/ q + 40 <= snd r) chq).
Proof.
intros ly lyc rd0 rdc sp s0 ra ch q sp' HCH HCHQ Etop Htop Hqt Hsp Hsp8 Hq8 Hsp' BYT W8 W16 Hra Hold Hnew Hk0.
assert (WEQ : forall a, sp <= a -> a + 8 <= ly_top ly -> a mod 8 = 0 -> a <> q -> rdword rdc a = rdword rd0 a).
{ intros a Ha Ht Ha8 Hq. apply rdword_ext. intros i Hi. apply BYT; [lia|].
  pose proof (Z.div_mod a 8 ltac:(lia)) as Da. pose proof (Z.div_mod q 8 ltac:(lia)) as Dq.
  rewrite Ha8 in Da. rewrite Hq8 in Dq. lia. }
split.
- destruct (pv_achain_x ly rd0 rdc sp s0 ch q HCH Hsp WEQ Hold Hnew) as (ch' & Hc' & _).
  exact (pv_chain_push lyc rdc sp sp' s0 ch' ra (achain_ly_top ly lyc rdc sp s0 ch' Etop Hc') ltac:(lia) W8 W16 Hra
    Hsp Hsp8 Hsp').
- intros sq Hsq Hsq2. destruct HCHQ as [(Eq & Hrq) | (Hq16 & chq & Hchq & Hfa)].
  + destruct (Hk0 Eq) as (w & Hw & Hw0). subst q.
    exact (pv_chainq_k0 lyc rdc sq (sp + 8) w ra ltac:(replace (sp + 8 - 8) with sp by lia; exact Hw) Hw0
      ltac:(replace (sp + 8 - 16) with (sp - 8) by lia; exact W8) Hrq Hsq ltac:(rewrite Etop; lia) Hq8).
  + destruct (pv_achain_x ly rd0 rdc sp q chq q Hchq Hsp WEQ Hold Hnew) as (chq' & Hc' & HF).
    exists chq'. split.
    * exact (achain_ly_top ly lyc rdc sq q chq' Etop (achain_lower ly rdc sp sq q chq' Hc' Hsq2)).
    * rewrite Etop. exact (pv_forall_bad_x (ly_top ly) q chq chq' (pv_achain_fps ly rd0 sp q chq Hchq Hsp) Hfa HF).
Qed.
(* one byte read off a memory as a val_mem of width 1 (image A's walk, a working branch 00c6d1886e6
   lib/A/FSH_parse_value.v pv_val1) *)
Lemma pv_val1 : forall (m : word -> option byte) a (b : byte), mbyte tfibsegs m a = Some b ->
  val_mem tfibsegs m a 1 (bv_unsigned b).
Proof.
intros m a b H k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r, H. f_equal.
pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
unfold YO0f.le_byte. cbn -[Z.modulo Z.shiftr Z.pow]. rewrite ?Z.shiftr_0_r, ?Z.mod_small by lia.
symmetry. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. exact Hr.
Qed.
(* the text byte at x, read off pj_in_ok's `bytes_at text tb` *)
Lemma pv_byte_tb : forall (m : word -> option byte) q text len p0 d (tb : list byte) x b,
  PjIn.pj_in_ok tfibsegs m q text len p0 d tb -> text <= x -> nth_error tb (Z.to_nat (x - text)) = Some b ->
  val_mem tfibsegs m x 1 (bv_unsigned b).
Proof.
intros m q text len p0 d tb x b HIN Hx Hb.
destruct HIN as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (H0 & H1 & HB) & _).
assert (Hlt : (Z.to_nat (x - text) < length tb)%nat) by (apply nth_error_Some; rewrite Hb; discriminate).
pose proof (HB _ Hlt) as E. rewrite Hb in E.
replace (text + Z.of_nat (Z.to_nat (x - text))) with x in E by lia.
apply pv_val1. exact E.
Qed.
(* the read-only view is a property of the image bytes only *)
Lemma pv_ro_keep : forall B (rd rd' : reader), arodata_okP tfibsegs FS_RLO FS_RHI B rd ->
  (forall a, in_roP tfibsegs FS_RLO FS_RHI a -> rd' a = rd a) -> arodata_okP tfibsegs FS_RLO FS_RHI B rd'.
Proof. intros B rd rd' H E a Ha Ho He. rewrite (E a Ha). exact (H a Ha Ho He). Qed.
End CH.
Ltac pv_inK := repeat (first [left; reflexivity | right]).

(* ================= the composition, with the callees and the runtime laws as named hypotheses ================= *)
Section H. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable k : nat.
Hypothesis Hk : (k <= 2)%nat.
(* the shadow-base cells of B (lib/B/FSH_Base.v FsShadowSyms: GOT word 0x9fc10, cell 0xa8438) *)
Hypothesis HSS : FsShadowSyms B.
(* the callees, each the text of its lib/B spec Definition (lib/B/FSH_Fn_reader.v) *)
Hypothesis skip_ws_holds : @skip_ws_spec fx rc SK tfibsegs B.
Hypothesis parse_string_holds : @parse_string_spec fx rc SK tfibsegs B.
Hypothesis parse_items_holds : (k <= 1)%nat -> @parse_items_spec fx rc SK tfibsegs B k.
(* the image facts (lib/B/FSH_Rt.v fs_img_facts, the spec Section's own hypothesis IMG): fuzz/alloc.c's statics are no
   runtime-owned static and not errno, which the class-0 fake-frame call's acall_kept image clause needs *)
Hypothesis IMG : fs_img_facts tfibsegs B.
(* the use-after-return flag's GOT word and cell (lib/B/FSW_K.v fs_D_GOT_uar / fs_D_uar_cell) *)
Hypothesis HGUAR : as_got_uar B = fs_D_GOT_uar.
Hypothesis HUCELL : as_uar_cell B = fs_D_uar_cell.
(* the class-0 fake-frame call (lib/B/FSH_Rt.v FsRt's field fr_stack_malloc_0, the text of its type) *)
Hypothesis SM0 : pc_stack_malloc (as_code B) 0 = PC_stack_malloc_0 /\ FSupoisonU.astack_malloc_realizesU tfibsegs B 0.
(* the fake-frame kit's unit laws (lib/B/FSW_frame.v Section f): the grant and the flag release *)
Hypothesis errno_low : api_env tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law tfibsegs B.
Hypothesis FFL : frame_flag_lawP tfibsegs B.

Let HPST_ERRNO : forall a, inFP FS_PSTAT_FP a -> ~ (as_errno B <= a < as_errno B + 4) := fun a Ha => proj2 (proj1 IMG a Ha).
Let HPST_OWN : forall a, inFP FS_PSTAT_FP a -> ~ Exists (in_zr a) (as_owned_static B) :=
  fs_pstat_not_owned tfibsegs B _ _ _ _ _ _ _ IMG.

(* ---- stage A: the entry -> the grant -> segment 1 -> the skip_ws entry, with the data the callees read carried to
   the call: the prologue's run writes [sp0 - 160, sp0) only, the grant keeps what acall_kept keeps, segment 1 writes
   F, F's shadow, the save area and the slot ---- *)
Lemma pv_pre : forall ly S U (W : world tfibsegs) regs mem md ch q ot v text len p tb tcap live peak cnt fail
  (Q : world tfibsegs -> config -> Prop),
  fpreU tfibsegs B (STK_parse_value (2 - k)) ly S U W regs mem md ch ->
  Z.of_nat (length (frames S)) <= FRL_parse_value (Z.of_nat k) ->
  YK11.getr regs 10 = w64 q -> YK11.getr regs 11 = w64 v ->
  PjIn.pj_in_ok tfibsegs (mrestrict (w_H W) mem) q text len p (Z.of_nat k) tb -> rd_win tfibsegs regs ly W mem q ot ->
  spZ regs + 8 <= q ->
  rd_text tfibsegs B ly S W mem text len tcap ->
  pobj tfibsegs B ly S W mem v ->
  fs_glob tfibsegs W mem live peak cnt fail ->
  (forall S2 pos msh mdh,
     msh = mkst (ms_regs msh) (Z_to_bv 64 A_skip_ws) (ms_mem msh) (seg_rom tfibsegs) ->
     ajournal tfibsegs B (STK_parse_value (2 - k) + (ot - spZ regs)) ot ([(v, v + 56)] ++ FS_PSTAT_FP) ly S W
       (unpoison U mem) md [(0, pos)] ly S2 W (unpoison U (ms_mem msh)) mdh 0 ->
     ARU tfibsegs B ly S2 U W (ms_mem msh) mdh ->
     frames S2 = (0, pos) :: frames S -> ~ In (0, pos) (frames S) -> ablocks B ly S2 = ablocks B ly S ->
     st_nev S2 = st_nev S -> blocks_bytes S2 = blocks_bytes S ->
     YK11.getr (ms_regs msh) 1%bv = Z_to_bv 64 0x830d4 -> YK11.getr (ms_regs msh) 10%bv = Z_to_bv 64 q ->
     YK11.getr (ms_regs msh) 2%bv = Z_to_bv 64 (32 * ((spZ regs - 160) / 32)) ->
     YK11.getr (ms_regs msh) 3%bv = YK11.getr regs 3%bv -> YK11.getr (ms_regs msh) 4%bv = YK11.getr regs 4%bv ->
     YK11.getr (ms_regs msh) 8%bv = Z_to_bv 64 (spZ regs) ->
     YK11.getr (ms_regs msh) 9%bv = Z_to_bv 64 (32 * ((spZ regs - 160) / 32)) ->
     YK11.getr (ms_regs msh) 18%bv = Z_to_bv 64 (frame_addr ly 0 pos) -> YK11.getr (ms_regs msh) 19%bv = Z_to_bv 64 v ->
     YK11.getr (ms_regs msh) 20%bv = Z_to_bv 64 q -> YK11.getr (ms_regs msh) 23%bv = Z_to_bv 64 SHADOW_OFF ->
     YK11.getr (ms_regs msh) 26%bv = Z_to_bv 64 (frame_addr ly 0 pos) ->
     YK11.getr (ms_regs msh) 27%bv = Z_to_bv 64 (SHADOW_OFF + frame_addr ly 0 pos / 8) ->
     pv_saved_ok (mrestrict (w_H W) (ms_mem msh)) (spZ regs) regs ->
     val_mem tfibsegs (mrestrict (w_H W) (ms_mem msh)) (frame_addr ly 0 pos + 56) 8 (flag_addr ly 0 pos) ->
     pv_eqon (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem msh)) (spZ regs) (2 ^ 64) ->
     pv_eqon (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem msh)) (text - HEAD) (text + tcap) ->
     pv_eqon (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem msh)) v (v + 56) ->
     fs_glob tfibsegs W (ms_mem msh) live peak cnt fail ->
     arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) (ms_mem msh)) ->
     SRr tfibsegs W (mkCfg msh mdh) Q) ->
  SRr tfibsegs W (YG0d.cfg_at tfibsegs A_parse_value regs mem md) Q.
Proof.
intros ly S U W regs mem md ch q ot v text len p tb tcap live peak cnt fail Q HPRE HFRL H10 H11 HIN HWIN Hq8 HTX HPO HG K.
pose proof (proj1 HPRE) as HPU. pose proof (proj2 HPRE) as HRO.
pose proof (fsw_sp B _ ly S U W regs mem md ch HPU) as (Hal16 & Hceil & H47 & HS0).
pose proof (fsw_ARU B _ ly S U W regs mem md ch HPU) as HARU0.
pose proof (ARU_AR tfibsegs B ly S U W mem md HARU0) as HAR0.
pose proof (pv_stk k Hk) as FSk.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (AR_laws_ok tfibsegs B) as LAWS.
destruct HWIN as (Hw1 & Hw2 & Hw3 & Hw4 & Hpres).
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN) as (Bq0 & Bq24 & Bt0 & Bp & Btl & Bqt & Blen & Bq8 & Bd).
destruct (fsw_pobj_low B ly S W (unpoison U mem) md mem v HAR0 HPO) as (Hv1 & Hv2).
pose proof HTX as (Htx1 & HRB & Htc). pose proof HRB as (HinT & HalT & HtcT & VhT).
destruct (fsw_ablock_low B ly S W (unpoison U mem) md (text - HEAD) (tcap + HEAD) HAR0 HinT) as (Tb1 & Tb2 & Tb3).
assert (RqT : req_size (tcap + HEAD) = tcap + HEAD) by (unfold req_size, HEAD; destruct (Z.eqb_spec (tcap + 16) 0); lia).
assert (NIMG : forall a, FS_IMG_END <= a -> ~ in_img tfibsegs a) by (intros a Ha Hi; pose proof (fs_segs_img a Hi); lia).
assert (IMGLO : forall a, in_img tfibsegs a -> a < FS_IMG_END) by (intros a Hi; pose proof (fs_segs_img a Hi); lia).
assert (FSIMG : FS_IMG_END < SHADOW_OFF) by (unfold FS_IMG_END, SHADOW_OFF; lia).
assert (Hsot : spZ regs <= ot) by lia.
apply (pv_seg0 B HSS HGUAR HUCELL k ly S U W regs mem md ch ([(v, v + 56)] ++ FS_PSTAT_FP) ot Q Hk HPU Hsot Hw3 Hw4
  ltac:(intros a Ha; apply Hpres; lia)).
intros ms1 mat1 HS1 HJ1 HARU1 HF1 HFr1.
destruct (pv_sm_site B ly S U W regs mem md ch k ms1 Hk HPU HS1)
  as (R2 & R9 & Fsp1 & Fal & R1 & R10 & R3 & R4 & R8 & R23 & R19 & R20).
assert (KEEP1 : forall x : word, ~ (spZ regs - 160 <= bv_unsigned x < spZ regs) ->
  mrestrict (w_H W) (ms_mem ms1) x = mrestrict (w_H W) mem x)
  by (exact (pv_frame_P _ _ _ _ (fun a => spZ regs - 160 <= a < spZ regs) HFr1 ltac:(pv_wr0_tac))).
apply (pv_sm B SM0 errno_low ML SMP k ly S U W regs mem md ch _ ot ms1 mat1 Q Hk HPU HFRL Hsot Hw3 HS1 HJ1 HARU1).
intros S2 regs2 mem2 md2 pos HS2 HJ2 HARU2 HP2 Ha0 Eab Hfrs Hnin Hnev Hbb Hz HK.
set (sp1 := 32 * ((spZ regs - 160) / 32)) in *.
assert (Hin0 : In (0, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
pose proof (ARU_AR tfibsegs B ly S2 U W mem2 md2 HARU2) as HAR2.
destruct (frames_bounds tfibsegs B LAWS ly S2 W (unpoison U mem2) md2 0 pos HAR2 Hin0) as (HF4096 & HFc & HFapp).
change (fs_frame_bytes 0) with 64 in HFc, HFapp.
assert (HFsh : frame_addr ly 0 pos + 64 <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= frame_addr ly 0 pos)
  by (unfold in_app, kLowShadowBeg, ASAN_CEIL, kHighMemBeg in HFapp; unfold SHADOW_OFF; lia).
assert (HFimg : forall a, frame_addr ly 0 pos <= a < frame_addr ly 0 pos + 64 -> ~ in_img tfibsegs a)
  by (intros a Ha; exact (frm_img tfibsegs B LAWS ly S2 W (unpoison U mem2) md2 0 pos a HAR2 Hin0 ltac:(change (fs_frame_bytes 0) with 64; lia))).
assert (Q2 : getr regs2 2%bv = Z_to_bv 64 sp1) by (rewrite (fsw_pres _ _ 2%bv HP2 ltac:(pv_cs)); exact R2).
assert (Q8 : getr regs2 8%bv = Z_to_bv 64 (spZ regs))
  by (rewrite (fsw_pres _ _ 8%bv HP2 ltac:(pv_cs)), R8; unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
assert (Q9 : getr regs2 9%bv = Z_to_bv 64 sp1) by (rewrite (fsw_pres _ _ 9%bv HP2 ltac:(pv_cs)); exact R9).
assert (Q19 : getr regs2 19%bv = Z_to_bv 64 v) by (rewrite (fsw_pres _ _ 19%bv HP2 ltac:(pv_cs)), R19, H11; reflexivity).
assert (Q20 : getr regs2 20%bv = Z_to_bv 64 q) by (rewrite (fsw_pres _ _ 20%bv HP2 ltac:(pv_cs)), R20, H10; reflexivity).
assert (Q23 : getr regs2 23%bv = Z_to_bv 64 SHADOW_OFF) by (rewrite (fsw_pres _ _ 23%bv HP2 ltac:(pv_cs)); exact R23).
assert (Q3 : getr regs2 3%bv = getr regs 3%bv) by (rewrite (fsw_pres _ _ 3%bv HP2 ltac:(pv_cs)); exact R3).
assert (Q4 : getr regs2 4%bv = getr regs 4%bv) by (rewrite (fsw_pres _ _ 4%bv HP2 ltac:(pv_cs)); exact R4).
assert (Q10 : getr regs2 10%bv = Z_to_bv 64 (frame_addr ly 0 pos)) by (rewrite Ha0; reflexivity).
destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
apply (pv_seg1 B _ ot _ ly S S2 U W regs mem md regs2 mem2 md2 pos (spZ regs) sp1 v q Q
  (HS2 [Z_to_bv 64 (SHADOW_OFF + frame_addr ly 0 pos / 8)]) HJ2 HARU2 Hin0 Q10 Q23 Q20 Q8 Q9 Q19 Q2); try lia.
intros msh math Hmsh HJ3 HARU3 KEEP3 Vsv3 Vfl3 S1 S10 S2r S3 S4 S8 S9 S18 S19 S20 S23 S26 S27.
(* the three memory steps, as pointwise agreement of the restricted memories *)
assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 160 <= a < spZ regs) -> ~ pv_wr1 (frame_addr ly 0 pos) (spZ regs) sp1 a ->
  mrestrict (w_H W) mem2 (Z_to_bv 64 a) = mrestrict (w_H W) (ms_mem ms1) (Z_to_bv 64 a) ->
  mrestrict (w_H W) (ms_mem msh) (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a)).
{ intros a Ha N1 N3 E2.
  rewrite (KEEP3 (Z_to_bv 64 a) ltac:(rewrite wz by lia; exact N3)), E2.
  exact (KEEP1 (Z_to_bv 64 a) ltac:(rewrite wz by lia; exact N1)). }
(* a block byte (application memory) is kept by the grant *)
assert (GB : forall b m a, In (b, m) (ablocks B ly S) -> b <= a < b + req_size m ->
  mrestrict (w_H W) mem2 (Z_to_bv 64 a) = mrestrict (w_H W) (ms_mem ms1) (Z_to_bv 64 a)).
{ intros b m a Hb Ha.
  destruct (fsw_ablock_low B ly S W (unpoison U mem) md b m HAR0 Hb) as (Ab1 & Ab2 & _).
  apply (pv_M_of_aviewU B ly S U W (ms_mem ms1) _ ly S2 U W mem2 md2 a HARU1 HARU2); [lia | | |].
  - exact (blk_img tfibsegs B LAWS ly S W (unpoison U mem) md b m a HAR0 Hb Ha).
  - exact (fsw_ablock_off_shadow B ly S W (unpoison U mem) md b m HAR0 Hb a Ha).
  - replace a with (b + (a - b)) by lia. apply (K2 b m (a - b) Hb); [lia | tauto]. }
(* ... and a byte of a frame of frames S *)
assert (GF : forall cid pos' a, In (cid, pos') (frames S) ->
  frame_addr ly cid pos' <= a < frame_addr ly cid pos' + fs_frame_bytes cid ->
  mrestrict (w_H W) mem2 (Z_to_bv 64 a) = mrestrict (w_H W) (ms_mem ms1) (Z_to_bv 64 a)).
{ intros cid pos' a Hf Ha.
  destruct (frames_bounds tfibsegs B LAWS ly S W (unpoison U mem) md cid pos' HAR0 Hf) as (Fb1 & Fb2 & Fapp).
  apply (pv_M_of_aviewU B ly S U W (ms_mem ms1) _ ly S2 U W mem2 md2 a HARU1 HARU2); [lia | | |].
  - exact (frm_img tfibsegs B LAWS ly S W (unpoison U mem) md cid pos' a HAR0 Hf Ha).
  - unfold in_app, kLowShadowBeg, ASAN_CEIL, kHighMemBeg in Fapp. unfold SHADOW_OFF. lia.
  - apply (K4 cid pos' a Hf); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | tauto]. }
(* F is apart from the blocks and from the frames of frames S *)
assert (FB : forall b m, In (b, m) (ablocks B ly S) ->
  b + req_size m <= frame_addr ly 0 pos \/ frame_addr ly 0 pos + 64 <= b).
{ intros b m Hb. rewrite <- Eab in Hb.
  pose proof (sep_block_frame tfibsegs B LAWS ly S2 W (unpoison U mem2) md2 b m 0 pos HAR2 Hb Hin0) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. change (fs_frame_bytes 0) with 64 in D. lia. }
assert (FF : forall cid pos', In (cid, pos') (frames S) ->
  frame_addr ly cid pos' + fs_frame_bytes cid <= frame_addr ly 0 pos \/ frame_addr ly 0 pos + 64 <= frame_addr ly cid pos').
{ intros cid pos' Hf. destruct (in_split _ _ Hf) as (l1 & l2 & El).
  pose proof (sep_frames_pos tfibsegs B LAWS ly S2 W (unpoison U mem2) md2 (0, pos) (cid, pos') [] l1 l2 HAR2
    ltac:(rewrite Hfrs, El; reflexivity)) as D.
  unfold zdisjoint, frame_rng in D. cbn [fst snd] in D. change (fs_frame_bytes 0) with 64 in D. lia. }
apply (K S2 pos msh _ Hmsh HJ3 HARU3 Hfrs Hnin Eab Hnev Hbb S1 S10 S2r); try assumption.
- rewrite S3. exact Q3.
- rewrite S4. exact Q4.
- (* at and above the entry sp *)
  intros a Ha. apply AG; [lia | lia | unfold pv_wr1; unfold SHADOW_OFF in *; lia |].
  apply (pv_M_of_aviewU B ly S U W (ms_mem ms1) _ ly S2 U W mem2 md2 a HARU1 HARU2); [lia | apply NIMG; unfold FS_IMG_END in *; lia
    | unfold SHADOW_OFF in *; lia |].
  apply K1; [lia | lia].
- (* the text block *)
  intros a Ha. apply AG; [lia | lia | |].
  + pose proof (FB _ _ HinT) as D. rewrite RqT in D.
    pose proof (fsw_ablock_off_shadow B ly S W (unpoison U mem) md _ _ HAR0 HinT a ltac:(rewrite RqT; unfold HEAD in *; lia)) as NS.
    unfold pv_wr1. unfold HEAD in *. unfold SHADOW_OFF in *. lia.
  + apply (GB (text - HEAD) (tcap + HEAD) a HinT). rewrite RqT. unfold HEAD in *. lia.
- (* v *)
  intros a Ha.
  assert (NS : ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44))
    by exact (fsw_pobj_off_shadow B ly S W (unpoison U mem) md mem v HAR0 HPO a Ha).
  destruct HPO as [[((cid & pos' & Hf & _ & _ & H1 & H2) & _)|((b & m & Hb & H1 & H2) & _)] _].
  + apply AG; [lia | lia | pose proof (FF cid pos' Hf); unfold pv_wr1; unfold SHADOW_OFF in *; lia |].
    apply (GF cid pos' a Hf). lia.
  + apply AG; [lia | lia | pose proof (FB b m Hb); unfold pv_wr1; unfold HEAD, SHADOW_OFF in *; lia |].
    apply (GB b m a Hb). unfold HEAD in *. lia.
- (* the statics: image bytes, not written by the two runs; the grant keeps them (IMG: not runtime-owned, not errno) *)
  assert (KI1 : forall a, in_img tfibsegs a -> mrestrict (w_H W) (ms_mem ms1) (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a)).
  { intros a Hi. pose proof (fs_segs_img a Hi) as Hlo. unfold FS_IMG_END in Hlo. apply KEEP1. rewrite wz by lia. lia. }
  assert (KI3 : forall a, in_img tfibsegs a -> mrestrict (w_H W) (ms_mem msh) (Z_to_bv 64 a) = mrestrict (w_H W) mem2 (Z_to_bv 64 a)).
  { intros a Hi. pose proof (fs_segs_img a Hi) as Hlo. unfold FS_IMG_END in Hlo. apply KEEP3. rewrite wz by lia.
    intros Hw. unfold pv_wr1 in Hw.
    destruct Hw as [Hw|[Hw|[Hw|Hw]]]; [exact (HFimg a Hw Hi) | unfold SHADOW_OFF in *; lia | lia | lia]. }
  apply (pv_glob_eqon W W mem2 (ms_mem msh)); [intros a Ha; exact (KI3 a (pv_pstat_img a Ha))|].
  apply (pv_glob_aview W W (ms_mem ms1) mem2).
  + intros a Ha. pose proof (pv_pstat_img a Ha) as Hi. pose proof (fs_segs_img a Hi) as Hlo.
    rewrite <- (pv_aview_low B ly S2 U W mem2 md2 a HARU2 ltac:(unfold FS_IMG_END, SHADOW_OFF in *; lia)).
    rewrite <- (pv_aview_low B ly S U W (ms_mem ms1) _ a HARU1 ltac:(unfold FS_IMG_END, SHADOW_OFF in *; lia)).
    exact (K3 a Hi (HPST_OWN a Ha) (HPST_ERRNO a Ha)).
  + apply (pv_glob_eqon W W mem (ms_mem ms1)); [|exact HG]. intros a Ha. exact (KI1 a (pv_pstat_img a Ha)).
- (* the read-only view: image bytes, the same three steps; the grant's image clause takes arodata's own premises *)
  intros a Ha Ho He. pose proof (fsw_roP_img a Ha) as Hi. pose proof (fs_segs_img a Hi) as Hlo. unfold FS_IMG_END in Hlo.
  assert (KI3 : mrestrict (w_H W) (ms_mem msh) (Z_to_bv 64 a) = mrestrict (w_H W) mem2 (Z_to_bv 64 a)).
  { apply KEEP3. rewrite wz by lia. intros Hw. unfold pv_wr1 in Hw.
    destruct Hw as [Hw|[Hw|[Hw|Hw]]]; [exact (HFimg a Hw Hi) | unfold SHADOW_OFF in *; lia | lia | lia]. }
  assert (KI1 : mrestrict (w_H W) (ms_mem ms1) (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a)).
  { apply KEEP1. rewrite wz by lia. lia. }
  rewrite (aview_eq_of tfibsegs _ _ _ a KI3).
  rewrite <- (pv_aview_low B ly S2 U W mem2 md2 a HARU2 ltac:(unfold SHADOW_OFF in *; lia)).
  rewrite (K3 a Hi Ho He).
  rewrite (pv_aview_low B ly S U W (ms_mem ms1) _ a HARU1 ltac:(unfold SHADOW_OFF in *; lia)).
  rewrite (aview_eq_of tfibsegs _ _ _ a KI1). exact (HRO a Ha Ho He).
Qed.

(* ---- where v lies at any point of the walk: in a live block that stays live (its head is off the footprint, which
   holds v's 56 bytes and the statics only) or in a frame of the entry frames; its shadow is addressable ---- *)
Lemma pv_frames_free : forall S6 pos (l : list (Z * Z)), frames S6 = (0, pos) :: l ->
  frames (stack_free_state 0 pos S6) = l.
Proof.
intros S6 pos l H. unfold frames in *. unfold stack_free_state, set_fs. cbn. rewrite H. cbn [del_pos].
rewrite !Z.eqb_refl. reflexivity.
Qed.
Lemma pv_ablocks_free : forall ly c p S, ablocks B ly (stack_free_state c p S) = ablocks B ly S.
Proof. intros ly c p S. unfold ablocks. rewrite blocks_stack_free_state. reflexivity. Qed.
Lemma pv_v_place : forall STK ot ly S U (W : world tfibsegs) mem md own lyc Sc Wc memc mdc kk v,
  ajournal tfibsegs B STK ot ([(v, v + 56)] ++ FS_PSTAT_FP) ly S W (unpoison U mem) md own lyc Sc Wc memc mdc kk ->
  ARU tfibsegs B ly S U W mem md -> pobj tfibsegs B ly S W mem v ->
  (exists b m, In (b, m) (ablocks B ly S) /\ In (b, m) (ablocks B lyc Sc) /\ b + HEAD <= v /\ v + 56 <= b + req_size m) \/
  (exists cid pos', In (cid, pos') (frames S) /\ 0 <= cid /\ frame_addr lyc cid pos' = frame_addr ly cid pos' /\
     frame_addr ly cid pos' mod 8 = 0 /\ frame_addr ly cid pos' <= v /\ v + 56 <= frame_addr ly cid pos' + fs_frame_bytes cid).
Proof.
intros STK ot ly S U W mem md own lyc Sc Wc memc mdc kk v HJ HU HPO.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof (ARU_AR tfibsegs B ly S U W mem md HU) as HAR.
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hgone & _).
destruct (al_layout tfibsegs B LAWS ly S W (unpoison U mem) md lyc HAR Hly) as (_ & HFA & _).
destruct HPO as [[((cid & pos' & Hf & Hc & H8 & H1 & H2) & _)|((b & m & Hb & H1 & H2) & _)] _].
- right. exists cid, pos'. split; [exact Hf|]. split; [exact Hc|]. split; [apply HFA|]. split; [exact H8|]. lia.
- left. exists b, m. split; [exact Hb|]. split; [|lia].
  assert (DEC : forall x y : Z * Z, {x = y} + {x <> y}) by (decide equality; apply Z.eq_dec).
  destruct (in_dec DEC (b, m) (ablocks B lyc Sc)) as [Hin|Hnin]; [exact Hin|exfalso].
  pose proof (Hgone b m 0 Hb Hnin ltac:(unfold HEAD in H1; lia)) as (r & Hr & Ha). rewrite Z.add_0_r in Ha.
  apply in_app_or in Hr as [Hr|Hr].
  + cbn [In] in Hr. destruct Hr as [<-|[]]. cbn [fst snd] in Ha. unfold HEAD in H1. lia.
  + exact (blk_img tfibsegs B LAWS ly S W (unpoison U mem) md b m b HAR Hb ltac:(unfold HEAD in H1; lia)
      (pv_pstat_img b (ex_intro _ r (conj Hr Ha)))).
Qed.
Lemma pv_v_awr : forall STK ot ly S U (W : world tfibsegs) mem md own lyc Sc Wc memc mdc kk v STKx sp0 a,
  ajournal tfibsegs B STK ot ([(v, v + 56)] ++ FS_PSTAT_FP) ly S W (unpoison U mem) md own lyc Sc Wc memc mdc kk ->
  ARU tfibsegs B ly S U W mem md -> pobj tfibsegs B ly S W mem v -> in_zr a (v, 56) ->
  awr_byte tfibsegs B STKx sp0 ([(v, v + 56)] ++ FS_PSTAT_FP) (ablocks B ly S) (ablocks B lyc Sc) lyc own (frames S) a.
Proof.
intros STK ot ly S U W mem md own lyc Sc Wc memc mdc kk v STKx sp0 a HJ HU HPO Ha. unfold in_zr in Ha. cbn [fst snd] in Ha.
assert (HFP : inFP ([(v, v + 56)] ++ FS_PSTAT_FP) a) by (exists (v, v + 56); split; [left; reflexivity | cbn [fst snd]; lia]).
destruct (pv_v_place STK ot ly S U W mem md own lyc Sc Wc memc mdc kk v HJ HU HPO)
  as [(b & m & Hb & Hbc & H1 & H2)|(cid & pos' & Hf & Hc & EF & H8 & H1 & H2)].
- left. right. left. split; [exact HFP|]. exists b, m. split; [exact Hbc | unfold HEAD in H1; lia].
- right. right. split; [exact HFP|]. exists cid, pos'. split; [exact Hf|]. unfold in_zr, frame_rng. cbn [fst snd].
  rewrite EF. lia.
Qed.
(* the heads of U are no shadow byte's granule of a byte of a frame *)
Lemma pv_ush_frame : forall ly S U (W : world tfibsegs) mem md cid pos x,
  ARU tfibsegs B ly S U W mem md -> FSupoisonU.fs_heads B ly S U -> In (cid, pos) (frames S) ->
  frame_addr ly cid pos <= x < frame_addr ly cid pos + fs_frame_bytes cid ->
  in_ush U (shadow_of_addr SHADOW_OFF x) = false.
Proof.
intros ly S U W mem md cid pos x HU FH Hf Hx.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof (ARU_AR tfibsegs B ly S U W mem md HU) as HAR.
destruct (frames_bounds tfibsegs B LAWS ly S W (unpoison U mem) md cid pos HAR Hf) as (F1 & _).
apply fsw_head_ush_out; [lia|]. intros r Hr. destruct (FH r Hr) as (E16 & m & Hm & M16).
destruct (al_blocks tfibsegs B LAWS ly S W (unpoison U mem) md (fst r) m HAR Hm) as (Q16 & _).
split; [exact E16|].
split; [apply Z.mod_divide in Q16 as [z Hz]; [|lia]; rewrite Hz; replace (z * 16) with ((z * 2) * 8) by lia; apply Z_mod_mult|].
pose proof (sep_block_frame tfibsegs B LAWS ly S W (unpoison U mem) md (fst r) m cid pos HAR Hm Hf) as D.
unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.
Lemma pv_ra_v : forall STK ot ly S U (W : world tfibsegs) mem md own lyc Sc Uc Wc memc mdc kk v,
  ajournal tfibsegs B STK ot ([(v, v + 56)] ++ FS_PSTAT_FP) ly S W (unpoison U mem) md own lyc Sc Wc
    (unpoison Uc memc) mdc kk ->
  ARU tfibsegs B ly S U W mem md -> ARU tfibsegs B lyc Sc Uc Wc memc mdc ->
  FSupoisonU.fs_heads B ly S U -> FSupoisonU.fs_heads B lyc Sc Uc ->
  pobj tfibsegs B ly S W mem v -> range_addressable (aview tfibsegs (w_H Wc) memc) SHADOW_OFF v 56.
Proof.
intros STK ot ly S U W mem md own lyc Sc Uc Wc memc mdc kk v HJ HU HUc FH FHc HPO.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof (ARU_AR tfibsegs B ly S U W mem md HU) as HAR.
pose proof (ARU_AR tfibsegs B lyc Sc Uc Wc memc mdc HUc) as HARc.
pose proof asan_consts as (C1 & _).
assert (HRA0 : range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF v 56)
  by (destruct HPO as [[(_ & _ & R)|(_ & _ & R)] _]; exact R).
destruct (pv_v_place STK ot ly S U W mem md own lyc Sc Wc (unpoison Uc memc) mdc kk v HJ HU HPO)
  as [(b & m & Hb & Hbc & H1 & H2)|(cid & pos' & Hf & Hc & EF & H8 & H1 & H2)].
- exact (fsw_block_body_addressable B lyc Sc Uc Wc memc mdc b m v 56 HUc FHc Hbc ltac:(unfold HEAD in H1; lia) ltac:(lia) H2).
- pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & Hfrm & _).
  assert (Hfc : In (cid, pos') (frames Sc)) by (rewrite Hfrs; apply in_or_app; right; exact Hf).
  destruct (frames_bounds tfibsegs B LAWS ly S W (unpoison U mem) md cid pos' HAR Hf) as (Fb1 & Fb2 & Fapp).
  destruct (al_frames tfibsegs B LAWS ly S W (unpoison U mem) md cid pos' HAR Hf) as (F32 & _).
  pose proof (YG0s.frame_facts B ly S _ cid pos' (proj1 HAR) Hf) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & B64 & _).
  intros x Hx. destruct (HRA0 x Hx) as (s & Es & Hok). exists s. split; [|exact Hok]. rewrite <- Es.
  assert (SR : SHADOW_OFF <= shadow_of_addr SHADOW_OFF x < SHADOW_OFF + 2 ^ 44)
    by (unfold shadow_of_addr, SHADOW_OFF; Z.div_mod_to_equations; lia).
  assert (S64 : 0 <= shadow_of_addr SHADOW_OFF x < 2 ^ 64) by (unfold SHADOW_OFF in SR |- *; lia).
  assert (E1 : aview tfibsegs (w_H Wc) (unpoison Uc memc) (shadow_of_addr SHADOW_OFF x) =
               aview tfibsegs (w_H W) (unpoison U mem) (shadow_of_addr SHADOW_OFF x)).
  { apply (Hfrm cid pos' _ Hf).
    - right. assert (Hxf : frame_addr ly cid pos' <= x < frame_addr ly cid pos' + fs_frame_bytes cid) by lia.
      unfold in_zr, shadow_addr, shadow_of_addr. cbn [fst snd].
      apply Z.mod_divide in F32 as [a8 Ha8]; [|lia]. apply Z.mod_divide in B64 as [b8 Hb8]; [|lia].
      rewrite Ha8, Hb8 in Hxf |- *. Z.div_mod_to_equations. lia.
    - intros (r & Hr & Ha). apply in_app_or in Hr as [Hr|Hr].
      + cbn [In] in Hr. destruct Hr as [<-|[]]. cbn [fst snd] in Ha.
        unfold in_app, kLowShadowBeg, ASAN_CEIL, kHighMemBeg in Fapp. unfold SHADOW_OFF in *. lia.
      + pose proof (fs_segs_img _ (pv_pstat_img _ (ex_intro _ r (conj Hr Ha)))) as Hi.
        unfold FS_IMG_END, SHADOW_OFF in *. lia. }
  rewrite <- (aview_unpoison_out tfibsegs (w_H Wc) Uc memc (shadow_of_addr SHADOW_OFF x))
    by (rewrite (wz _ S64); rewrite <- EF in H1, H2;
        exact (pv_ush_frame lyc Sc Uc Wc memc mdc cid pos' x HUc FHc Hfc ltac:(lia))).
  rewrite <- (aview_unpoison_out tfibsegs (w_H W) U mem (shadow_of_addr SHADOW_OFF x))
    by (rewrite (wz _ S64); exact (pv_ush_frame ly S U W mem md cid pos' x HU FH Hf ltac:(lia))).
  exact E1.
Qed.
(* ---- what the epilogue's writes (F, F's shadow, the flag byte: FSW_parse_value.pe_wr) do not touch: the stack, the
   image, live blocks and their shadow, the other live frames and their shadow ---- *)
Lemma pv_pe : forall ly S (W : world tfibsegs) m md pos (l : list (Z * Z)),
  AR tfibsegs B ly S W m md -> frames S = (0, pos) :: l ->
  (forall a, alloc_ceiling <= a -> ~ pe_wr (frame_addr ly 0 pos) (flag_addr ly 0 pos) a) /\
  (forall a, in_img tfibsegs a -> ~ pe_wr (frame_addr ly 0 pos) (flag_addr ly 0 pos) a) /\
  (forall b n a, In (b, n) (ablocks B ly S) -> b <= a < b + req_size n ->
     ~ pe_wr (frame_addr ly 0 pos) (flag_addr ly 0 pos) a /\
     ~ pe_wr (frame_addr ly 0 pos) (flag_addr ly 0 pos) (shadow_of_addr SHADOW_OFF a)) /\
  (forall cid p' a, In (cid, p') l -> frame_addr ly cid p' <= a < frame_addr ly cid p' + fs_frame_bytes cid ->
     ~ pe_wr (frame_addr ly 0 pos) (flag_addr ly 0 pos) a /\
     ~ pe_wr (frame_addr ly 0 pos) (flag_addr ly 0 pos) (shadow_of_addr SHADOW_OFF a)).
Proof.
intros ly S W m md pos l HAR Hfrs.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hin0 : In (0, pos) (frames S)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds tfibsegs B LAWS ly S W m md 0 pos HAR Hin0) as (HF4096 & HFc & HFapp).
destruct (al_frames _ _ LAWS ly S W m md 0 pos HAR Hin0) as (HF32 & _ & HFp & _).
destruct (al_flag _ _ LAWS ly S W m md 0 pos HAR Hin0) as (_ & HFLo & HFLapp & HFLc).
set (F := frame_addr ly 0 pos) in *. set (FL := flag_addr ly 0 pos) in *.
change (fs_frame_bytes 0) with 64 in *.
assert (GR : forall x, ~ (F <= x < F + 64) -> 0 <= x ->
  ~ (SHADOW_OFF + F / 8 <= shadow_of_addr SHADOW_OFF x < SHADOW_OFF + F / 8 + 8)).
{ intros x Hx Hx0. unfold shadow_of_addr. apply Z.mod_divide in HF32 as [f Hf]; [|lia]. rewrite Hf in Hx |- *.
  Z.div_mod_to_equations. lia. }
assert (HF8 : F / 8 + 8 <= 2 ^ 44) by (unfold in_app, kLowShadowBeg, ASAN_CEIL, kHighMemBeg in HFapp; Z.div_mod_to_equations; lia).
unfold pe_wr. split; [|split; [|split]].
- intros a Ha. unfold in_app, kLowShadowBeg, ASAN_CEIL, kHighMemBeg, SHADOW_OFF in *. lia.
- intros a Hi. pose proof (fs_segs_img a Hi) as Hlo. intros [H|[H|H]].
  + exact (frm_img tfibsegs B LAWS ly S W m md 0 pos a HAR Hin0 ltac:(change (fs_frame_bytes 0) with 64; fold F; lia) Hi).
  + unfold FS_IMG_END, SHADOW_OFF in *. lia.
  + assert (a = FL) by lia. subst a.
    exact (proj2 (al_client_img tfibsegs B LAWS ly S W m md FL HAR ltac:(right; right; exists 0, pos; split; [exact Hin0 | reflexivity])) Hi).
- intros b n a Hb Ha.
  pose proof (sep_block_frame tfibsegs B LAWS ly S W m md b n 0 pos HAR Hb Hin0) as D. unfold zdisjoint in D.
  cbn [fst snd] in D. change (fs_frame_bytes 0) with 64 in D. fold F in D.
  destruct (al_blocks _ _ LAWS ly S W m md b n HAR Hb) as (_ & Hb4096 & Hbc & Happ & Hbp & _).
  pose proof (fsw_ablock_off_shadow B ly S W m md b n HAR Hb a Ha) as NS.
  split.
  + intros [H|[H|H]]; [lia | unfold SHADOW_OFF in *; lia |].
    assert (a = FL) by lia. subst a. exact (proj2 (Hbp FL Ha) HFLo).
  + intros [H|[H|H]].
    * unfold shadow_of_addr, in_app, kLowShadowBeg, ASAN_CEIL, kHighMemBeg, SHADOW_OFF in *. Z.div_mod_to_equations. lia.
    * exact (GR a ltac:(lia) ltac:(lia) H).
    * unfold shadow_of_addr, in_app, kLowShadowBeg, ASAN_CEIL, kHighMemBeg, SHADOW_OFF in *. Z.div_mod_to_equations. lia.
- intros cid p' a Hl Ha. assert (Hf' : In (cid, p') (frames S)) by (rewrite Hfrs; right; exact Hl).
  destruct (in_split _ _ Hl) as (l1 & l2 & El).
  pose proof (sep_frames_pos tfibsegs B LAWS ly S W m md (0, pos) (cid, p') [] l1 l2 HAR
    ltac:(rewrite Hfrs, El; reflexivity)) as D.
  unfold zdisjoint, frame_rng in D. cbn [fst snd] in D. change (fs_frame_bytes 0) with 64 in D. fold F in D.
  destruct (frames_bounds tfibsegs B LAWS ly S W m md cid p' HAR Hf') as (G1 & G2 & G3).
  destruct (al_frames _ _ LAWS ly S W m md cid p' HAR Hf') as (_ & _ & Gp & _).
  split.
  + intros [H|[H|H]]; [lia | unfold in_app, kLowShadowBeg, ASAN_CEIL, kHighMemBeg, SHADOW_OFF in *; lia |].
    assert (a = FL) by lia. subst a. exact (proj2 (Gp FL Ha) HFLo).
  + intros [H|[H|H]].
    * unfold shadow_of_addr, in_app, kLowShadowBeg, ASAN_CEIL, kHighMemBeg, SHADOW_OFF in *. Z.div_mod_to_equations. lia.
    * exact (GR a ltac:(lia) ltac:(lia) H).
    * unfold shadow_of_addr, in_app, kLowShadowBeg, ASAN_CEIL, kHighMemBeg, SHADOW_OFF in *. Z.div_mod_to_equations. lia.
Qed.

(* ---- the spec's post (FSH_Fn_reader.v parse_value_spec, the text of its SRr predicate), named for the composition:
   pv_postQ is fpostU's state predicate at a block list D, pv_post the whole predicate ---- *)
Definition pv_postQ (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte)
  (q ot v text len p : Z) (tb : list byte) (tcap : Z) (u : PjTree.jv) (pr : bool) (ws : list Z) (live peak cnt fail : Z)
  (D : list (Z * Z)) : alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' W' regs' mem' md' =>
    YK11.getr regs' 10 = w64 0 /\
    PjIn.pj_in_ok tfibsegs (mrestrict (w_H W') mem') q text len
      (p + Z.of_nat (length ws) + Z.of_nat (length (concat (WriterValue.wvpieces u pr (Z.of_nat k))))) (Z.of_nat k) tb /\
    wkeep tfibsegs W W' mem mem' (spZ regs) ot q 24 /\
    Permutation (ablocks B ly' S') (ablocks B ly S ++ rd_hblocks D) /\
    rtree tfibsegs B ly' S' W' mem' v u D /\ rd_sum D = PjGrammar.held (PjRoundTrip.ttrace u) /\
    (length D <= length (PjRoundTrip.ttrace u))%nat /\
    pobj tfibsegs B ly' S' W' mem' v /\
    rd_text tfibsegs B ly' S' W' mem' text len tcap /\
    (exists peak', peak <= peak' /\
       fs_glob tfibsegs W' mem' (live + PjGrammar.held (PjRoundTrip.ttrace u)) peak'
         (cnt + Z.of_nat (length (PjRoundTrip.ttrace u))) fail).
Definition pv_post (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (q ot v text len p : Z) (tb : list byte) (tcap : Z) (u : PjTree.jv)
  (pr : bool) (ws : list Z) (live peak cnt fail : Z) : world tfibsegs -> config -> Prop :=
  fun W' c' => exists D Da,
    Permutation Da D /\
    fpostU tfibsegs B (STK_parse_value (2 - k) + (ot - spZ regs)) ot ([(v, v + 56)] ++ FS_PSTAT_FP) regs ly S U W mem md
      (rd_ev (PjRoundTrip.ttrace u)) (U ++ rd_heads Da)
      (pv_postQ ly S W regs mem q ot v text len p tb tcap u pr ws live peak cnt fail D) W' c'.

(* ---- stage B: the entry -> the skip_ws call 0x830d0 -> 0x830d4, with the data the dispatch and the two arms read:
   the journal from the entry (own [(0, pos)], no tick), the callee-saved registers, in->p past ws, the text, the
   statics, the read-only view, the save area and the flag word, the stack bytes of [sp, ot) but in->p, v's bytes ---- *)
Lemma pv_A : forall ly S U (W : world tfibsegs) regs mem md ch q ot v text len p tb tcap live peak cnt fail
  (ws wt rest : list Z) c0 (Q : world tfibsegs -> config -> Prop),
  fpreU tfibsegs B (STK_parse_value (2 - k)) ly S U W regs mem md ch -> FSupoisonU.fs_heads B ly S U ->
  Z.of_nat (length (frames S)) <= FRL_parse_value (Z.of_nat k) ->
  YK11.getr regs 10 = w64 q -> YK11.getr regs 11 = w64 v ->
  PjIn.pj_in_ok tfibsegs (mrestrict (w_H W) mem) q text len p (Z.of_nat k) tb -> rd_win tfibsegs regs ly W mem q ot ->
  spZ regs + 8 <= q ->
  rd_text tfibsegs B ly S W mem text len tcap ->
  ReaderRes.rest_at tb text p = ws ++ wt ++ rest -> Forall (fun c => PjGrammar.ws c = true) ws ->
  hd_error wt = Some c0 -> c0 = 34 \/ c0 = 123 ->
  pobj tfibsegs B ly S W mem v ->
  fs_glob tfibsegs W mem live peak cnt fail ->
  (forall ly2 S3 (W2 : world tfibsegs) regs2 mem2 md2 pos,
     ajournal tfibsegs B (STK_parse_value (2 - k) + (ot - spZ regs)) ot ([(v, v + 56)] ++ FS_PSTAT_FP) ly S W
       (unpoison U mem) md [(0, pos)] ly2 S3 W2 (unpoison U mem2) md2 0 ->
     ARU tfibsegs B ly2 S3 U W2 mem2 md2 ->
     ~ In (0, pos) (frames S) -> ablocks B ly2 S3 = ablocks B ly S ->
     YK11.getr regs2 2%bv = Z_to_bv 64 (32 * ((spZ regs - 160) / 32)) ->
     YK11.getr regs2 3%bv = YK11.getr regs 3%bv -> YK11.getr regs2 4%bv = YK11.getr regs 4%bv ->
     YK11.getr regs2 8%bv = Z_to_bv 64 (spZ regs) ->
     YK11.getr regs2 9%bv = Z_to_bv 64 (32 * ((spZ regs - 160) / 32)) ->
     YK11.getr regs2 18%bv = Z_to_bv 64 (frame_addr ly 0 pos) -> YK11.getr regs2 19%bv = Z_to_bv 64 v ->
     YK11.getr regs2 20%bv = Z_to_bv 64 q -> YK11.getr regs2 23%bv = Z_to_bv 64 SHADOW_OFF ->
     YK11.getr regs2 26%bv = Z_to_bv 64 (frame_addr ly 0 pos) ->
     YK11.getr regs2 27%bv = Z_to_bv 64 (SHADOW_OFF + frame_addr ly 0 pos / 8) ->
     PjIn.pj_in_ok tfibsegs (mrestrict (w_H W2) mem2) q text len (p + Z.of_nat (length ws)) (Z.of_nat k) tb ->
     rd_text tfibsegs B ly2 S3 W2 mem2 text len tcap ->
     fs_glob tfibsegs W2 mem2 live peak cnt fail ->
     arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W2) mem2) ->
     pv_saved_ok (mrestrict (w_H W2) mem2) (spZ regs) regs ->
     val_mem tfibsegs (mrestrict (w_H W2) mem2) (frame_addr ly 0 pos + 56) 8 (flag_addr ly 0 pos) ->
     (forall a, spZ regs <= a < ot -> ~ (q <= a < q + 8) ->
        mbyte tfibsegs (mrestrict (w_H W2) mem2) a = mbyte tfibsegs (mrestrict (w_H W) mem) a /\
        (writable_at tfibsegs (mrestrict (w_H W) mem) a <-> writable_at tfibsegs (mrestrict (w_H W2) mem2) a)) ->
     (forall x, v <= x < v + 56 -> mrestrict (w_H W2) mem2 (Z_to_bv 64 x) = mrestrict (w_H W) mem (Z_to_bv 64 x)) ->
     SRr tfibsegs W2 (YG0d.cfg_at tfibsegs 0x830d4 regs2 mem2 md2) Q) ->
  SRr tfibsegs W (YG0d.cfg_at tfibsegs A_parse_value regs mem md) Q.
Proof.
intros ly S U W regs mem md ch q ot v text len p tb tcap live peak cnt fail ws wt rest c0 Q HPRE FH HFRL H10 H11 HIN
  HWIN Hq8 HTX Hrest Hws Hc0 Hc0v HPO HG K.
pose proof (proj1 HPRE) as HPU.
pose proof (fsw_sp B _ ly S U W regs mem md ch HPU) as (Hal16 & Hceil & H47 & HS0).
pose proof (fsw_ARU B _ ly S U W regs mem md ch HPU) as HARU0.
pose proof (ARU_AR tfibsegs B ly S U W mem md HARU0) as HAR0.
pose proof HPU as ((_ & Hret & Hra4 & Hgp & Htp & Hstk & _ & HCHe & _) & _ & _).
pose proof (pv_stk_rel k Hk) as (SR1 & _ & _).
pose proof (pv_stk k Hk) as FSk.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HWIN as (Hw1 & Hw2 & Hw3 & Hw4 & Hpres).
pose proof Hstk as (_ & _ & Hslo & _ & _ & H47b & _ & Htop1 & Htop2).
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN) as (Bq0 & Bq24 & Bt0 & Bp & Btl & Bqt & Blen & Bq8 & Bd).
pose proof HTX as (Htx1 & HRB & Htc). pose proof HRB as (HinT & HalT & HtcT & VhT).
assert (Hsp8 : spZ regs mod 8 = 0)
  by (replace (spZ regs) with ((spZ regs / 16 * 2) * 8) by (pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)); lia);
      apply Z_mod_mult).
apply (pv_pre ly S U W regs mem md ch q ot v text len p tb tcap live peak cnt fail Q HPRE HFRL H10 H11 HIN HWIN Hq8 HTX
  HPO HG).
intros S2 pos msh mdh Hmsh HJ3 HARU3 Hfrs Hnin Eab Hnev Hbb S1 S10 S2r S3 S4 S8 S9 S18 S19 S20 S23 S26 S27 Vsv Vfl
  EQsp EQtx EQv HG3 HRO3.
set (sp1 := 32 * ((spZ regs - 160) / 32)) in *.
assert (Fsp1 : spZ regs - 176 <= sp1 <= spZ regs - 160 /\ sp1 mod 32 = 0).
{ pose proof (fsw_realign_facts (spZ regs - 160) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity)) as (F1 & F2 & F3).
  subst sp1. lia. }
assert (Hsp16 : sp1 mod 16 = 0)
  by (replace sp1 with ((sp1 / 32 * 2) * 16) by (pose proof (Z.div_mod sp1 32 ltac:(lia)); lia); apply Z_mod_mult).
assert (Csp : spZ (ms_regs msh) = sp1) by (unfold spZ; rewrite S2r; apply wz; lia).
assert (Hin0 : In (0, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
(* the chain fpreU reads at skip_ws' entry: parse_value's saved record on top of the entry chain *)
assert (HCH0 : exists ch0, achain ly (aview tfibsegs (w_H W) (unpoison U (ms_mem msh))) sp1 (s0Z (ms_regs msh)) ch0).
{ assert (Es0 : s0Z (ms_regs msh) = spZ regs) by (unfold s0Z; rewrite S8; apply wz; lia).
  rewrite Es0.
  assert (Hkept : achain ly (aview tfibsegs (w_H W) (unpoison U (ms_mem msh))) (spZ regs) (s0Z regs) ch).
  { apply (achain_kept ly _ _ (spZ regs) (s0Z regs) ch (spZ regs) HCHe ltac:(lia) ltac:(lia)).
    intros a Ha.
    rewrite (fsw_aview_unpoison_high B ly S2 U W (ms_mem msh) mdh a HARU3) by lia.
    rewrite (fsw_aview_unpoison_high B ly S U W mem md a HARU0) by lia.
    apply aview_eq_of. exact (EQsp a Ha). }
  pose proof (Vsv 0%nat ltac:(lia)) as V0. pose proof (Vsv 1%nat ltac:(lia)) as V1.
  cbn [Z.of_nat nth pv_saved pv_extra0 firstn tl] in V0, V1.
  replace (spZ regs - 8 * (0 + 1)) with (spZ regs - 8) in V0 by lia.
  replace (spZ regs - 8 * (1 + 1)) with (spZ regs - 16) in V1 by lia.
  apply (pv_chain_push ly _ (spZ regs) sp1 (s0Z regs) ch (raZ regs) Hkept ltac:(lia)).
  - rewrite (pv_rdword_U B ly S2 U W (ms_mem msh) mdh _ HARU3) by lia.
    exact (YF0x.val_mem_rdword (w_H W) (ms_mem msh) _ _ (u64_range _) V0).
  - rewrite (pv_rdword_U B ly S2 U W (ms_mem msh) mdh _ HARU3) by lia.
    exact (YF0x.val_mem_rdword (w_H W) (ms_mem msh) _ _ (u64_range _) V1).
  - exact Hra4.
  - lia.
  - exact Hsp8.
  - lia. }
(* skip_ws' data premises at its entry *)
assert (FH2 : FSupoisonU.fs_heads B ly S2 U) by (intros r Hr; rewrite Eab; exact (FH r Hr)).
assert (HIN2 : PjIn.pj_in_ok tfibsegs (mrestrict (w_H W) (ms_mem msh)) q text len p (Z.of_nat k) tb).
{ apply (pv_eqon_in (mrestrict (w_H W) mem) _ q text len p (Z.of_nat k) tb); [| |exact HIN].
  - eapply pv_eqon_sub; [exact EQsp | lia | lia].
  - eapply pv_eqon_sub; [exact EQtx | unfold HEAD; lia | lia]. }
assert (HWIN2 : rd_win tfibsegs (ms_regs msh) ly W (ms_mem msh) q ot).
{ pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & JP & _).
  unfold rd_win. rewrite Csp. split; [lia|]. split; [lia|]. split; [exact Hw3|]. split; [exact Hw4|].
  intros a Ha. apply (fsw_apresent_unpoison B ly S2 U W (ms_mem msh) mdh a HARU3); [lia|]. apply JP. lia. }
assert (HTX2 : rd_text tfibsegs B ly S2 W (ms_mem msh) text len tcap).
{ split; [exact Htx1|]. split; [|exact Htc]. split; [rewrite Eab; exact HinT|]. split; [exact HalT|]. split; [exact HtcT|].
  apply (pv_eqon_val (mrestrict (w_H W) mem) _ (text - HEAD) 8 tcap); [|exact VhT].
  eapply pv_eqon_sub; [exact EQtx | lia | cbn; unfold HEAD; lia]. }
assert (Hstop : forall c r, wt ++ rest = c :: r -> PjGrammar.ws c = false).
{ intros c r E. destruct wt as [|w wt']; [discriminate Hc0|]. cbn in Hc0, E. injection Hc0 as ->. injection E as -> _.
  destruct Hc0v as [->| ->]; reflexivity. }
rewrite Hmsh.
apply (pv_wscall B skip_ws_holds (STK_parse_value (2 - k) + (ot - spZ regs)) ot ([(v, v + 56)] ++ FS_PSTAT_FP) ly S U W
  mem md ly S2 W (ms_regs msh) (ms_mem msh) mdh pos q sp1 text len p
  (Z.of_nat k) tb tcap ws (wt ++ rest) live peak cnt fail Q Csp S10 S1 ltac:(rewrite S3; exact Hgp)
  ltac:(rewrite S4; exact Htp) Hsp16 ltac:(lia) ltac:(lia) HCH0 HRO3 FH2 HIN2 HWIN2 HTX2 Hrest Hws Hstop HG3 HJ3 HARU3).
intros ly2 S5 W2 regs2 mem2 md2 HJ4 HARU4 HJc OK4 PO4 HP4 QIN QWK QAB QTX QGL.
assert (P : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr (ms_regs msh) r)
  by (intros r Hr; exact (fsw_pres _ _ r HP4 Hr)).
(* the frames: F's flag word is a byte of the callee's live frame (0, pos), off its empty footprint *)
assert (KB : forall x, ((exists b n, In (b, n) (ablocks B ly S2) /\ b <= x < b + req_size n) \/
    (exists cid pos', In (cid, pos') (frames S2) /\ frame_addr ly cid pos' <= x < frame_addr ly cid pos' + fs_frame_bytes cid)) ->
  mrestrict (w_H W2) mem2 (Z_to_bv 64 x) = mrestrict (w_H W) (ms_mem msh) (Z_to_bv 64 x))
  by (intros x Hx; exact (proj2 (fsw_journal_kept_byte B _ _ _ ly S2 U W (ms_mem msh) mdh ly2 S5 U W2 mem2 md2 0 x
        HJc HARU3 OK4 PO4 Hx (pv_inFP_nil x)))).
apply (K ly2 S5 W2 regs2 mem2 md2 pos HJ4 HARU4 Hnin ltac:(rewrite QAB; exact Eab)).
- rewrite (P 2%bv ltac:(pv_cs)). exact S2r.
- rewrite (P 3%bv ltac:(pv_cs)). exact S3.
- rewrite (P 4%bv ltac:(pv_cs)). exact S4.
- rewrite (P 8%bv ltac:(pv_cs)). exact S8.
- rewrite (P 9%bv ltac:(pv_cs)). exact S9.
- rewrite (P 18%bv ltac:(pv_cs)). exact S18.
- rewrite (P 19%bv ltac:(pv_cs)). exact S19.
- rewrite (P 20%bv ltac:(pv_cs)). exact S20.
- rewrite (P 23%bv ltac:(pv_cs)). exact S23.
- rewrite (P 26%bv ltac:(pv_cs)). exact S26.
- rewrite (P 27%bv ltac:(pv_cs)). exact S27.
- exact QIN.
- exact QTX.
- exact QGL.
- exact (arodata_kept B _ _ _ ly S2 U W (ms_mem msh) mdh ly2 S5 U W2 mem2 md2 0 HJc HARU3 OK4 PO4 pv_sink_nil
    (fun a _ => pv_inFP_nil a) HRO3).
- (* the save area lies in [sp1, ot) below in->p *)
  apply (pv_saved_mb (mrestrict (w_H W) (ms_mem msh))); [|exact Vsv].
  intros a Ha. exact (proj1 (QWK a ltac:(lia) ltac:(lia))).
- (* the flag word *)
  apply (pv_val_mb (mrestrict (w_H W) (ms_mem msh))); [|exact Vfl].
  intros i Hi. apply pv_mb_of_mr. apply KB. right. exists 0, pos. split; [exact Hin0|].
  change (fs_frame_bytes 0) with 64. cbn in Hi. lia.
- (* the stack bytes of [sp, ot) but in->p *)
  intros a Ha Hq. destruct (QWK a ltac:(lia) Hq) as (M1 & W1).
  rewrite M1. split; [exact (pv_mb_of_mr _ _ _ _ a (EQsp a ltac:(lia)))|].
  rewrite <- W1. apply pv_wr_keep. exact (EQsp a ltac:(lia)).
- (* v's bytes: a block byte or a byte of a frame of the entry frames *)
  intros x Hx. rewrite (KB x), (EQv x Hx); [reflexivity|].
  destruct HPO as [[((cid & pos' & Hf & _ & _ & H1 & H2) & _)|((b & m & Hb & H1 & H2) & _)] _].
  + right. exists cid, pos'. split; [rewrite Hfrs; right; exact Hf | lia].
  + left. exists b, m. split; [rewrite Eab; exact Hb | unfold HEAD in H1; lia].
Qed.

(* ---- stage C, the string arm: 0x830d4 -> the dispatch -> parse_string 0x831ac -> 0x831b0 -> v->str -> the epilogue
   -> ret, from pv_A's data, to the spec's post at D = Da = [(a, |s| + 1)] ---- *)
Lemma pv_strarm : forall ly S U (W : world tfibsegs) regs mem md ch q ot v text len p tb tcap (s : list Z) pr
    (ws rest : list Z) live peak cnt fail ly2 S3 (W2 : world tfibsegs) regs2 mem2 md2 pos,
  let u := PjTree.JStr s in
  fpreU tfibsegs B (STK_parse_value (2 - k)) ly S U W regs mem md ch -> FSupoisonU.fs_heads B ly S U ->
  PjIn.pj_in_ok tfibsegs (mrestrict (w_H W) mem) q text len p (Z.of_nat k) tb -> rd_win tfibsegs regs ly W mem q ot ->
  (q = spZ regs + 8 /\ raZ regs <= q \/
   spZ regs + 16 <= q /\ exists chq, achain ly (aview tfibsegs (w_H W) (unpoison U mem)) (spZ regs) q chq /\
     Forall (fun r => bad_next (fst (fst r)) (ly_top ly) (snd r) = true \/ q + 40 <= snd r) chq) ->
  rd_text tfibsegs B ly S W mem text len tcap ->
  ReaderRes.rest_at tb text p = ws ++ (34 :: s ++ [34]) ++ rest -> plain_bytes s ->
  pobj tfibsegs B ly S W mem v -> PjStruct.pj_zero tfibsegs (mrestrict (w_H W) mem) v ->
  (v + 56 <= text - HEAD \/ text + tcap <= v) ->
  quiet cnt fail (Z.of_nat (length (PjRoundTrip.ttrace u))) -> rd_sizes_ok (PjRoundTrip.ttrace u) ->
  live + rd_live (PjRoundTrip.ttrace u) < 2 ^ 64 ->
  st_nev S + rd_ev (PjRoundTrip.ttrace u) <= EV_MAX -> blocks_bytes S + rd_live (PjRoundTrip.ttrace u) <= LIVE_MAX ->
  ajournal tfibsegs B (STK_parse_value (2 - k) + (ot - spZ regs)) ot ([(v, v + 56)] ++ FS_PSTAT_FP) ly S W
    (unpoison U mem) md [(0, pos)] ly2 S3 W2 (unpoison U mem2) md2 0 ->
  ARU tfibsegs B ly2 S3 U W2 mem2 md2 ->
  ~ In (0, pos) (frames S) -> ablocks B ly2 S3 = ablocks B ly S ->
  YK11.getr regs2 2%bv = Z_to_bv 64 (32 * ((spZ regs - 160) / 32)) ->
  YK11.getr regs2 3%bv = YK11.getr regs 3%bv -> YK11.getr regs2 4%bv = YK11.getr regs 4%bv ->
  YK11.getr regs2 8%bv = Z_to_bv 64 (spZ regs) ->
  YK11.getr regs2 9%bv = Z_to_bv 64 (32 * ((spZ regs - 160) / 32)) ->
  YK11.getr regs2 18%bv = Z_to_bv 64 (frame_addr ly 0 pos) -> YK11.getr regs2 19%bv = Z_to_bv 64 v ->
  YK11.getr regs2 20%bv = Z_to_bv 64 q -> YK11.getr regs2 23%bv = Z_to_bv 64 SHADOW_OFF ->
  YK11.getr regs2 26%bv = Z_to_bv 64 (frame_addr ly 0 pos) ->
  YK11.getr regs2 27%bv = Z_to_bv 64 (SHADOW_OFF + frame_addr ly 0 pos / 8) ->
  PjIn.pj_in_ok tfibsegs (mrestrict (w_H W2) mem2) q text len (p + Z.of_nat (length ws)) (Z.of_nat k) tb ->
  rd_text tfibsegs B ly2 S3 W2 mem2 text len tcap ->
  fs_glob tfibsegs W2 mem2 live peak cnt fail ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W2) mem2) ->
  pv_saved_ok (mrestrict (w_H W2) mem2) (spZ regs) regs ->
  val_mem tfibsegs (mrestrict (w_H W2) mem2) (frame_addr ly 0 pos + 56) 8 (flag_addr ly 0 pos) ->
  (forall a, spZ regs <= a < ot -> ~ (q <= a < q + 8) ->
     mbyte tfibsegs (mrestrict (w_H W2) mem2) a = mbyte tfibsegs (mrestrict (w_H W) mem) a /\
     (writable_at tfibsegs (mrestrict (w_H W) mem) a <-> writable_at tfibsegs (mrestrict (w_H W2) mem2) a)) ->
  (forall x, v <= x < v + 56 -> mrestrict (w_H W2) mem2 (Z_to_bv 64 x) = mrestrict (w_H W) mem (Z_to_bv 64 x)) ->
  SRr tfibsegs W2 (YG0d.cfg_at tfibsegs 0x830d4 regs2 mem2 md2)
    (pv_post ly S U W regs mem md q ot v text len p tb tcap u pr ws live peak cnt fail).
Proof.
intros ly S U W regs mem md ch q ot v text len p tb tcap s pr ws rest live peak cnt fail ly2 S3 W2 regs2 mem2 md2 pos u
  HPRE FH HIN HWIN HCHQ HTX Hrest Hplain HPO HZ Hvtx Hquiet Hsz Hlive Hnev Hbb
  HJ4 HARU4 Hnin AB R2 R3 R4 R8 R9 R18 R19 R20 R23 R26 R27 QIN2 QTX2 QG2 QRO2 SV2 FL2 SKS VK.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 HPRE) as HPU.
pose proof (fsw_sp B _ ly S U W regs mem md ch HPU) as (Hal16 & Hceil & H47 & HS0).
pose proof (fsw_ARU B _ ly S U W regs mem md ch HPU) as HARU0.
pose proof (ARU_AR tfibsegs B ly S U W mem md HARU0) as HAR0.
pose proof HPU as ((_ & Hret & Hra4 & Hgp & Htp & Hstk & _ & HCHe & _) & _ & _).
pose proof (pv_stk_rel k Hk) as (_ & SR2 & _).
pose proof (pv_stk k Hk) as FSk.
pose proof HWIN as (Hw1 & Hw2 & Hw3 & Hw4 & Hpres).
pose proof Hstk as (_ & _ & Hslo & Hslo2 & _ & H47b & _ & Htop1 & Htop2).
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN) as (Bq0 & Bq24 & Bt0 & Bp & Btl & Bqt & Blen & Bq8 & Bd).
pose proof HTX as (Htx1 & HRB & Htc). pose proof HRB as (HinT & HalT & HtcT & VhT).
destruct (fsw_ablock_low B ly S W (unpoison U mem) md (text - HEAD) (tcap + HEAD) HAR0 HinT) as (Tb1 & Tb2 & Tb3).
assert (RqT : req_size (tcap + HEAD) = tcap + HEAD) by (unfold req_size, HEAD; destruct (Z.eqb_spec (tcap + 16) 0); lia).
destruct (fsw_pobj_low B ly S W (unpoison U mem) md mem v HAR0 HPO) as (Hv1 & Hv2).
assert (Hv8 : v mod 8 = 0) by (destruct HPO as [[(_ & H8 & _)|(_ & H8 & _)] _]; exact H8).
assert (Hvsh : v + 56 <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= v).
{ pose proof (fsw_pobj_off_shadow B ly S W (unpoison U mem) md mem v HAR0 HPO) as NS.
  destruct (Z_le_gt_dec (v + 56) SHADOW_OFF) as [|H]; [left; lia|right].
  destruct (Z_le_gt_dec (SHADOW_OFF + 2 ^ 44) v) as [|H']; [lia|].
  exfalso. apply (NS (Z.max v SHADOW_OFF)); lia. }
pose proof HJ4 as (_ & Hly4 & _ & _ & _ & Hfrs4 & Hnev4 & _ & JHI4 & _ & _ & _ & _ & JP4 & _).
cbn [app] in Hfrs4.
destruct (pv_ly_top _ _ _ Hly4) as (ET4 & EL4 & EH4).
assert (FH4 : FSupoisonU.fs_heads B ly2 S3 U) by (intros r Hr; rewrite AB; exact (FH r Hr)).
set (sp1 := 32 * ((spZ regs - 160) / 32)) in *.
assert (Fsp1 : spZ regs - 176 <= sp1 <= spZ regs - 160 /\ sp1 mod 32 = 0).
{ pose proof (fsw_realign_facts (spZ regs - 160) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity)) as (F1 & F2 & F3).
  subst sp1. lia. }
assert (Hsp16 : sp1 mod 16 = 0)
  by (replace sp1 with ((sp1 / 32 * 2) * 16) by (pose proof (Z.div_mod sp1 32 ltac:(lia)); lia); apply Z_mod_mult).
assert (Hsp8 : spZ regs mod 8 = 0)
  by (replace (spZ regs) with ((spZ regs / 16 * 2) * 8) by (pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)); lia);
      apply Z_mod_mult).
(* the text at in->p + |ws|: the quote, the plain run, its copy *)
destruct (pv_str_text tb text len p ws s rest Blen ltac:(lia) Hrest Hplain) as (Hplt & Hquote & HPR & Hrun).
set (p' := p + Z.of_nat (length ws)) in *.
set (Qn := Z.of_nat (length s)) in *.
assert (Htr : PjRoundTrip.ttrace u = [PjGrammar.EAlloc (Datatypes.S (length s))]) by exact (pv_tr_str s Hplain).
rewrite Htr in Hquiet, Hsz, Hlive, Hnev, Hbb. cbn [length Z.of_nat rd_live rd_ev fold_right PjGrammar.esize] in Hquiet, Hsz,
  Hlive, Hnev, Hbb.
pose proof (Forall_inv Hsz) as Hsz1. cbn [PjGrammar.esize] in Hsz1.
(* v: not image, writable at 0x830d4, apart from F *)
assert (VNI : forall a0, v <= a0 < v + 56 -> ~ in_img tfibsegs a0).
{ intros a0 Ha0. refine (proj2 (al_client_img tfibsegs B LAWS ly S W (unpoison U mem) md a0 HAR0 _)).
  destruct HPO as [[((cid & pos' & Hf & _ & _ & H1 & H2) & _)|((b & m & Hb & H1 & H2) & _)] _].
  - right; left. exists cid, pos'. split; [exact Hf | lia].
  - left. exists b, m. split; [exact Hb | unfold HEAD in H1; lia]. }
assert (HVW2 : forall o, 0 <= o < 56 -> writable_at tfibsegs (mrestrict (w_H W2) mem2) (v + o)).
{ intros o Ho. pose proof HPO as [_ Hw]. apply (proj1 (pv_wr_keep _ _ (v + o) (VK (v + o) ltac:(lia)))). exact (Hw o Ho). }
pose proof (ARU_AR tfibsegs B ly2 S3 U W2 mem2 md2 HARU4) as HAR4.
assert (Hin04 : In (0, pos) (frames S3)) by (rewrite Hfrs4; left; reflexivity).
destruct (frames_bounds tfibsegs B LAWS ly2 S3 W2 (unpoison U mem2) md2 0 pos HAR4 Hin04) as (HF4096 & HFc & HFapp).
destruct (pv_ly_F _ ly ly2 0 pos Hly4) as (EF4 & EFL4).
change (fs_frame_bytes 0) with 64 in HFc, HFapp. rewrite EF4 in HF4096, HFc, HFapp.
assert (VF : forall x, v <= x < v + 56 -> ~ (frame_addr ly 0 pos <= x < frame_addr ly 0 pos + 64)).
{ intros x Hx.
  destruct (pv_v_place _ _ ly S U W mem md _ ly2 S3 W2 _ md2 _ v HJ4 HARU0 HPO)
    as [(b & m & Hb & Hbc & H1 & H2)|(cid & pos' & Hf & Hc & EF & H8 & H1 & H2)].
  - pose proof (sep_block_frame tfibsegs B LAWS ly2 S3 W2 (unpoison U mem2) md2 b m 0 pos HAR4 Hbc Hin04) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. change (fs_frame_bytes 0) with 64 in D. rewrite EF4 in D.
    unfold HEAD in H1. lia.
  - destruct (in_split _ _ Hf) as (l1 & l2 & El).
    pose proof (sep_frames_pos tfibsegs B LAWS ly2 S3 W2 (unpoison U mem2) md2 (0, pos) (cid, pos') [] l1 l2 HAR4
      ltac:(rewrite Hfrs4, El; reflexivity)) as D.
    unfold zdisjoint, frame_rng in D. cbn [fst snd] in D. change (fs_frame_bytes 0) with 64 in D. rewrite EF4, EF in D.
    lia. }
(* the dispatch's reads at 0x830d4 *)
assert (Hp'1 : text <= p') by lia.
pose proof (pv_byte_tb _ q text len p' (Z.of_nat k) tb p' (Z_to_bv 8 34) QIN2 Hp'1 Hquote) as Vc.
change (bv_unsigned (Z_to_bv 8 34)) with 34 in Vc.
pose proof QIN2 as (QB0 & QB8 & _).
assert (Vq0 : val_mem tfibsegs (mrestrict (w_H W2) mem2) q 8 p') by (apply fsw_pj_u64_val; split; [lia | exact QB0]).
assert (Vq8 : val_mem tfibsegs (mrestrict (w_H W2) mem2) (q + 8) 8 (text + len))
  by (apply fsw_pj_u64_val; split; [lia | exact QB8]).
assert (HinT2 : In (text - HEAD, tcap + HEAD) (ablocks B ly2 S3)) by (rewrite AB; exact HinT).
pose proof (fsw_block_body_addressable B ly2 S3 U W2 mem2 md2 (text - HEAD) (tcap + HEAD) p' 1 HARU4 FH4 HinT2
  ltac:(unfold HEAD; lia) ltac:(lia) ltac:(rewrite RqT; unfold HEAD in *; lia)) as RAc.
pose proof (pv_ra_v _ _ ly S U W mem md _ ly2 S3 U W2 mem2 md2 _ v HJ4 HARU0 HARU4 FH FH4 HPO) as RAv.
assert (Hcsh : p' + 1 <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= p').
{ pose proof (fsw_ablock_off_shadow B ly S W (unpoison U mem) md _ _ HAR0 HinT p' ltac:(rewrite RqT; unfold HEAD in *; lia)) as NS.
  lia. }
unfold YG0d.cfg_at, w64.
refine (pv_disp (fx := fx) (rc := rc) B (STK_parse_value (2 - k) + (ot - spZ regs)) ot ([(v, v + 56)] ++ FS_PSTAT_FP) ly S W
  (unpoison U mem) md
  [(0, pos)] ly2 S3 U W2 (mkst regs2 (Z_to_bv 64 0x830d4) mem2 (seg_rom tfibsegs)) md2 0 v q p' (text + len) 34 _
  eq_refl R19 R20 R23 Hv1 ltac:(lia) Hv8 Hvsh ltac:(lia) Bq8 ltac:(lia) ltac:(rewrite EL4; lia) ltac:(rewrite EH4; lia)
  ltac:(unfold HEAD in *; lia) ltac:(unfold HEAD in *; lia) ltac:(unfold HEAD in *; lia) ltac:(unfold HEAD in *; lia)
  ltac:(unfold HEAD in *; lia) Hcsh (or_introl eq_refl) Vq0 Vq8 Vc RAc RAv HVW2
  (fun a0 Ha0 => pv_v_awr _ _ ly S U W mem md _ ly2 S3 W2 _ md2 _ v _ _ a0 HJ4 HARU0 HPO Ha0) HJ4 HARU4 _ _).
2: { intros E. discriminate E. }
intros _ ms' mdx' Hms' C10r C1r CK Vty HJd HARUd KEEPd Wvd.
change (ms_regs (mkst regs2 (Z_to_bv 64 0x830d4) mem2 (seg_rom tfibsegs))) with regs2 in CK.
change (ms_mem (mkst regs2 (Z_to_bv 64 0x830d4) mem2 (seg_rom tfibsegs))) with mem2 in KEEPd.
set (regsC := ms_regs ms') in *. set (memC := ms_mem ms') in *.
assert (KC : forall a0, 0 <= a0 < 2 ^ 64 -> ~ (v <= a0 < v + 4) ->
  mrestrict (w_H W2) memC (Z_to_bv 64 a0) = mrestrict (w_H W2) mem2 (Z_to_bv 64 a0))
  by (intros a0 Ha0 Hn; apply KEEPd; rewrite wz by lia; exact Hn).
assert (Csp : spZ regsC = sp1) by (unfold spZ; rewrite (CK 2%bv ltac:(pv_inK)), R2; apply wz; lia).
assert (C3' : YK11.getr regsC 3%bv = w64 (as_gp B)) by (rewrite (CK 3%bv ltac:(pv_inK)), R3; exact Hgp).
assert (C4' : YK11.getr regsC 4%bv = w64 (as_tp B)) by (rewrite (CK 4%bv ltac:(pv_inK)), R4; exact Htp).
(* the two chains at parse_string's entry *)
set (rdC := aview tfibsegs (w_H W2) (unpoison U memC)). set (rd0 := aview tfibsegs (w_H W) (unpoison U mem)).
assert (BYT : forall b, spZ regs <= b < ly_top ly -> ~ (q <= b < q + 8) -> rdC b = rd0 b).
{ intros b Hb Hq. subst rdC rd0.
  rewrite (fsw_aview_unpoison_high B ly2 S3 U W2 memC mdx' b HARUd) by lia.
  rewrite (fsw_aview_unpoison_high B ly S U W mem md b HARU0) by lia.
  rewrite (pv_aview_eq2 (w_H W2) (w_H W2) mem2 memC b (KC b ltac:(lia) ltac:(lia))).
  destruct (Z_lt_le_dec b ot) as [Hbo|Hbo].
  - unfold aview. rewrite (proj1 (SKS b ltac:(lia) Hq)). reflexivity.
  - rewrite <- (fsw_aview_unpoison_high B ly2 S3 U W2 mem2 md2 b HARU4) by lia.
    rewrite <- (fsw_aview_unpoison_high B ly S U W mem md b HARU0) by lia.
    apply JHI4; lia. }
assert (SVC : pv_saved_ok (mrestrict (w_H W2) memC) (spZ regs) regs).
{ apply (pv_saved_mb (mrestrict (w_H W2) mem2)); [|exact SV2].
  intros a0 Ha0. exact (pv_mb_of_mr _ _ _ _ a0 (KC a0 ltac:(lia) ltac:(lia))). }
pose proof (SVC 0%nat ltac:(lia)) as V0. pose proof (SVC 1%nat ltac:(lia)) as V1.
cbn [Z.of_nat nth pv_saved pv_extra0 firstn tl] in V0, V1.
replace (spZ regs - 8 * (0 + 1)) with (spZ regs - 8) in V0 by lia.
replace (spZ regs - 8 * (1 + 1)) with (spZ regs - 16) in V1 by lia.
assert (W8 : rdword rdC (spZ regs - 8) = Some (raZ regs)).
{ subst rdC. rewrite (pv_rdword_U B ly2 S3 U W2 memC mdx' _ HARUd) by lia.
  exact (YF0x.val_mem_rdword (w_H W2) memC _ _ (u64_range _) V0). }
assert (W16 : rdword rdC (spZ regs - 16) = Some (s0Z regs)).
{ subst rdC. rewrite (pv_rdword_U B ly2 S3 U W2 memC mdx' _ HARUd) by lia.
  exact (YF0x.val_mem_rdword (w_H W2) memC _ _ (u64_range _) V1). }
assert (QINC : PjIn.pj_in_ok tfibsegs (mrestrict (w_H W2) memC) q text len p' (Z.of_nat k) tb).
{ apply (pv_eqon_in (mrestrict (w_H W2) mem2) _ q text len p' (Z.of_nat k) tb); [| |exact QIN2];
    intros a0 Ha0; apply KC; unfold HEAD in *; lia. }
assert (Hold : forall w, rdword rd0 q = Some w -> 4096 <= w < alloc_ceiling).
{ intros w Hw. subst rd0. rewrite (pv_rdword_U B ly S U W mem md _ HARU0) in Hw by lia.
  pose proof HIN as (HB0 & _).
  assert (U64 : PjStruct.pj_u64 tfibsegs (mrestrict (w_H W) mem) q p) by (split; [lia | exact HB0]).
  assert (Hp64 : 0 <= p < 2 ^ 64) by lia.
  rewrite (YF0x.val_mem_rdword (w_H W) mem q p Hp64 (fsw_pj_u64_val _ _ q p U64)) in Hw.
  injection Hw as <-. unfold HEAD in *. lia. }
assert (Hnew : exists w', rdword rdC q = Some w' /\ 4096 <= w' < alloc_ceiling).
{ exists p'. split; [|unfold HEAD in *; lia]. subst rdC. rewrite (pv_rdword_U B ly2 S3 U W2 memC mdx' _ HARUd) by lia.
  pose proof QINC as (HB0 & _).
  assert (U64 : PjStruct.pj_u64 tfibsegs (mrestrict (w_H W2) memC) q p') by (split; [lia | exact HB0]).
  assert (Hp64 : 0 <= p' < 2 ^ 64) by lia.
  exact (YF0x.val_mem_rdword (w_H W2) memC q p' Hp64 (fsw_pj_u64_val _ _ q p' U64)). }
assert (Hk0 : q = spZ regs + 8 -> exists w, rdword rdC (spZ regs) = Some w /\ 0 <= w).
{ intros Eq. apply pv_rdword_some. intros i Hi.
  change (rdC (spZ regs + i) <> None).
  rewrite (BYT (spZ regs + i) ltac:(lia) ltac:(lia)). subst rd0.
  rewrite (fsw_aview_unpoison_high B ly S U W mem md _ HARU0) by lia.
  apply aview_some_of_apresent. apply Hpres. lia. }
destruct (pv_call_chains ly ly2 rd0 rdC (spZ regs) (s0Z regs) (raZ regs) ch q sp1 HCHe HCHQ ET4 ltac:(lia) ltac:(lia)
  ltac:(lia) Hsp8 Bq8 ltac:(lia) BYT W8 W16 Hra4 Hold Hnew Hk0) as (HCH0 & HCHq).
(* lia case-splits every disjunctive hypothesis: drop the ones no later step reads *)
clear HCHQ Hcsh.
assert (Es0C : s0Z regsC = spZ regs) by (unfold s0Z; rewrite (CK 8%bv ltac:(pv_inK)), R8; apply wz; lia).
(* parse_string's other premises at its entry *)
assert (HWINC : rd_win tfibsegs regsC ly2 W2 memC q ot).
{ pose proof HJd as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & JPd & _).
  unfold rd_win. rewrite Csp. split; [lia|]. split; [lia|]. split; [exact Hw3|]. split; [rewrite ET4; exact Hw4|].
  intros a0 Ha0. apply (fsw_apresent_unpoison B ly2 S3 U W2 memC mdx' a0 HARUd); [lia|]. apply JPd. lia. }
assert (HTXC : rd_text tfibsegs B ly2 S3 W2 memC text len tcap).
{ pose proof QTX2 as (T1 & (T2 & T3 & T4 & T5) & T6). split; [exact T1|]. split; [|exact T6].
  split; [exact T2|]. split; [exact T3|]. split; [exact T4|].
  apply (pv_val_mb (mrestrict (w_H W2) mem2)); [|exact T5]. intros i Hi. cbn in Hi. apply pv_mb_of_mr.
  apply KC; unfold HEAD in *; lia. }
assert (HGC : fs_glob tfibsegs W2 memC live peak cnt fail).
{ apply (pv_glob_eqon W2 W2 mem2 memC); [|exact QG2]. intros a0 Ha0. pose proof (pv_pstat_img a0 Ha0) as Hi.
  pose proof (fs_segs_img a0 Hi) as Hlo. apply KC; [unfold FS_IMG_END in Hlo; lia|].
  intros Hv. exact (VNI a0 ltac:(lia) Hi). }
assert (HROC : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W2) memC)).
{ apply (pv_ro_keep B (aview tfibsegs (w_H W2) mem2)); [exact QRO2|]. intros a0 Ha0.
  pose proof (fsw_roP_img a0 Ha0) as Hi. pose proof (fs_segs_img a0 Hi) as Hlo.
  apply pv_aview_eq2. apply KC; [unfold FS_IMG_END in Hlo; lia|]. intros Hv. exact (VNI a0 ltac:(lia) Hi). }
assert (Ebb : blocks_bytes S3 = blocks_bytes S) by (rewrite (pv_bb B ly2 S3), AB, <- (pv_bb B ly S); reflexivity).
destruct (HCHq (sp1 - FRAME_parse_string) ltac:(unfold FRAME_parse_string; lia) ltac:(unfold FRAME_parse_string; lia))
  as (chq5 & HCHq5 & _).
rewrite Hms'.
refine (pv_strcall B parse_string_holds (STK_parse_value (2 - k) + (ot - spZ regs)) ot ([(v, v + 56)] ++ FS_PSTAT_FP)
  ly S U W mem md ly2 S3 W2 regsC memC mdx' pos q sp1 text len p' (Z.of_nat k) tb tcap Qn live peak cnt fail _
  Csp C10r C1r C3' C4' Hsp16 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite Es0C; exact HCH0)
  (ex_intro _ chq5 HCHq5)
  HROC FH4 QINC HWINC HTXC Hplt Hquote HPR HGC Hquiet ltac:(unfold HEAD in *; lia) ltac:(unfold HEAD in *; lia)
  ltac:(unfold HEAD in *; lia) ltac:(rewrite Ebb; unfold HEAD in *; lia) HJd HARUd
  (fun a0 Ha0 => match Ha0 with ex_intro _ r (conj Hr Har) => ex_intro _ r (conj (in_or_app _ _ _ (or_intror Hr)) Har) end)
  _).
intros ly3 S6 W3 regs3 mem3 md3 a HJ5 HARU5 HJc5 OK5 PO5 HP5 Q10 Q4096 Qab QRB Qcb QIN3 QWK3 QTX3 QGL3.
pose proof (ARU_AR tfibsegs B ly3 S6 _ W3 mem3 md3 HARU5) as HAR5.
pose proof (fsw_rblock_low B ly3 S6 W3 _ md3 mem3 a (Qn + 1) HAR5 QRB) as (Ra1 & Ra2).
pose proof QRB as (QRB1 & QRB2 & QRB3 & QRB4).
assert (FH5 : FSupoisonU.fs_heads B ly3 S6 (U ++ [(a - HEAD, HEAD)])).
{ intros r Hr. apply in_app_or in Hr as [Hr|Hr].
  - destruct (FH4 r Hr) as (E16 & m & Hm & M16). split; [exact E16|]. exists m.
    split; [rewrite Qab; apply in_or_app; left; exact Hm | exact M16].
  - cbn [In] in Hr. destruct Hr as [<-|[]]. cbn [fst snd]. split; [reflexivity|]. exists (Qn + 1 + HEAD).
    split; [rewrite Qab; apply in_or_app; right; left; reflexivity|].
    pose proof (req_size_pos (Qn + 1 + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hr2). unfold HEAD in *. lia. }
(* v's bytes across parse_string: a block byte or a byte of a frame of the entry frames, off the statics *)
assert (VPL3 : (exists b m, In (b, m) (ablocks B ly2 S3) /\ b + HEAD <= v /\ v + 56 <= b + req_size m) \/
               (exists cid pos', In (cid, pos') (frames S3) /\ frame_addr ly2 cid pos' <= v /\
                  v + 56 <= frame_addr ly2 cid pos' + fs_frame_bytes cid)).
{ destruct (pv_v_place _ _ ly S U W mem md _ ly2 S3 W2 _ mdx' _ v HJd HARU0 HPO)
    as [(b & m & Hb & Hbc & H1 & H2)|(cid & pos' & Hf & Hc & EF & H8 & H1 & H2)].
  - left. exists b, m. split; [exact Hbc|]. split; [exact H1 | exact H2].
  - right. exists cid, pos'. split; [rewrite Hfrs4; right; exact Hf|]. rewrite EF. lia. }
assert (VJ5 : forall x, v <= x < v + 56 ->
  mrestrict (w_H W3) mem3 (Z_to_bv 64 x) = mrestrict (w_H W2) memC (Z_to_bv 64 x)).
{ intros x Hx. refine (proj2 (fsw_journal_kept_byte B _ _ _ ly2 S3 U W2 memC mdx' ly3 S6 _ W3 mem3 md3 _ x HJc5 HARUd OK5
    PO5 _ _)).
  - destruct VPL3 as [(b & m & Hbc & H1 & H2)|(cid & pos' & Hf & H1 & H2)].
    + left. exists b, m. split; [exact Hbc | unfold HEAD in H1; lia].
    + right. exists cid, pos'. split; [exact Hf | lia].
  - intros Hin. exact (VNI x Hx (pv_pstat_img x Hin)). }
assert (HVW3 : forall o, 0 <= o < 56 -> writable_at tfibsegs (mrestrict (w_H W3) mem3) (v + o))
  by (intros o Ho; apply (proj1 (pv_wr_keep _ _ (v + o) (VJ5 (v + o) ltac:(lia)))); exact (Wvd o Ho)).
assert (R19' : YK11.getr regs3 19%bv = Z_to_bv 64 v)
  by (rewrite (fsw_pres _ _ 19%bv HP5 ltac:(pv_cs)), (CK 19%bv ltac:(pv_inK)); exact R19).
assert (R23' : YK11.getr regs3 23%bv = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (fsw_pres _ _ 23%bv HP5 ltac:(pv_cs)), (CK 23%bv ltac:(pv_inK)); exact R23).
unfold YG0d.cfg_at, w64.
refine (pv_str1 (fx := fx) (rc := rc) B (STK_parse_value (2 - k) + (ot - spZ regs)) ot ([(v, v + 56)] ++ FS_PSTAT_FP)
  ly S W (unpoison U mem) md [(0, pos)] ly3 S6 (U ++ [(a - HEAD, HEAD)]) W3 regs3 mem3 md3 EV_fuzz_malloc v a _
  R19' R23' Q10 Hv1 ltac:(lia) Hv8 ltac:(unfold HEAD in *; lia) Hvsh
  (pv_ra_v _ _ ly S U W mem md _ ly3 S6 _ W3 mem3 md3 _ v HJ5 HARU0 HARU5 FH FH5 HPO) HVW3
  (fun a0 Ha0 => pv_v_awr _ _ ly S U W mem md _ ly3 S6 W3 _ md3 _ v _ _ a0 HJ5 HARU0 HPO Ha0) HJ5 HARU5 _).
intros ms4 mdx4 Hms4 R21 PK Vstr HJ6 HARU6 KEEP6 Wv6.
clear Hvsh.
set (regs4 := ms_regs ms4) in *. set (mem4 := ms_mem ms4) in *.
rewrite Hms4.
pose proof HJ6 as (_ & Hly6 & _ & _ & _ & Hfrs6 & _). cbn [app] in Hfrs6.
destruct (pv_ly_F _ ly ly3 0 pos Hly6) as (EF6 & EFL6).
pose proof (ARU_AR tfibsegs B ly3 S6 _ W3 mem4 mdx4 HARU6) as HAR6.
assert (K6 : forall a0, 0 <= a0 < 2 ^ 64 -> ~ (v + 16 <= a0 < v + 24) ->
  mrestrict (w_H W3) mem4 (Z_to_bv 64 a0) = mrestrict (w_H W3) mem3 (Z_to_bv 64 a0))
  by (intros a0 Ha0 Hn; apply KEEP6; rewrite wz by lia; exact Hn).
assert (Hin06 : In (0, pos) (frames S6)) by (rewrite Hfrs6; left; reflexivity).
assert (SV4 : pv_saved_ok (mrestrict (w_H W3) mem4) (spZ regs) regs).
{ apply (pv_saved_mb (mrestrict (w_H W3) mem3)).
  - intros a0 Ha0. apply pv_mb_of_mr. apply K6; lia.
  - apply (pv_saved_mb (mrestrict (w_H W2) memC)); [|exact SVC]. intros a0 Ha0. exact (proj1 (QWK3 a0 ltac:(lia) ltac:(lia))). }
assert (FL4 : val_mem tfibsegs (mrestrict (w_H W3) mem4) (frame_addr ly3 0 pos + 56) 8 (flag_addr ly3 0 pos)).
{ rewrite EF6, EFL6. apply (pv_val_mb (mrestrict (w_H W2) mem2)); [|exact FL2].
  intros i Hi. cbn in Hi. apply pv_mb_of_mr.
  assert (Hx : ~ (v <= frame_addr ly 0 pos + 56 + i < v + 56)) by (intros Hx; exact (VF _ Hx ltac:(lia))).
  rewrite (K6 (frame_addr ly 0 pos + 56 + i) ltac:(lia) ltac:(lia)).
  assert (HFi : frame_addr ly2 0 pos <= frame_addr ly 0 pos + 56 + i < frame_addr ly2 0 pos + fs_frame_bytes 0)
    by (rewrite EF4; change (fs_frame_bytes 0) with 64; lia).
  rewrite (proj2 (fsw_journal_kept_byte B _ _ _ ly2 S3 U W2 memC mdx' ly3 S6 _ W3 mem3 md3 _ _ HJc5 HARUd OK5 PO5
    (or_intror (ex_intro _ 0 (ex_intro _ pos (conj Hin04 HFi))))
    (fun Hin => frm_img tfibsegs B LAWS ly2 S3 W2 (unpoison U mem2) md2 0 pos _ HAR4 Hin04 HFi (pv_pstat_img _ Hin)))).
  apply KC; lia. }
eapply SRr_mono.
{ refine (pv_epi (fx := fx) (rc := rc) B ML ASF FFL (STK_parse_value (2 - k) + (ot - spZ regs)) ot
    ([(v, v + 56)] ++ FS_PSTAT_FP) ly S U W mem md ly3 S6 (U ++ [(a - HEAD, HEAD)]) W3 regs regs4 mem4 mdx4 pos (spZ regs) 0
    EV_fuzz_malloc 0x8329c 21%bv []
    (pv_postQ ly S W regs mem q ot v text len p tb tcap u pr ws live peak cnt fail [(a, Qn + 1)])
    (or_introl (conj eq_refl eq_refl)) Hin06 _ _ _ _ R21 _ _ eq_refl Hret ltac:(lia) Hal16 ltac:(lia) ltac:(lia) SV4 FL4 HJ6
    HARU6 _).
  - rewrite (PK 8%bv ltac:(pv_inK)), (fsw_pres _ _ 8%bv HP5 ltac:(pv_cs)), (CK 8%bv ltac:(pv_inK)). exact R8.
  - rewrite EF6, (PK 18%bv ltac:(pv_inK)), (fsw_pres _ _ 18%bv HP5 ltac:(pv_cs)), (CK 18%bv ltac:(pv_inK)). exact R18.
  - rewrite EF6, (PK 27%bv ltac:(pv_inK)), (fsw_pres _ _ 27%bv HP5 ltac:(pv_cs)), (CK 27%bv ltac:(pv_inK)). exact R27.
  - rewrite EF6, (PK 26%bv ltac:(pv_inK)), (fsw_pres _ _ 26%bv HP5 ltac:(pv_cs)), (CK 26%bv ltac:(pv_inK)). exact R26.
  - rewrite (PK 3%bv ltac:(pv_inK)), (fsw_pres _ _ 3%bv HP5 ltac:(pv_cs)), (CK 3%bv ltac:(pv_inK)). exact R3.
  - rewrite (PK 4%bv ltac:(pv_inK)), (fsw_pres _ _ 4%bv HP5 ltac:(pv_cs)), (CK 4%bv ltac:(pv_inK)). exact R4.
  - intros mat regsf memf Hr10 KEEPf.
    destruct (pv_pe ly3 S6 W3 _ mdx4 pos (frames S) HAR6 Hfrs6) as (PEhi & PEimg & PEblk & PEfrm).
    assert (KF : forall a0, 0 <= a0 < 2 ^ 64 -> ~ pe_wr (frame_addr ly3 0 pos) (flag_addr ly3 0 pos) a0 ->
      mrestrict (w_H W3) memf (Z_to_bv 64 a0) = mrestrict (w_H W3) mem4 (Z_to_bv 64 a0))
      by (intros a0 Ha0 Hn; apply KEEPf; rewrite wz by lia; exact Hn).
    assert (Hnew6 : In (a - HEAD, Qn + 1 + HEAD) (ablocks B ly3 S6))
      by (rewrite Qab; apply in_or_app; right; left; reflexivity).
    assert (RqN : req_size (Qn + 1 + HEAD) = Qn + 1 + HEAD)
      by (unfold req_size, HEAD; destruct (Z.eqb_spec (Qn + 1 + 16) 0); lia).
    assert (HinT6 : In (text - HEAD, tcap + HEAD) (ablocks B ly3 S6))
      by (rewrite Qab; apply in_or_app; left; exact HinT2).
    assert (VPE : forall x, v <= x < v + 56 -> ~ pe_wr (frame_addr ly3 0 pos) (flag_addr ly3 0 pos) x /\
      ~ pe_wr (frame_addr ly3 0 pos) (flag_addr ly3 0 pos) (shadow_of_addr SHADOW_OFF x)).
    { intros x Hx. destruct (pv_v_place _ _ ly S U W mem md _ ly3 S6 W3 _ mdx4 _ v HJ6 HARU0 HPO)
        as [(b & m & Hb & Hb6 & H1 & H2)|(cid & pos' & Hf & Hc & EF & H8 & H1 & H2)].
      - exact (PEblk b m x Hb6 ltac:(unfold HEAD in H1; lia)).
      - exact (PEfrm cid pos' x Hf ltac:(rewrite EF; lia)). }
    assert (NBV : forall x, a - HEAD <= x < a + Qn + 1 -> ~ (v <= x < v + 56)).
    { intros x Hx Hv. destruct (pv_v_place _ _ ly S U W mem md _ ly3 S6 W3 _ mdx4 _ v HJ6 HARU0 HPO)
        as [(b & m & Hb & Hb6 & H1 & H2)|(cid & pos' & Hf & Hc & EF & H8 & H1 & H2)].
      - assert (Hb3 : In (b, m) (ablocks B ly2 S3)) by (rewrite AB; exact Hb).
        destruct (in_split _ _ Hb3) as (l1 & l2 & El).
        pose proof (sep_blocks_pos tfibsegs B LAWS ly3 S6 W3 _ mdx4 (b, m) (a - HEAD, Qn + 1 + HEAD) l1 l2 [] HAR6
          ltac:(rewrite Qab, El, <- app_assoc; reflexivity)) as D.
        unfold zdisjoint, block_rng in D. cbn [fst snd] in D. rewrite RqN in D. clear - D H1 H2 Hx Hv. unfold HEAD in *.
        lia.
      - pose proof (sep_block_frame tfibsegs B LAWS ly3 S6 W3 _ mdx4 (a - HEAD) (Qn + 1 + HEAD) cid pos' HAR6 Hnew6
          ltac:(rewrite Hfrs6; right; exact Hf)) as D.
        unfold zdisjoint in D. cbn [fst snd] in D. rewrite RqN, EF in D. clear - D H1 H2 Hx Hv. unfold HEAD in *. lia. }
    assert (VB4 : forall x, v <= x < v + 56 -> ~ (v <= x < v + 4) -> ~ (v + 16 <= x < v + 24) ->
      mrestrict (w_H W3) mem4 (Z_to_bv 64 x) = mrestrict (w_H W) mem (Z_to_bv 64 x)).
    { intros x Hx H1 H2. rewrite (K6 x ltac:(lia) H2), (VJ5 x Hx), (KC x ltac:(lia) H1). exact (VK x Hx). }
    assert (VTY4 : val_mem tfibsegs (mrestrict (w_H W3) mem4) v 4 4).
    { apply (pv_val_mb (mrestrict (w_H W2) memC)); [|exact Vty]. intros i Hi. cbn in Hi. apply pv_mb_of_mr.
      rewrite (K6 (v + i) ltac:(lia) ltac:(lia)). exact (VJ5 (v + i) ltac:(lia)). }
    pose proof HZ as ((HZ8 & (HZ0 & HZ1 & HZS)) & HZB).
    assert (ZU : forall off, off = 8 \/ off = 24 \/ off = 32 \/ off = 40 \/ off = 48 ->
      PjStruct.pj_u64 tfibsegs (mrestrict (w_H W3) mem4) (v + off) 0).
    { intros off Hoff. assert (Hoff' : 0 <= off <= 48) by (destruct Hoff as [->|[->|[->|[->| ->]]]]; lia).
      pose proof (PjStruct.pj_zero_u64 tfibsegs _ v off HZB Hoff') as (Hr & Hb). split; [exact Hr|].
      apply (pv_eqon_bytes (mrestrict (w_H W) mem)); [|exact Hb]. rewrite Mem.length_le8.
      intros x Hx. destruct Hoff as [->|[->|[->|[->| ->]]]]; apply VB4; lia. }
    assert (HDR4 : PjStruct.pj_hdr tfibsegs (mrestrict (w_H W3) mem4) v 4 0 a 0 0 0 0).
    { split.
      { split; [exact Hv8|]. split; [lia|]. split; [lia|]. intros a0 Ha0. split.
        - pose proof (Wv6 (a0 - v) ltac:(lia)) as Hw. replace (v + (a0 - v)) with a0 in Hw by lia. exact Hw.
        - destruct (Z_lt_le_dec a0 (v + 4)) as [L1|L1]; [|destruct (Z_lt_le_dec a0 (v + 16)) as [L2|L2];
            [|destruct (Z_lt_le_dec a0 (v + 24)) as [L3|L3]]].
          + pose proof (VTY4 (Z.to_nat (a0 - v)) ltac:(lia)) as E.
            replace (v + Z.of_nat (Z.to_nat (a0 - v))) with a0 in E by lia. eexists. exact E.
          + destruct (HZS a0 ltac:(lia)) as (_ & b & Hb). exists b.
            change (mbyte tfibsegs (mrestrict (w_H W3) mem4) a0 = Some b).
            rewrite (pv_mb_of_mr _ _ _ _ a0 (VB4 a0 ltac:(lia) ltac:(lia) ltac:(lia))). exact Hb.
          + pose proof (Vstr (Z.to_nat (a0 - (v + 16))) ltac:(lia)) as E.
            replace (v + 16 + Z.of_nat (Z.to_nat (a0 - (v + 16)))) with a0 in E by lia. eexists. exact E.
          + destruct (HZS a0 ltac:(lia)) as (_ & b & Hb). exists b.
            change (mbyte tfibsegs (mrestrict (w_H W3) mem4) a0 = Some b).
            rewrite (pv_mb_of_mr _ _ _ _ a0 (VB4 a0 ltac:(lia) ltac:(lia) ltac:(lia))). exact Hb. }
      split; [apply fsw_val_pj_u32; [exact VTY4 | lia | lia | lia]|].
      split; [exact (ZU 8 ltac:(lia))|].
      split; [apply fsw_val_pj_u64; [exact Vstr | unfold HEAD in *; lia | lia | lia]|].
      split; [exact (ZU 24 ltac:(lia))|]. split; [exact (ZU 32 ltac:(lia))|]. split; [exact (ZU 40 ltac:(lia))|].
      exact (ZU 48 ltac:(lia)). }
    assert (RA4 : range_addressable (aview tfibsegs (w_H W3) mem4) SHADOW_OFF v 56)
      by exact (pv_ra_v _ _ ly S U W mem md _ ly3 S6 _ W3 mem4 mdx4 _ v HJ6 HARU0 HARU6 FH FH5 HPO).
    assert (RAf : range_addressable (aview tfibsegs (w_H W3) memf) SHADOW_OFF v 56).
    { apply (pv_eqon_RA (w_H W3) (w_H W3) mem4 memf v 56); [|exact RA4]. intros a0 Ha0.
      apply KF; [unfold shadow_of_addr, SHADOW_OFF; Z.div_mod_to_equations; lia | exact (proj2 (VPE a0 Ha0))]. }
    assert (Ewt : concat (WriterValue.wvpieces u pr (Z.of_nat k)) = 34 :: s ++ [34])
      by exact (pv_wt_str s pr (Z.of_nat k) Hplain).
    unfold pv_postQ. rewrite Ewt.
    split; [exact Hr10|].
    split.
    { replace (p + Z.of_nat (length ws) + Z.of_nat (length (34 :: s ++ [34]))) with (p' + Qn + 2)
        by (cbn [length]; rewrite length_app; cbn [length]; lia).
      apply (pv_eqon_in (mrestrict (w_H W3) mem4) _ q text len (p' + Qn + 2) (Z.of_nat k) tb).
      - intros a0 Ha0. apply KF; [lia|]. apply PEhi. lia.
      - intros a0 Ha0. apply KF; [lia|]. exact (proj1 (PEblk _ _ a0 HinT6 ltac:(rewrite RqT; unfold HEAD in *; lia))).
      - apply (pv_eqon_in (mrestrict (w_H W3) mem3) _ q text len (p' + Qn + 2) (Z.of_nat k) tb); [| |exact QIN3].
        + intros a0 Ha0. apply K6; lia.
        + intros a0 Ha0. apply K6; [lia|]. unfold HEAD in *. lia. }
    split.
    { intros a0 Ha0 Hq.
      assert (E4 : mrestrict (w_H W3) memf (Z_to_bv 64 a0) = mrestrict (w_H W3) mem3 (Z_to_bv 64 a0))
        by (rewrite (KF a0 ltac:(lia) (PEhi a0 ltac:(lia))); apply K6; lia).
      destruct (QWK3 a0 ltac:(lia) Hq) as (M3 & Wr3).
      destruct (SKS a0 ltac:(lia) ltac:(lia)) as (M2 & Wr2).
      assert (EC : mrestrict (w_H W2) memC (Z_to_bv 64 a0) = mrestrict (w_H W2) mem2 (Z_to_bv 64 a0)) by (apply KC; lia).
      split.
      - rewrite (pv_mb_of_mr _ _ _ _ a0 E4), M3, (pv_mb_of_mr _ _ _ _ a0 EC). exact M2.
      - rewrite Wr2, (pv_wr_keep _ _ a0 EC), Wr3. apply pv_wr_keep. exact E4. }
    split.
    { rewrite pv_ablocks_free, Qab, AB. unfold rd_hblocks. cbn [map fst snd]. apply Permutation_refl. }
    split.
    { split; [|split; [|intros x Hx; exact Hx]].
      - change (PjStruct.pj_node tfibsegs (mrestrict (w_H W3) memf) (fun a0 k0 => In (a0, k0) [(a, Qn + 1)]) v
          (PjTree.JStr s) [(a, Qn + 1)]).
        cbn [PjStruct.pj_node]. split; [constructor; [intros Hin; inversion Hin | constructor]|].
        split.
        + intros b x Hb Hx. cbn [In] in Hb. destruct Hb as [<-|[]]. unfold PjStruct.pj_holds in Hx. cbn [fst snd] in Hx.
          apply (NBV x). unfold HEAD. lia.
        + exists 0, a, 0, 0, 0, 0. split.
          * apply (PjStruct.pj_hdr_eq tfibsegs (mrestrict (w_H W3) mem4)); [exact HDR4|].
            intros x Hx. apply KEEPf. exact (proj1 (VPE (bv_unsigned x) Hx)).
          * split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
            exists (Qn + 1). split; [|reflexivity].
            split; [left; reflexivity|]. split; [unfold Qn; lia|].
            rewrite Hrun in Qcb. destruct Qcb as (Qc1 & Qc2). split; [exact Qc1|].
            apply (pv_eqon_bytes (mrestrict (w_H W3) mem3)); [|exact Qc2].
            rewrite length_map, length_app. cbn [length]. intros x Hx.
            rewrite (KF x ltac:(unfold HEAD in *; lia)
              (proj1 (PEblk _ _ x Hnew6 ltac:(rewrite RqN; unfold Qn, HEAD in *; lia)))).
            apply K6; [unfold HEAD in *; lia|]. intros Hv'. apply (NBV x); [unfold Qn, HEAD in *; lia | lia].
      - intros a0 k0 Hak. cbn [In] in Hak. destruct Hak as [E|[]]. injection E as <- <-.
        split; [rewrite pv_ablocks_free; exact Hnew6|]. split; [exact QRB2|]. split; [exact QRB3|].
        apply (pv_val_mb (mrestrict (w_H W3) mem3)); [|exact QRB4]. intros i Hi. cbn in Hi. apply pv_mb_of_mr.
        rewrite (KF (a - HEAD + i) ltac:(unfold HEAD in *; lia)
          (proj1 (PEblk _ _ (a - HEAD + i) Hnew6 ltac:(rewrite RqN; unfold HEAD in *; lia)))).
        apply K6; [unfold HEAD in *; lia|]. intros Hv'. apply (NBV (a - HEAD + i)); [unfold HEAD in *; lia | lia]. }
    split; [rewrite Htr; cbn; lia|].
    split; [rewrite Htr; cbn; lia|].
    split.
    { split.
      - destruct (pv_v_place _ _ ly S U W mem md _ ly3 S6 W3 _ mdx4 _ v HJ6 HARU0 HPO)
          as [(b & m & Hb & Hb6 & H1 & H2)|(cid & pos' & Hf & Hc & EF & H8 & H1 & H2)].
        + right. split; [exists b, m; split; [rewrite pv_ablocks_free; exact Hb6 | lia]|]. split; [exact Hv8 | exact RAf].
        + left. split; [|split; [exact Hv8 | exact RAf]]. exists cid, pos'.
          split; [rewrite (pv_frames_free S6 pos (frames S) Hfrs6); exact Hf|]. split; [exact Hc|]. rewrite EF.
          split; [exact H8|]. lia.
      - intros i Hi. apply (proj1 (pv_wr_keep _ _ (v + i) (KF (v + i) ltac:(lia) (proj1 (VPE (v + i) ltac:(lia)))))).
        exact (Wv6 i Hi). }
    split.
    { pose proof QTX3 as (T1 & (T2 & T3 & T4 & T5) & T6). split; [exact T1|]. split; [|exact T6].
      split; [rewrite pv_ablocks_free; exact T2|]. split; [exact T3|]. split; [exact T4|].
      apply (pv_val_mb (mrestrict (w_H W3) mem3)); [|exact T5]. intros i Hi. cbn in Hi. apply pv_mb_of_mr.
      rewrite (KF (text - HEAD + i) ltac:(unfold HEAD in *; lia)
        (proj1 (PEblk _ _ (text - HEAD + i) HinT6 ltac:(rewrite RqT; unfold HEAD in *; lia)))). apply K6; [unfold HEAD in *; lia|].
      unfold HEAD in *. lia. }
    exists (Z.max peak (live + Qn + 1)). split; [lia|].
    rewrite Htr. cbn [PjGrammar.held PjGrammar.held_ev length Z.of_nat].
    replace (live + (Z.of_nat (Datatypes.S (length s)) + 0)) with (live + Qn + 1) by (unfold Qn; lia).
    apply (pv_glob_eqon W3 W3 mem3 memf); [|exact QGL3].
    intros a0 Ha0. pose proof (pv_pstat_img a0 Ha0) as Hi. pose proof (fs_segs_img a0 Hi) as Hlo.
    rewrite (KF a0 ltac:(unfold FS_IMG_END in Hlo; lia) (PEimg a0 Hi)). apply K6; [unfold FS_IMG_END in Hlo; lia|].
    intros Hv'. exact (VNI a0 ltac:(lia) Hi). }
intros W' c' _ HF. unfold pv_post. exists [(a, Qn + 1)], [(a, Qn + 1)]. split; [apply Permutation_refl|].
rewrite Htr. cbn [rd_ev fold_right]. rewrite Z.add_0_r. exact HF.
Qed.

(* ---- stage C, the object arm: 0x830d4 -> the dispatch -> parse_items 0x83278 -> 0x8327c -> the epilogue -> ret, from
   pv_A's data, to the spec's post at parse_items' own D, Da; k <= 1 since depth (JObj ms) >= 1 ---- *)
Lemma pv_objarm : forall ly S U (W : world tfibsegs) regs mem md ch q ot v text len p tb tcap
    (ms : list (list Z * PjTree.jv)) pr (ws rest : list Z) live peak cnt fail ly2 S3 (W2 : world tfibsegs) regs2 mem2 md2 pos,
  let u := PjTree.JObj ms in
  fpreU tfibsegs B (STK_parse_value (2 - k)) ly S U W regs mem md ch -> FSupoisonU.fs_heads B ly S U ->
  Z.of_nat (length (frames S)) <= FRL_parse_value (Z.of_nat k) ->
  PjIn.pj_in_ok tfibsegs (mrestrict (w_H W) mem) q text len p (Z.of_nat k) tb -> rd_win tfibsegs regs ly W mem q ot ->
  (q = spZ regs + 8 /\ raZ regs <= q \/
   spZ regs + 16 <= q /\ exists chq, achain ly (aview tfibsegs (w_H W) (unpoison U mem)) (spZ regs) q chq /\
     Forall (fun r => bad_next (fst (fst r)) (ly_top ly) (snd r) = true \/ q + 40 <= snd r) chq) ->
  rd_text tfibsegs B ly S W mem text len tcap ->
  ReaderRes.rest_at tb text p = ws ++ concat (WriterValue.wvpieces u pr (Z.of_nat k)) ++ rest ->
  FSDocStrs.fs_doc_values u -> FSDocStrs.fs_doc_strings u ->
  PjRoundTrip.pj_wf ReaderRes.jr_strtod u -> (PjTree.depth u <= 2 - k)%nat ->
  pobj tfibsegs B ly S W mem v -> PjStruct.pj_zero tfibsegs (mrestrict (w_H W) mem) v ->
  (v + 56 <= text - HEAD \/ text + tcap <= v) ->
  quiet cnt fail (Z.of_nat (length (PjRoundTrip.ttrace u))) -> rd_sizes_ok (PjRoundTrip.ttrace u) ->
  live + rd_live (PjRoundTrip.ttrace u) < 2 ^ 64 ->
  st_nev S + rd_ev (PjRoundTrip.ttrace u) <= EV_MAX -> blocks_bytes S + rd_live (PjRoundTrip.ttrace u) <= LIVE_MAX ->
  ajournal tfibsegs B (STK_parse_value (2 - k) + (ot - spZ regs)) ot ([(v, v + 56)] ++ FS_PSTAT_FP) ly S W
    (unpoison U mem) md [(0, pos)] ly2 S3 W2 (unpoison U mem2) md2 0 ->
  ARU tfibsegs B ly2 S3 U W2 mem2 md2 ->
  ~ In (0, pos) (frames S) -> ablocks B ly2 S3 = ablocks B ly S ->
  YK11.getr regs2 2%bv = Z_to_bv 64 (32 * ((spZ regs - 160) / 32)) ->
  YK11.getr regs2 3%bv = YK11.getr regs 3%bv -> YK11.getr regs2 4%bv = YK11.getr regs 4%bv ->
  YK11.getr regs2 8%bv = Z_to_bv 64 (spZ regs) ->
  YK11.getr regs2 9%bv = Z_to_bv 64 (32 * ((spZ regs - 160) / 32)) ->
  YK11.getr regs2 18%bv = Z_to_bv 64 (frame_addr ly 0 pos) -> YK11.getr regs2 19%bv = Z_to_bv 64 v ->
  YK11.getr regs2 20%bv = Z_to_bv 64 q -> YK11.getr regs2 23%bv = Z_to_bv 64 SHADOW_OFF ->
  YK11.getr regs2 26%bv = Z_to_bv 64 (frame_addr ly 0 pos) ->
  YK11.getr regs2 27%bv = Z_to_bv 64 (SHADOW_OFF + frame_addr ly 0 pos / 8) ->
  PjIn.pj_in_ok tfibsegs (mrestrict (w_H W2) mem2) q text len (p + Z.of_nat (length ws)) (Z.of_nat k) tb ->
  rd_text tfibsegs B ly2 S3 W2 mem2 text len tcap ->
  fs_glob tfibsegs W2 mem2 live peak cnt fail ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W2) mem2) ->
  pv_saved_ok (mrestrict (w_H W2) mem2) (spZ regs) regs ->
  val_mem tfibsegs (mrestrict (w_H W2) mem2) (frame_addr ly 0 pos + 56) 8 (flag_addr ly 0 pos) ->
  (forall a, spZ regs <= a < ot -> ~ (q <= a < q + 8) ->
     mbyte tfibsegs (mrestrict (w_H W2) mem2) a = mbyte tfibsegs (mrestrict (w_H W) mem) a /\
     (writable_at tfibsegs (mrestrict (w_H W) mem) a <-> writable_at tfibsegs (mrestrict (w_H W2) mem2) a)) ->
  (forall x, v <= x < v + 56 -> mrestrict (w_H W2) mem2 (Z_to_bv 64 x) = mrestrict (w_H W) mem (Z_to_bv 64 x)) ->
  SRr tfibsegs W2 (YG0d.cfg_at tfibsegs 0x830d4 regs2 mem2 md2)
    (pv_post ly S U W regs mem md q ot v text len p tb tcap u pr ws live peak cnt fail).
Proof.
intros ly S U W regs mem md ch q ot v text len p tb tcap ms pr ws rest live peak cnt fail ly2 S3 W2 regs2 mem2 md2 pos u
  HPRE FH HFRL HIN HWIN HCHQ HTX Hrest Hvals Hstrs Hwf Hdep HPO HZ Hvtx Hquiet Hsz Hlive Hnev Hbb
  HJ4 HARU4 Hnin AB R2 R3 R4 R8 R9 R18 R19 R20 R23 R26 R27 QIN2 QTX2 QG2 QRO2 SV2 FL2 SKS VK.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 HPRE) as HPU.
pose proof (fsw_sp B _ ly S U W regs mem md ch HPU) as (Hal16 & Hceil & H47 & HS0).
pose proof (fsw_ARU B _ ly S U W regs mem md ch HPU) as HARU0.
pose proof (ARU_AR tfibsegs B ly S U W mem md HARU0) as HAR0.
pose proof HPU as ((_ & Hret & Hra4 & Hgp & Htp & Hstk & _ & HCHe & _) & _ & _).
assert (Hk1 : (k <= 1)%nat).
{ assert (Hd1 : (1 <= PjTree.depth (PjTree.JObj ms))%nat) by (cbn [PjTree.depth]; lia).
  change (PjTree.depth (PjTree.JObj ms) <= 2 - k)%nat in Hdep. clear - Hd1 Hdep. lia. }
pose proof (pv_stk_rel k Hk) as (_ & _ & SR3). specialize (SR3 Hk1).
pose proof (pv_stk k Hk) as FSk.
pose proof HWIN as (Hw1 & Hw2 & Hw3 & Hw4 & Hpres).
pose proof Hstk as (_ & _ & Hslo & Hslo2 & _ & H47b & _ & Htop1 & Htop2).
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN) as (Bq0 & Bq24 & Bt0 & Bp & Btl & Bqt & Blen & Bq8 & Bd).
pose proof HTX as (Htx1 & HRB & Htc). pose proof HRB as (HinT & HalT & HtcT & VhT).
destruct (fsw_ablock_low B ly S W (unpoison U mem) md (text - HEAD) (tcap + HEAD) HAR0 HinT) as (Tb1 & Tb2 & Tb3).
assert (RqT : req_size (tcap + HEAD) = tcap + HEAD) by (unfold req_size, HEAD; destruct (Z.eqb_spec (tcap + 16) 0); lia).
destruct (fsw_pobj_low B ly S W (unpoison U mem) md mem v HAR0 HPO) as (Hv1 & Hv2).
assert (Hv8 : v mod 8 = 0) by (destruct HPO as [[(_ & H8 & _)|(_ & H8 & _)] _]; exact H8).
assert (Hvsh : v + 56 <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= v).
{ pose proof (fsw_pobj_off_shadow B ly S W (unpoison U mem) md mem v HAR0 HPO) as NS.
  destruct (Z_le_gt_dec (v + 56) SHADOW_OFF) as [|H]; [left; lia|right].
  destruct (Z_le_gt_dec (SHADOW_OFF + 2 ^ 44) v) as [|H']; [lia|].
  exfalso. apply (NS (Z.max v SHADOW_OFF)); lia. }
pose proof HJ4 as (_ & Hly4 & _ & _ & _ & Hfrs4 & Hnev4 & _ & JHI4 & _ & _ & _ & _ & JP4 & _).
cbn [app] in Hfrs4.
destruct (pv_ly_top _ _ _ Hly4) as (ET4 & EL4 & EH4).
assert (FH4 : FSupoisonU.fs_heads B ly2 S3 U) by (intros r Hr; rewrite AB; exact (FH r Hr)).
set (sp1 := 32 * ((spZ regs - 160) / 32)) in *.
assert (Fsp1 : spZ regs - 176 <= sp1 <= spZ regs - 160 /\ sp1 mod 32 = 0).
{ pose proof (fsw_realign_facts (spZ regs - 160) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity)) as (F1 & F2 & F3).
  subst sp1. lia. }
assert (Hsp16 : sp1 mod 16 = 0)
  by (replace sp1 with ((sp1 / 32 * 2) * 16) by (pose proof (Z.div_mod sp1 32 ltac:(lia)); lia); apply Z_mod_mult).
assert (Hsp8 : spZ regs mod 8 = 0)
  by (replace (spZ regs) with ((spZ regs / 16 * 2) * 8) by (pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)); lia);
      apply Z_mod_mult).
(* the text at in->p + |ws|: the brace *)
destruct (pv_wt_obj ms pr (Z.of_nat k)) as (r & Ewt). fold u in Ewt.
set (wt := concat (WriterValue.wvpieces u pr (Z.of_nat k))) in *.
set (p' := p + Z.of_nat (length ws)) in *.
assert (Hrest' : ReaderRes.rest_at tb text p' = wt ++ rest) by (apply pv_rest_skip; [clear - Bp; lia | exact Hrest]).
assert (HL0 : Z.of_nat (length (ReaderRes.rest_at tb text p)) = text + len - p).
{ unfold ReaderRes.rest_at, ReaderRes.zb. rewrite length_map, length_skipn. clear - Blen Bp. lia. }
rewrite Hrest, Ewt in HL0. rewrite !length_app in HL0. cbn [length] in HL0.
assert (Hplt : p' < text + len) by (subst p'; clear - HL0; lia).
destruct (pv_rest_byte tb text p' (wt ++ rest) 0 123 Hrest' ltac:(rewrite Ewt; reflexivity)) as (b0 & Hb0 & Eb0).
rewrite Nat.add_0_r in Hb0.
(* v: not image, writable at 0x830d4, apart from F *)
assert (VNI : forall a0, v <= a0 < v + 56 -> ~ in_img tfibsegs a0).
{ intros a0 Ha0. refine (proj2 (al_client_img tfibsegs B LAWS ly S W (unpoison U mem) md a0 HAR0 _)).
  destruct HPO as [[((cid & pos' & Hf & _ & _ & H1 & H2) & _)|((b & m & Hb & H1 & H2) & _)] _].
  - right; left. exists cid, pos'. split; [exact Hf | lia].
  - left. exists b, m. split; [exact Hb | unfold HEAD in H1; lia]. }
assert (HVW2 : forall o, 0 <= o < 56 -> writable_at tfibsegs (mrestrict (w_H W2) mem2) (v + o)).
{ intros o Ho. pose proof HPO as [_ Hw]. apply (proj1 (pv_wr_keep _ _ (v + o) (VK (v + o) ltac:(lia)))). exact (Hw o Ho). }
pose proof (ARU_AR tfibsegs B ly2 S3 U W2 mem2 md2 HARU4) as HAR4.
assert (Hin04 : In (0, pos) (frames S3)) by (rewrite Hfrs4; left; reflexivity).
destruct (pv_ly_F _ ly ly2 0 pos Hly4) as (EF4 & EFL4).
assert (VF : forall x, v <= x < v + 56 -> ~ (frame_addr ly 0 pos <= x < frame_addr ly 0 pos + 64)).
{ intros x Hx.
  destruct (pv_v_place _ _ ly S U W mem md _ ly2 S3 W2 _ md2 _ v HJ4 HARU0 HPO)
    as [(b & m & Hb & Hbc & H1 & H2)|(cid & pos' & Hf & Hc & EF & H8 & H1 & H2)].
  - pose proof (sep_block_frame tfibsegs B LAWS ly2 S3 W2 (unpoison U mem2) md2 b m 0 pos HAR4 Hbc Hin04) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. change (fs_frame_bytes 0) with 64 in D. rewrite EF4 in D.
    unfold HEAD in H1. lia.
  - destruct (in_split _ _ Hf) as (l1 & l2 & El).
    pose proof (sep_frames_pos tfibsegs B LAWS ly2 S3 W2 (unpoison U mem2) md2 (0, pos) (cid, pos') [] l1 l2 HAR4
      ltac:(rewrite Hfrs4, El; reflexivity)) as D.
    unfold zdisjoint, frame_rng in D. cbn [fst snd] in D. change (fs_frame_bytes 0) with 64 in D. rewrite EF4, EF in D.
    lia. }
(* the dispatch's reads at 0x830d4 *)
assert (Hp'1 : text <= p') by lia.
pose proof (pv_byte_tb _ q text len p' (Z.of_nat k) tb p' b0 QIN2 Hp'1 Hb0) as Vc. rewrite Eb0 in Vc.
pose proof QIN2 as (QB0 & QB8 & _).
assert (Vq0 : val_mem tfibsegs (mrestrict (w_H W2) mem2) q 8 p') by (apply fsw_pj_u64_val; split; [lia | exact QB0]).
assert (Vq8 : val_mem tfibsegs (mrestrict (w_H W2) mem2) (q + 8) 8 (text + len))
  by (apply fsw_pj_u64_val; split; [lia | exact QB8]).
assert (HinT2 : In (text - HEAD, tcap + HEAD) (ablocks B ly2 S3)) by (rewrite AB; exact HinT).
pose proof (fsw_block_body_addressable B ly2 S3 U W2 mem2 md2 (text - HEAD) (tcap + HEAD) p' 1 HARU4 FH4 HinT2
  ltac:(unfold HEAD; lia) ltac:(lia) ltac:(rewrite RqT; unfold HEAD in *; lia)) as RAc.
pose proof (pv_ra_v _ _ ly S U W mem md _ ly2 S3 U W2 mem2 md2 _ v HJ4 HARU0 HARU4 FH FH4 HPO) as RAv.
assert (Hcsh : p' + 1 <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= p').
{ pose proof (fsw_ablock_off_shadow B ly S W (unpoison U mem) md _ _ HAR0 HinT p' ltac:(rewrite RqT; unfold HEAD in *; lia)) as NS.
  lia. }
unfold YG0d.cfg_at, w64.
refine (pv_disp (fx := fx) (rc := rc) B (STK_parse_value (2 - k) + (ot - spZ regs)) ot ([(v, v + 56)] ++ FS_PSTAT_FP) ly S W
  (unpoison U mem) md
  [(0, pos)] ly2 S3 U W2 (mkst regs2 (Z_to_bv 64 0x830d4) mem2 (seg_rom tfibsegs)) md2 0 v q p' (text + len) 123 _
  eq_refl R19 R20 R23 Hv1 ltac:(lia) Hv8 Hvsh ltac:(lia) Bq8 ltac:(lia) ltac:(rewrite EL4; lia) ltac:(rewrite EH4; lia)
  ltac:(unfold HEAD in *; lia) ltac:(unfold HEAD in *; lia) ltac:(unfold HEAD in *; lia) ltac:(unfold HEAD in *; lia)
  ltac:(unfold HEAD in *; lia) Hcsh (or_intror eq_refl) Vq0 Vq8 Vc RAc RAv HVW2
  (fun a0 Ha0 => pv_v_awr _ _ ly S U W mem md _ ly2 S3 W2 _ md2 _ v _ _ a0 HJ4 HARU0 HPO Ha0) HJ4 HARU4 _ _).
{ intros E. discriminate E. }
intros _ ms' mdx' Hms' C10r C11r C12r C1r CK HJd HARUd KEEPd.
change (ms_regs (mkst regs2 (Z_to_bv 64 0x830d4) mem2 (seg_rom tfibsegs))) with regs2 in CK.
change (ms_mem (mkst regs2 (Z_to_bv 64 0x830d4) mem2 (seg_rom tfibsegs))) with mem2 in KEEPd.
set (regsC := ms_regs ms') in *. set (memC := ms_mem ms') in *.
assert (KC : forall a0, mrestrict (w_H W2) memC (Z_to_bv 64 a0) = mrestrict (w_H W2) mem2 (Z_to_bv 64 a0))
  by (intros a0; apply KEEPd).
assert (Csp : spZ regsC = sp1) by (unfold spZ; rewrite (CK 2%bv ltac:(pv_inK)), R2; apply wz; lia).
assert (C3' : YK11.getr regsC 3%bv = w64 (as_gp B)) by (rewrite (CK 3%bv ltac:(pv_inK)), R3; exact Hgp).
assert (C4' : YK11.getr regsC 4%bv = w64 (as_tp B)) by (rewrite (CK 4%bv ltac:(pv_inK)), R4; exact Htp).
(* the two chains at parse_items' entry *)
set (rdC := aview tfibsegs (w_H W2) (unpoison U memC)). set (rd0 := aview tfibsegs (w_H W) (unpoison U mem)).
assert (BYT : forall b, spZ regs <= b < ly_top ly -> ~ (q <= b < q + 8) -> rdC b = rd0 b).
{ intros b Hb Hq. subst rdC rd0.
  rewrite (fsw_aview_unpoison_high B ly2 S3 U W2 memC mdx' b HARUd) by lia.
  rewrite (fsw_aview_unpoison_high B ly S U W mem md b HARU0) by lia.
  rewrite (pv_aview_eq2 (w_H W2) (w_H W2) mem2 memC b (KC b)).
  destruct (Z_lt_le_dec b ot) as [Hbo|Hbo].
  - unfold aview. rewrite (proj1 (SKS b ltac:(lia) Hq)). reflexivity.
  - rewrite <- (fsw_aview_unpoison_high B ly2 S3 U W2 mem2 md2 b HARU4) by lia.
    rewrite <- (fsw_aview_unpoison_high B ly S U W mem md b HARU0) by lia.
    apply JHI4; lia. }
assert (SVC : pv_saved_ok (mrestrict (w_H W2) memC) (spZ regs) regs).
{ apply (pv_saved_mb (mrestrict (w_H W2) mem2)); [|exact SV2]. intros a0 Ha0. exact (pv_mb_of_mr _ _ _ _ a0 (KC a0)). }
pose proof (SVC 0%nat ltac:(lia)) as V0. pose proof (SVC 1%nat ltac:(lia)) as V1.
cbn [Z.of_nat nth pv_saved pv_extra0 firstn tl] in V0, V1.
replace (spZ regs - 8 * (0 + 1)) with (spZ regs - 8) in V0 by lia.
replace (spZ regs - 8 * (1 + 1)) with (spZ regs - 16) in V1 by lia.
assert (W8 : rdword rdC (spZ regs - 8) = Some (raZ regs)).
{ subst rdC. rewrite (pv_rdword_U B ly2 S3 U W2 memC mdx' _ HARUd) by lia.
  exact (YF0x.val_mem_rdword (w_H W2) memC _ _ (u64_range _) V0). }
assert (W16 : rdword rdC (spZ regs - 16) = Some (s0Z regs)).
{ subst rdC. rewrite (pv_rdword_U B ly2 S3 U W2 memC mdx' _ HARUd) by lia.
  exact (YF0x.val_mem_rdword (w_H W2) memC _ _ (u64_range _) V1). }
assert (QINC : PjIn.pj_in_ok tfibsegs (mrestrict (w_H W2) memC) q text len p' (Z.of_nat k) tb).
{ apply (pv_eqon_in (mrestrict (w_H W2) mem2) _ q text len p' (Z.of_nat k) tb); [| |exact QIN2];
    intros a0 Ha0; apply KC. }
assert (Hold : forall w, rdword rd0 q = Some w -> 4096 <= w < alloc_ceiling).
{ intros w Hw. subst rd0. rewrite (pv_rdword_U B ly S U W mem md _ HARU0) in Hw by lia.
  pose proof HIN as (HB0 & _).
  assert (U64 : PjStruct.pj_u64 tfibsegs (mrestrict (w_H W) mem) q p) by (split; [lia | exact HB0]).
  assert (Hp64 : 0 <= p < 2 ^ 64) by lia.
  rewrite (YF0x.val_mem_rdword (w_H W) mem q p Hp64 (fsw_pj_u64_val _ _ q p U64)) in Hw.
  injection Hw as <-. unfold HEAD in *. lia. }
assert (Hnew : exists w', rdword rdC q = Some w' /\ 4096 <= w' < alloc_ceiling).
{ exists p'. split; [|unfold HEAD in *; lia]. subst rdC. rewrite (pv_rdword_U B ly2 S3 U W2 memC mdx' _ HARUd) by lia.
  pose proof QINC as (HB0 & _).
  assert (U64 : PjStruct.pj_u64 tfibsegs (mrestrict (w_H W2) memC) q p') by (split; [lia | exact HB0]).
  assert (Hp64 : 0 <= p' < 2 ^ 64) by lia.
  exact (YF0x.val_mem_rdword (w_H W2) memC q p' Hp64 (fsw_pj_u64_val _ _ q p' U64)). }
assert (Hk0 : q = spZ regs + 8 -> exists w, rdword rdC (spZ regs) = Some w /\ 0 <= w).
{ intros Eq. apply pv_rdword_some. intros i Hi.
  change (rdC (spZ regs + i) <> None).
  rewrite (BYT (spZ regs + i) ltac:(lia) ltac:(lia)). subst rd0.
  rewrite (fsw_aview_unpoison_high B ly S U W mem md _ HARU0) by lia.
  apply aview_some_of_apresent. apply Hpres. lia. }
destruct (pv_call_chains ly ly2 rd0 rdC (spZ regs) (s0Z regs) (raZ regs) ch q sp1 HCHe HCHQ ET4 ltac:(lia) ltac:(lia)
  ltac:(lia) Hsp8 Bq8 ltac:(lia) BYT W8 W16 Hra4 Hold Hnew Hk0) as (HCH0 & HCHq).
clear HCHQ Hcsh Hvsh.
assert (Es0C : s0Z regsC = spZ regs) by (unfold s0Z; rewrite (CK 8%bv ltac:(pv_inK)), R8; apply wz; lia).
(* parse_items' other premises at its entry *)
assert (HWINC : rd_win tfibsegs regsC ly2 W2 memC q ot).
{ pose proof HJd as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & JPd & _).
  unfold rd_win. rewrite Csp. split; [lia|]. split; [lia|]. split; [exact Hw3|]. split; [rewrite ET4; exact Hw4|].
  intros a0 Ha0. apply (fsw_apresent_unpoison B ly2 S3 U W2 memC mdx' a0 HARUd); [lia|]. apply JPd. lia. }
assert (HTXC : rd_text tfibsegs B ly2 S3 W2 memC text len tcap).
{ pose proof QTX2 as (T1 & (T2 & T3 & T4 & T5) & T6). split; [exact T1|]. split; [|exact T6].
  split; [exact T2|]. split; [exact T3|]. split; [exact T4|].
  apply (pv_val_mb (mrestrict (w_H W2) mem2)); [|exact T5]. intros i Hi. apply pv_mb_of_mr. apply KC. }
assert (HGC : fs_glob tfibsegs W2 memC live peak cnt fail).
{ apply (pv_glob_eqon W2 W2 mem2 memC); [|exact QG2]. intros a0 Ha0. apply KC. }
assert (HROC : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W2) memC)).
{ apply (pv_ro_keep B (aview tfibsegs (w_H W2) mem2)); [exact QRO2|]. intros a0 Ha0. apply pv_aview_eq2. apply KC. }
assert (Ebb : blocks_bytes S3 = blocks_bytes S) by (rewrite (pv_bb B ly2 S3), AB, <- (pv_bb B ly S); reflexivity).
assert (HPOC : pobj tfibsegs B ly2 S3 W2 memC v).
{ split.
  - destruct (pv_v_place _ _ ly S U W mem md _ ly2 S3 W2 _ mdx' _ v HJd HARU0 HPO)
      as [(b & m & Hb & Hbc & H1 & H2)|(cid & pos' & Hf & Hc & EF & H8 & H1 & H2)].
    + right. split; [exists b, m; split; [exact Hbc | lia]|]. split; [exact Hv8|].
      exact (pv_ra_v _ _ ly S U W mem md _ ly2 S3 U W2 memC mdx' _ v HJd HARU0 HARUd FH FH4 HPO).
    + left. split; [|split; [exact Hv8 | exact (pv_ra_v _ _ ly S U W mem md _ ly2 S3 U W2 memC mdx' _ v HJd HARU0 HARUd FH FH4 HPO)]].
      exists cid, pos'. split; [rewrite Hfrs4; right; exact Hf|]. split; [exact Hc|]. rewrite EF. split; [exact H8|]. lia.
  - intros i Hi. apply (proj1 (pv_wr_keep _ _ (v + i) (KC (v + i)))). exact (HVW2 i Hi). }
assert (HZC : PjStruct.pj_zero tfibsegs (mrestrict (w_H W2) memC) v).
{ apply (pv_eqon_zero (mrestrict (w_H W) mem)); [|exact HZ]. intros a0 Ha0. rewrite (KC a0). exact (VK a0 Ha0). }
rewrite Hms'.
refine (pv_objcall B k (parse_items_holds Hk1) (STK_parse_value (2 - k) + (ot - spZ regs)) ot ([(v, v + 56)] ++ FS_PSTAT_FP)
  ly S U W mem md ly2 S S3 W2 regsC memC mdx' pos q sp1 v text len p' tb tcap ms pr rest live peak cnt fail _
  Hk1 Csp C10r C11r C12r C1r C3' C4' Hsp16 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite Es0C; exact HCH0)
  (HCHq sp1 ltac:(lia) ltac:(lia)) HROC FH4 Hfrs4 HFRL QINC HWINC HTXC Hrest' Hvals Hstrs Hwf Hdep HPOC HZC
  ltac:(left; lia) Hvtx HGC Hquiet Hsz Hlive ltac:(change (PjTree.JObj ms) with u; lia) ltac:(rewrite Ebb; exact Hbb)
  HJd HARUd _
  (fun a0 Ha0 => match Ha0 with ex_intro _ r0 (conj Hr Har) => ex_intro _ r0 (conj (in_or_app _ _ _ (or_intror Hr)) Har) end)
  _).
{ intros a0 Ha0. assert (HFP : inFP ([(v, v + 56)] ++ FS_PSTAT_FP) a0) by (exists (v, v + 56); split; [left; reflexivity | cbn; lia]).
  destruct (pv_v_place _ _ ly S U W mem md _ ly2 S3 W2 _ mdx' _ v HJd HARU0 HPO)
    as [(b & m & Hb & Hbc & H1 & H2)|(cid & pos' & Hf & Hc & EF & H8 & H1 & H2)].
  - left. split; [exact HFP|]. exists b, m. split; [exact Hbc | unfold HEAD in H1; lia].
  - right. split; [exact HFP|]. exists cid, pos'. split; [exact Hf|]. unfold in_zr, frame_rng. cbn [fst snd]. lia. }
intros ly3 S6 W3 regs3 mem3 md3 D Da HDa HJ5 HARU5 HJc5 OK5 PO5 HP5 Q10 QIN3 QWK3 QPERM QT QSUM QLEN QPO QTX QGL.
clear Hvtx.
pose proof HJ5 as (_ & Hly5 & _ & _ & _ & Hfrs5 & _). cbn [app] in Hfrs5.
destruct (pv_ly_F _ ly ly3 0 pos Hly5) as (EF5 & EFL5).
pose proof (ARU_AR tfibsegs B ly3 S6 _ W3 mem3 md3 HARU5) as HAR5.
assert (Hin05 : In (0, pos) (frames S6)) by (rewrite Hfrs5; left; reflexivity).
assert (SV3 : pv_saved_ok (mrestrict (w_H W3) mem3) (spZ regs) regs).
{ apply (pv_saved_mb (mrestrict (w_H W2) memC)); [|exact SVC]. intros a0 Ha0. exact (proj1 (QWK3 a0 ltac:(lia) ltac:(lia))). }
assert (FL3 : val_mem tfibsegs (mrestrict (w_H W3) mem3) (frame_addr ly3 0 pos + 56) 8 (flag_addr ly3 0 pos)).
{ rewrite EF5, EFL5. apply (pv_val_mb (mrestrict (w_H W2) mem2)); [|exact FL2].
  intros i Hi. cbn in Hi. apply pv_mb_of_mr.
  assert (HFi : frame_addr ly2 0 pos <= frame_addr ly 0 pos + 56 + i < frame_addr ly2 0 pos + fs_frame_bytes 0)
    by (rewrite EF4; change (fs_frame_bytes 0) with 64; lia).
  assert (NFP : ~ inFP ([(v, v + 56)] ++ FS_PSTAT_FP) (frame_addr ly 0 pos + 56 + i)).
  { intros (r0 & Hr & Har). apply in_app_or in Hr as [Hr|Hr].
    + cbn [In] in Hr. destruct Hr as [<-|[]]. cbn [fst snd] in Har. exact (VF _ Har ltac:(lia)).
    + exact (frm_img tfibsegs B LAWS ly2 S3 W2 (unpoison U mem2) md2 0 pos _ HAR4 Hin04 HFi
        (pv_pstat_img _ (ex_intro _ r0 (conj Hr Har)))). }
  rewrite (proj2 (fsw_journal_kept_byte B _ _ _ ly2 S3 U W2 memC mdx' ly3 S6 _ W3 mem3 md3 _ _ HJc5 HARUd OK5 PO5
    (or_intror (ex_intro _ 0 (ex_intro _ pos (conj Hin04 HFi)))) NFP)).
  apply KC. }
assert (R10' : YK11.getr regs3 10%bv = Z_to_bv 64 0) by exact Q10.
unfold YG0d.cfg_at, w64.
eapply SRr_mono.
{ refine (pv_epi (fx := fx) (rc := rc) B ML ASF FFL (STK_parse_value (2 - k) + (ot - spZ regs)) ot
    ([(v, v + 56)] ++ FS_PSTAT_FP) ly S U W mem md ly3 S6 (U ++ rd_heads Da) W3 regs regs3 mem3 md3 pos (spZ regs) 0
    (rd_ev (PjRoundTrip.ttrace u)) 0x8327c 10%bv []
    (pv_postQ ly S W regs mem q ot v text len p tb tcap u pr ws live peak cnt fail D)
    (or_intror (conj eq_refl eq_refl)) Hin05 _ _ _ _ R10' _ _ eq_refl Hret ltac:(lia) Hal16 ltac:(lia) ltac:(lia) SV3 FL3
    HJ5 HARU5 _).
  - rewrite (fsw_pres _ _ 8%bv HP5 ltac:(pv_cs)), (CK 8%bv ltac:(pv_inK)). exact R8.
  - rewrite EF5, (fsw_pres _ _ 18%bv HP5 ltac:(pv_cs)), (CK 18%bv ltac:(pv_inK)). exact R18.
  - rewrite EF5, (fsw_pres _ _ 27%bv HP5 ltac:(pv_cs)), (CK 27%bv ltac:(pv_inK)). exact R27.
  - rewrite EF5, (fsw_pres _ _ 26%bv HP5 ltac:(pv_cs)), (CK 26%bv ltac:(pv_inK)). exact R26.
  - rewrite (fsw_pres _ _ 3%bv HP5 ltac:(pv_cs)), (CK 3%bv ltac:(pv_inK)). exact R3.
  - rewrite (fsw_pres _ _ 4%bv HP5 ltac:(pv_cs)), (CK 4%bv ltac:(pv_inK)). exact R4.
  - intros mat regsf memf Hr10 KEEPf.
    destruct (pv_pe ly3 S6 W3 _ md3 pos (frames S) HAR5 Hfrs5) as (PEhi & PEimg & PEblk & PEfrm).
    assert (KF : forall a0, 0 <= a0 < 2 ^ 64 -> ~ pe_wr (frame_addr ly3 0 pos) (flag_addr ly3 0 pos) a0 ->
      mrestrict (w_H W3) memf (Z_to_bv 64 a0) = mrestrict (w_H W3) mem3 (Z_to_bv 64 a0))
      by (intros a0 Ha0 Hn; apply KEEPf; rewrite wz by lia; exact Hn).
    pose proof QTX as (QT1 & (HinT6 & QT3 & QT4 & QT5) & QT6).
    assert (VPE : forall x, v <= x < v + 56 -> ~ pe_wr (frame_addr ly3 0 pos) (flag_addr ly3 0 pos) x /\
      ~ pe_wr (frame_addr ly3 0 pos) (flag_addr ly3 0 pos) (shadow_of_addr SHADOW_OFF x)).
    { intros x Hx. destruct (pv_v_place _ _ ly S U W mem md _ ly3 S6 W3 _ md3 _ v HJ5 HARU0 HPO)
        as [(b & m & Hb & Hb6 & H1 & H2)|(cid & pos' & Hf & Hc & EF & H8 & H1 & H2)].
      - exact (PEblk b m x Hb6 ltac:(unfold HEAD in H1; lia)).
      - exact (PEfrm cid pos' x Hf ltac:(rewrite EF; lia)). }
    pose proof QT as (QTn & QTb & QTi).
    assert (DPE : forall a0 k0 x, In (a0, k0) D -> a0 - HEAD <= x < a0 + k0 ->
      ~ pe_wr (frame_addr ly3 0 pos) (flag_addr ly3 0 pos) x).
    { intros a0 k0 x Hd Hx. destruct (QTb a0 k0 Hd) as (Hb & _ & Hkk0 & _).
      pose proof (req_size_pos (k0 + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hr2).
      exact (proj1 (PEblk _ _ x Hb ltac:(unfold HEAD in *; lia))). }
    unfold pv_postQ.
    split; [exact Hr10|].
    split.
    { apply (pv_eqon_in (mrestrict (w_H W3) mem3) _ q text len _ (Z.of_nat k) tb); [| |exact QIN3].
      - intros a0 Ha0. apply KF; [lia|]. apply PEhi. lia.
      - intros a0 Ha0. apply KF; [lia|].
        exact (proj1 (PEblk _ _ a0 HinT6 ltac:(rewrite RqT; unfold HEAD in *; lia))). }
    split.
    { intros a0 Ha0 Hq.
      assert (E4 : mrestrict (w_H W3) memf (Z_to_bv 64 a0) = mrestrict (w_H W3) mem3 (Z_to_bv 64 a0))
        by exact (KF a0 ltac:(lia) (PEhi a0 ltac:(lia))).
      destruct (QWK3 a0 ltac:(lia) Hq) as (M3 & Wr3).
      destruct (SKS a0 ltac:(lia) ltac:(lia)) as (M2 & Wr2).
      split.
      - rewrite (pv_mb_of_mr _ _ _ _ a0 E4), M3, (pv_mb_of_mr _ _ _ _ a0 (KC a0)). exact M2.
      - rewrite Wr2, (pv_wr_keep _ _ a0 (KC a0)), Wr3. apply pv_wr_keep. exact E4. }
    split.
    { rewrite pv_ablocks_free. rewrite AB in QPERM. exact QPERM. }
    split.
    { split; [|split].
      - eapply (PjStruct.pj_node_frame tfibsegs); [exact QTn | intros a0 k0 H; exact H |].
        intros x Hx. apply KEEPf. destruct Hx as [Hx|(b & Hb & Hx)].
        + exact (proj1 (VPE _ Hx)).
        + destruct b as [a0 k0]. unfold PjStruct.pj_holds in Hx. cbn [fst snd] in Hx.
          exact (DPE a0 k0 (bv_unsigned x) Hb ltac:(unfold HEAD; lia)).
      - intros a0 k0 Hd. destruct (QTb a0 k0 Hd) as (Hb & Hal & Hkk0 & Hv).
        split; [rewrite pv_ablocks_free; exact Hb|]. split; [exact Hal|]. split; [exact Hkk0|].
        destruct (fsw_ablock_low B ly3 S6 W3 _ md3 _ _ HAR5 Hb) as (Ab1 & Ab2 & Ab3).
        apply (pv_val_mb (mrestrict (w_H W3) mem3)); [|exact Hv]. intros i Hi. cbn in Hi. apply pv_mb_of_mr.
        apply KF; [unfold HEAD in *; lia|]. exact (DPE a0 k0 (a0 - HEAD + i) Hd ltac:(unfold HEAD; lia)).
      - exact QTi. }
    split; [exact QSUM|].
    split; [exact QLEN|].
    split.
    { pose proof QPO as (_ & QPW).
      assert (RA3 : range_addressable (aview tfibsegs (w_H W3) mem3) SHADOW_OFF v 56)
        by (destruct QPO as [[(_ & _ & R)|(_ & _ & R)] _]; exact R).
      assert (RAf : range_addressable (aview tfibsegs (w_H W3) memf) SHADOW_OFF v 56).
      { apply (pv_eqon_RA (w_H W3) (w_H W3) mem3 memf v 56); [|exact RA3]. intros a0 Ha0.
        apply KF; [unfold shadow_of_addr, SHADOW_OFF; Z.div_mod_to_equations; lia | exact (proj2 (VPE a0 Ha0))]. }
      split.
      - destruct (pv_v_place _ _ ly S U W mem md _ ly3 S6 W3 _ md3 _ v HJ5 HARU0 HPO)
          as [(b & m & Hb & Hb6 & H1 & H2)|(cid & pos' & Hf & Hc & EF & H8 & H1 & H2)].
        + right. split; [exists b, m; split; [rewrite pv_ablocks_free; exact Hb6 | lia]|]. split; [exact Hv8 | exact RAf].
        + left. split; [|split; [exact Hv8 | exact RAf]]. exists cid, pos'.
          split; [rewrite (pv_frames_free S6 pos (frames S) Hfrs5); exact Hf|]. split; [exact Hc|]. rewrite EF.
          split; [exact H8|]. lia.
      - intros i Hi. apply (proj1 (pv_wr_keep _ _ (v + i) (KF (v + i) ltac:(lia) (proj1 (VPE (v + i) ltac:(lia)))))).
        exact (QPW i Hi). }
    split.
    { split; [exact QT1|]. split; [|exact QT6].
      split; [rewrite pv_ablocks_free; exact HinT6|]. split; [exact QT3|]. split; [exact QT4|].
      apply (pv_val_mb (mrestrict (w_H W3) mem3)); [|exact QT5]. intros i Hi. cbn in Hi. apply pv_mb_of_mr.
      apply KF; [unfold HEAD in *; lia|].
      exact (proj1 (PEblk _ _ (text - HEAD + i) HinT6 ltac:(rewrite RqT; unfold HEAD in *; lia))). }
    destruct QGL as (peak' & Hpk & QG3). exists peak'. split; [exact Hpk|].
    apply (pv_glob_eqon W3 W3 mem3 memf); [|exact QG3].
    intros a0 Ha0. pose proof (pv_pstat_img a0 Ha0) as Hi. pose proof (fs_segs_img a0 Hi) as Hlo.
    apply KF; [unfold FS_IMG_END in Hlo; lia | exact (PEimg a0 Hi)]. }
intros W' c' _ HF. unfold pv_post. exists D, Da. split; [exact HDa | exact HF].
Qed.

(* ================= parse_value_spec k: one front (pv_A), then the string arm or the object arm =================
   The root is a string or an object (FS_DOC_STRS (i)), so the byte after ws is a quote or a brace and the dispatch
   takes 0x83184 or 0x83174 (FSW_parse_value.pv_disp); the literal and number arms are not reached. *)
Theorem parse_value_holds : @parse_value_spec fx rc SK tfibsegs B k.
Proof.
intros ly S U W regs mem md ch q ot v text len p tb tcap u pr ws rest live peak cnt fail tr wt Hk' HPRE FH HFRL H10 H11
  HIN HWIN HCHQ HTX Hrest Hws Hvals Hstrs Hwf Hdep HPO HZ Hvst Hvtx HG Hquiet Hsz Hlive Hnev Hbb.
assert (Hq8 : spZ regs + 8 <= q) by (destruct HCHQ as [(E & _)|(E & _)]; lia).
destruct (pv_u_cases u Hvals) as [(s & Eu) | (ms & Eu)]; subst u.
- pose proof (pv_str_plain s Hstrs) as Hplain.
  assert (Ewt : wt = 34 :: s ++ [34]) by exact (pv_wt_str s pr (Z.of_nat k) Hplain).
  rewrite Ewt in Hrest.
  apply (pv_A ly S U W regs mem md ch q ot v text len p tb tcap live peak cnt fail ws (34 :: s ++ [34]) rest 34 _
    HPRE FH HFRL H10 H11 HIN HWIN Hq8 HTX Hrest Hws eq_refl (or_introl eq_refl) HPO HG).
  intros ly2 S3 W2 regs2 mem2 md2 pos HJ4 HARU4 Hnin AB R2 R3 R4 R8 R9 R18 R19 R20 R23 R26 R27 QIN2 QTX2 QG2 QRO2 SV2 FL2
    SKS VK.
  eapply SRr_mono.
  + exact (pv_strarm ly S U W regs mem md ch q ot v text len p tb tcap s pr ws rest live peak cnt fail ly2 S3 W2 regs2
      mem2 md2 pos HPRE FH HIN HWIN HCHQ HTX Hrest Hplain HPO HZ Hvtx Hquiet Hsz Hlive Hnev Hbb HJ4 HARU4 Hnin AB R2 R3 R4
      R8 R9 R18 R19 R20 R23 R26 R27 QIN2 QTX2 QG2 QRO2 SV2 FL2 SKS VK).
  + intros W' c' _ HF. exact HF.
- destruct (pv_wt_obj ms pr (Z.of_nat k)) as (r & Ewt).
  assert (Hhd : hd_error wt = Some 123)
    by (change (hd_error (concat (WriterValue.wvpieces (PjTree.JObj ms) pr (Z.of_nat k))) = Some 123); rewrite Ewt;
        reflexivity).
  apply (pv_A ly S U W regs mem md ch q ot v text len p tb tcap live peak cnt fail ws wt rest 123 _
    HPRE FH HFRL H10 H11 HIN HWIN Hq8 HTX Hrest Hws Hhd (or_intror eq_refl) HPO HG).
  intros ly2 S3 W2 regs2 mem2 md2 pos HJ4 HARU4 Hnin AB R2 R3 R4 R8 R9 R18 R19 R20 R23 R26 R27 QIN2 QTX2 QG2 QRO2 SV2 FL2
    SKS VK.
  eapply SRr_mono.
  + exact (pv_objarm ly S U W regs mem md ch q ot v text len p tb tcap ms pr ws rest live peak cnt fail ly2 S3 W2 regs2
      mem2 md2 pos HPRE FH HFRL HIN HWIN HCHQ HTX Hrest Hvals Hstrs Hwf Hdep HPO HZ Hvtx Hquiet Hsz Hlive Hnev Hbb HJ4 HARU4
      Hnin AB R2 R3 R4 R8 R9 R18 R19 R20 R23 R26 R27 QIN2 QTX2 QG2 QRO2 SV2 FL2 SKS VK).
  + intros W' c' _ HF. exact HF.
Qed.
End H.

(* the theorem's elaborated shape, every implicit argument explicit (the sink head is the binder SK, never an inferred
   instance; the image is B's tfibsegs): the lane's fixed shape (k <= 2, FsShadowSyms, the three callee specs, parse_items
   only when k <= 1), then the runtime facts the walk's own steps use, as named Section hypotheses: the image facts (the
   statics across the grant), the use-after-return flag's GOT word and cell, the class-0 fake-frame call, and the
   fake-frame kit's unit laws (errno_low, ML, SMP for the grant; ML, ASF, FFL for the flag release) *)
Check (@parse_value_holds : forall (fx : YK11.FPState) (rc : YM05.RunCeil) (SK : YI16.sink_head) (B : asyms) (k : nat),
  (k <= 2)%nat -> FsShadowSyms B -> @skip_ws_spec fx rc SK tfibsegs B -> @parse_string_spec fx rc SK tfibsegs B ->
  ((k <= 1)%nat -> @parse_items_spec fx rc SK tfibsegs B k) ->
  fs_img_facts tfibsegs B -> as_got_uar B = fs_D_GOT_uar -> as_uar_cell B = fs_D_uar_cell ->
  pc_stack_malloc (as_code B) 0 = PC_stack_malloc_0 /\ FSupoisonU.astack_malloc_realizesU tfibsegs B 0 ->
  api_env tfibsegs B -> model_laws (as_universe B) -> stack_malloc_progressP B -> astack_free_law tfibsegs B ->
  frame_flag_lawP tfibsegs B ->
  @parse_value_spec fx rc SK tfibsegs B k).
Print Assumptions parse_value_holds.
