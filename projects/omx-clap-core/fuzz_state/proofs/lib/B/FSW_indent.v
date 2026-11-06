(* indent 0x86368 (preset_file.c:514-523) on fs.asan-ubsan (image B, sha256 5ac5ce0954f8...): Theorem indent_proof :
   @indent_spec fx rc SK B tfibsegs (S0's statement lib/B/FSH_Fn_writer.v indent_spec, no CTX, with the head-in-U
   premise: a working branch adfa7850046 over a working branch bddf781b317), the callee put 0x8449c through put_spec
   (same file) as a Section hypothesis. SK stays the Section's Context and is passed with `@` (a build-B instantiation
   passes FSH_Base.fsB_sink_head). 28 words, disassembled from B itself (capstone over the pinned fuzz_state.asan-ubsan):
     0x86368 addi sp, sp, -32; sd ra, 24(sp); sd s0, 16(sp); sd s1, 8(sp); sd s2, 0(sp)
     0x8637c beqz a1, 0x863c0                         (pretty = 0: straight to the epilogue)
     0x86380 mv s0, a2; mv s1, a0; auipc a0 / addi a1 -> a1 = 0x21040 ("\n"); li a2, 1; mv a0, s1
     0x86398 jal put 0x8449c                          (returns to 0x8639c)
     0x8639c blez s0, 0x863c0                         (depth <= 0, signed 64-bit)
     0x863a0 auipc a0 / addi s2 -> s2 = 0x21300 ("  ")
     0x863a8 li a2, 2; mv a0, s1; mv a1, s2
     0x863b4 jal put 0x8449c                          (returns to 0x863b8)
     0x863b8 addiw s0, s0, -1; bnez s0, 0x863a8
     0x863c0 ld ra / s0 / s1 / s2; addi sp, sp, 32; ret
   UBSan: B is the ASan + UBSan build, but indent carries no UBSan check. Its only calls are the two `jal` to put
   (0x86398, 0x863b4); no instruction in [0x86368, 0x863d8) transfers to a __ubsan_handle_* entry, and the loop's
   `addiw s0, s0, -1` is not overflow-checked (s0 >= 1 there). So no UBSan handler branch exists to rule out.
   Uninstrumented for ASan too: no GOT load, no shadow check.
   The two strings are FS_RO_STRS entries (lib/B/FSH_Rt.v, measured in B at the same addresses as in A), so fs_img_facts
   gives their bytes. At both put calls s0 holds depth (or what is left of it), a value below alloc_ceiling or (negative
   depth) at least ly_top - 16, so put's frame chain is [] (put's achain premise at s0, discharged in ind_call).
   Section hypotheses: IMG : fs_img_facts tfibsegs B (lib/B/FSH_Rt.v); PUT : put_spec B tfibsegs.
   The buffer's head in U (cap <> 0 -> In (buf - HEAD, HEAD) U), put's premise twice, is carried by the invariant iRI
   between puts: indent's own premise gives it at entry, and each put's uswap keeps U (arm 1, where cap <> 0 already
   held before the call, since arm 1 keeps buf and a zero-cap buffer is at 0, below every block) or appends the new head
   (arms 2 and 3).
   Resume after each put: the kit's FSW_K3.fsw_after_callFPU_win (the resumed frame [sp - 32, sp) anywhere inside
   indent's journal window, which ends at the raised top ot; the frame's chunks read on the call's memory, carried by
   put's keep clause wkeep). No local after-call lemma.
   The post's journal count k = wevk cap st' (cap-aware): the journal at each state after the pieces P is kept at
   k <= wevk cap (iw P), each put adding its own wevk (put's entry cap); iw_wevk_step adds them up. bswap is the realloc
   form (C1 ++ new :: C2), composed by bswap_trans through mid_unique.
   Route: indent_arm0 (pretty = 0), ind_arm1 (entry and the newline put), ind_r80 (blez s0), ind_loop (the two-space
   puts, by induction), ind_call (one put through PUT), ind_ret (the return), over the invariant iRI between puts.
   Template: the image-A proof lib/A/FSW_indent.v (a working branch a6f109640fd), every address replaced by
   B's own (lib/B/FSH_Base.v, lib/B/FSPstat.v, lib/B/YB1w.v, the disassembly above).
   Rule 24 (record (internal path): proof-index indent, 14 named / 15
   by address / 4 related / 28 lemma(s), an earlier delivery 6 named; git grep by name and by B entry 0x86368 over main, ossv/recipes,
   ossv/candidates, release/pau-projects-recipes and the named cold refs, 2026-10-29T04:18:29Z; CONFIRM by a Theorem Labs lane
   2026-10-29T04:39:15Z): no proof of indent against S0's lib/B spec on any searched ref; 211ff3e9df0
   lib/B/Prog/indent*.v and a working branch 0603c9ef lib/B/Prog/indent.v are templates only; written over S0 and
   the lib/B walk kit FSW_K / FSW_K3 / FSW_ret / FSW_rd (U form; a working branch 65632947036). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v FSH_Base FSH_Rt FSPstat FSH_Fn_writer FSW_K FSW_K3 FSW_ret FSW_rd FSW_writer_tbl FSW_writer_kit.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterApp WriterValue.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ================= the writer model across several puts (lib/Prog/WriterApp.v) ================= *)
(* put_spec states its model from a fresh call log; every field but the log agrees with put1 on the running state *)
Lemma put1_fields : forall (st : WriterApp.wst) b,
  let st' := WriterApp.put1 (WriterApp.mkW (WriterApp.w_failed st) (WriterApp.w_text st) (WriterApp.w_cap st)
               (WriterApp.w_cnt st) (WriterApp.w_fail st) []) b in
  WriterApp.w_failed st' = WriterApp.w_failed (WriterApp.put1 st b) /\
  WriterApp.w_text st' = WriterApp.w_text (WriterApp.put1 st b) /\
  WriterApp.w_cap st' = WriterApp.w_cap (WriterApp.put1 st b) /\
  WriterApp.w_cnt st' = WriterApp.w_cnt (WriterApp.put1 st b) /\
  WriterApp.w_fail st' = WriterApp.w_fail (WriterApp.put1 st b).
Proof.
intros [f t c n fl cs] b. cbn zeta. unfold WriterApp.put1. cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap
  WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls].
destruct (negb (f =? 0)); [repeat split; reflexivity|].
destruct (_ <=? c); [repeat split; reflexivity|]. destruct (n =? fl); repeat split; reflexivity.
Qed.
Lemma put1_text_le : forall st b,
  Z.of_nat (length (WriterApp.w_text (WriterApp.put1 st b))) <=
  Z.of_nat (length (WriterApp.w_text st)) + Z.of_nat (length b).
Proof.
intros [f t c n fl cs] b. unfold WriterApp.put1. cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap
  WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls].
destruct (negb (f =? 0)); [cbn; lia|].
destruct (_ <=? c); [cbn; rewrite length_app; lia|]. destruct (n =? fl); cbn; [lia | rewrite length_app; lia].
Qed.
Lemma putN_text_le : forall P st,
  Z.of_nat (length (WriterApp.w_text (WriterApp.putN st P))) <=
  Z.of_nat (length (WriterApp.w_text st)) + Z.of_nat (length (concat P)).
Proof.
induction P as [|b P IH]; intros st; [cbn; lia|].
rewrite WriterApp.putN_cons. pose proof (IH (WriterApp.put1 st b)) as H. pose proof (put1_text_le st b) as H1.
cbn [concat]. rewrite length_app. lia.
Qed.
Lemma dbl_ge : forall fuel c need, 0 <= c -> c <= WriterSpec.dbl fuel c need.
Proof.
induction fuel as [|f IH]; intros c need Hc; cbn [WriterSpec.dbl]; [lia|].
destruct (need <=? c); [lia|]. pose proof (IH (2 * c) need ltac:(lia)). lia.
Qed.
Lemma put1_cap_ge : forall st b, 0 <= WriterApp.w_cap st -> WriterApp.w_cap st <= WriterApp.w_cap (WriterApp.put1 st b).
Proof.
intros [f t c n fl cs] b Hc. cbn [WriterApp.w_cap] in Hc. unfold WriterApp.put1. cbn [WriterApp.w_failed WriterApp.w_text
  WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls].
destruct (negb (f =? 0)); [cbn [WriterApp.w_cap]; lia|].
destruct (_ <=? c); [cbn [WriterApp.w_cap]; lia|]. destruct (n =? fl); cbn [WriterApp.w_cap]; [lia|].
unfold WriterSpec.newcap. destruct (c =? 0) eqn:E.
- apply Z.eqb_eq in E. subst c.
  match goal with |- _ <= WriterSpec.dbl _ _ ?nd => pose proof (dbl_ge 64 4096 nd ltac:(lia)) end. lia.
- exact (dbl_ge 64 c _ Hc).
Qed.

(* ---- lists: the one entry a writer call adds is at the end, and no entry repeats ---- *)
Lemma pairwise_dup : forall {T} (R : T -> T -> Prop) X x Y, pairwise R (X ++ x :: Y) -> In x (X ++ Y) -> R x x.
Proof.
intros T R X. induction X as [|z X IH]; intros x Y Hp Hin; cbn in Hp, Hin.
- destruct Hp as [Hf _]. exact (proj1 (Forall_forall _ _) Hf x Hin).
- destruct Hp as [Hf Hp]. destruct Hin as [<- | Hin].
  + apply (proj1 (Forall_forall _ _) Hf). apply in_or_app. right. left. reflexivity.
  + exact (IH x Y Hp Hin).
Qed.
Lemma last_split : forall {T} (Y1 Y2 Z : list T) h, Y1 ++ h :: Y2 = Z ++ [h] -> ~ In h (Y1 ++ Y2) -> Y2 = [] /\ Y1 = Z.
Proof.
intros T Y1 Y2 Z h E Hn. destruct Y2 as [|y Y2] using rev_ind.
- split; [reflexivity|]. exact (proj1 (app_inj_tail _ _ _ _ E)).
- exfalso. rewrite app_comm_cons, app_assoc in E. apply app_inj_tail in E as [_ ->].
  apply Hn. apply in_or_app. right. apply in_or_app. right. left. reflexivity.
Qed.

(* the heads move twice as one move (FSH_Fn_writer.v uswap) *)
Lemma uswap_trans : forall U U1 U2 buf buf1 buf2 cap cap1,
  uswap U U1 buf buf1 cap -> uswap U1 U2 buf1 buf2 cap1 ->
  (forall X Y, U1 = X ++ (buf1 - HEAD, HEAD) :: Y -> ~ In (buf1 - HEAD, HEAD) (X ++ Y)) ->
  (cap1 = 0 -> ~ In (buf1 - HEAD, HEAD) U1) -> (cap1 = 0 -> cap = 0) ->
  uswap U U2 buf buf2 cap.
Proof.
intros U U1 U2 buf buf1 buf2 cap cap1 H1 H2 Hnd Hz Hc0.
destruct H1 as [[-> ->] | [(X1 & X2 & EU & EU1) | (Hc & EU1)]].
{ destruct H2 as [H2 | [H2 | (Hc1 & EU2)]]; [left; exact H2 | right; left; exact H2 | right; right].
  split; [exact (Hc0 Hc1) | exact EU2]. }
- destruct H2 as [[-> ->] | [(Y1 & Y2 & EY & EU2) | (Hc1 & EU2)]].
  + right. left. exists X1, X2. split; [exact EU | exact EU1].
  + rewrite EU1, app_assoc in EY. symmetry in EY.
    destruct (last_split Y1 Y2 (X1 ++ X2) _ EY ltac:(apply (Hnd Y1 Y2); rewrite EU1, app_assoc; exact (eq_sym EY)))
      as [-> ->].
    right. left. exists X1, X2. split; [exact EU | rewrite EU2, <- app_assoc; reflexivity].
  + exfalso. apply (Hz Hc1). rewrite EU1. apply in_or_app. right. apply in_or_app. right. left. reflexivity.
- destruct H2 as [[-> ->] | [(Y1 & Y2 & EY & EU2) | (Hc1 & EU2)]].
  + right. right. split; [exact Hc | exact EU1].
  + rewrite EU1 in EY. symmetry in EY.
    destruct (last_split Y1 Y2 U _ EY ltac:(apply (Hnd Y1 Y2); rewrite EU1; exact (eq_sym EY))) as [-> ->].
    right. right. split; [exact Hc | rewrite EU2; reflexivity].
  + exfalso. apply (Hz Hc1). rewrite EU1. apply in_or_app. right. left. reflexivity.
Qed.

(* an entry that occurs once splits its list one way only *)
Lemma mid_unique : forall {T} (X Y X' Y' : list T) x, X ++ x :: Y = X' ++ x :: Y' -> ~ In x (X ++ Y) ->
  X ++ Y = X' ++ Y'.
Proof.
intros T X. induction X as [|a X IH]; intros Y X' Y' x E Hn; destruct X' as [|b X']; cbn [app] in *.
- injection E as E. exact E.
- injection E as <- E. exfalso. apply Hn. rewrite E. apply in_or_app. right. left. reflexivity.
- injection E as -> E. exfalso. apply Hn. left. reflexivity.
- injection E as <- E. f_equal. apply (IH Y X' Y' x E). intros Hx. apply Hn. right. exact Hx.
Qed.
(* bswap's realloc form keeps every other entry *)
Lemma in_realloc : forall {T} (C1 C2 L : list T) n x, C1 ++ C2 = L -> In x L -> In x (C1 ++ n :: C2).
Proof.
intros T C1 C2 L n x E Hx. rewrite <- E in Hx. apply in_app_or in Hx as [Hx | Hx]; apply in_or_app;
  [left; exact Hx | right; right; exact Hx].
Qed.

(* the writer's buffer block moves twice as one move (FSH_Fn_writer.v bswap: the new block anywhere in the list,
   C1 ++ new :: C2 with C1 ++ C2 the list without the old one) *)
Lemma bswap_trans : forall A A1 A2 buf buf1 buf2 cap cap1 cap2,
  bswap A A1 buf buf1 cap cap1 -> bswap A1 A2 buf1 buf2 cap1 cap2 ->
  (forall X Y, A1 = X ++ (buf1 - HEAD, cap1 + HEAD) :: Y -> ~ In (buf1 - HEAD, cap1 + HEAD) (X ++ Y)) ->
  (cap1 = 0 -> ~ In (buf1 - HEAD, cap1 + HEAD) A1) ->
  bswap A A2 buf buf2 cap cap2.
Proof.
intros A A1 A2 buf buf1 buf2 cap cap1 cap2 H1 H2 Hnd Hz.
destruct H1 as [(-> & -> & ->) | [(Hc & C1 & C2 & EA1 & EC) | (X1 & X2 & C1 & C2 & EA & EA1 & EC)]]; [exact H2|..].
- destruct H2 as [(-> & -> & ->) | [(Hc1 & D1 & D2 & EA2 & ED) | (Y1 & Y2 & D1 & D2 & EY & EA2 & ED)]].
  + right. left. split; [exact Hc|]. exists C1, C2. split; [exact EA1 | exact EC].
  + exfalso. apply (Hz Hc1). rewrite EA1. apply in_or_app. right. left. reflexivity.
  + right. left. split; [exact Hc|]. exists D1, D2. split; [exact EA2|].
    rewrite ED, <- EC. symmetry.
    apply (mid_unique C1 C2 Y1 Y2 (buf1 - HEAD, cap1 + HEAD)); [rewrite <- EA1; exact EY|].
    apply (Hnd C1 C2 EA1).
- destruct H2 as [(-> & -> & ->) | [(Hc1 & D1 & D2 & EA2 & ED) | (Y1 & Y2 & D1 & D2 & EY & EA2 & ED)]].
  + right. right. exists X1, X2, C1, C2. split; [exact EA|]. split; [exact EA1 | exact EC].
  + exfalso. apply (Hz Hc1). rewrite EA1. apply in_or_app. right. left. reflexivity.
  + right. right. exists X1, X2, D1, D2. split; [exact EA|]. split; [exact EA2|].
    rewrite ED, <- EC. symmetry.
    apply (mid_unique C1 C2 Y1 Y2 (buf1 - HEAD, cap1 + HEAD)); [rewrite <- EA1; exact EY|].
    apply (Hnd C1 C2 EA1).
Qed.

Lemma wbudget_kept_trans : forall S S1 S2 f c n f1 c1 n1 f2 c2 n2,
  wbudget_kept S S1 f c n f1 c1 n1 -> wbudget_kept S1 S2 f1 c1 n1 f2 c2 n2 -> wbudget_kept S S2 f c n f2 c2 n2.
Proof. intros. unfold wbudget_kept in *. lia. Qed.

Lemma putN_cap_ge : forall P st, 0 <= WriterApp.w_cap st -> WriterApp.w_cap st <= WriterApp.w_cap (WriterApp.putN st P).
Proof.
induction P as [|b P IH]; intros st H; [cbn; lia|].
rewrite WriterApp.putN_cons. pose proof (put1_cap_ge st b H) as H1. pose proof (IH (WriterApp.put1 st b) ltac:(lia)). lia.
Qed.

(* the frame's four saved words at sp - 32 .. sp: s2, s1, s0, ra, read back as the resumed env's extra atoms 32..35 *)
(* ---- the model's call log: put_spec's st' starts from an EMPTY log, so a call's own requests are what it adds ---- *)
Lemma put1_calls_split : forall st b,
  wcalls (WriterApp.put1 st b) = wcalls st +
    wcalls (WriterApp.put1 (WriterApp.mkW (WriterApp.w_failed st) (WriterApp.w_text st) (WriterApp.w_cap st)
              (WriterApp.w_cnt st) (WriterApp.w_fail st) []) b).
Proof.
intros [f t c n fl cs] b. unfold wcalls, WriterApp.put1.
cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls].
destruct (negb (f =? 0)); [cbn [WriterApp.w_calls length]; lia|].
destruct (_ <=? c); [cbn [WriterApp.w_calls length]; lia|].
destruct (n =? fl); cbn [WriterApp.w_calls]; rewrite !length_app; cbn [length]; lia.
Qed.
Lemma put1_calls_ge : forall st b, wcalls st <= wcalls (WriterApp.put1 st b).
Proof. intros st b. rewrite put1_calls_split. unfold wcalls. lia. Qed.
Lemma putN_calls_ge : forall P st, wcalls st <= wcalls (WriterApp.putN st P).
Proof.
induction P as [|b P IH]; intros st; [cbn; lia|].
rewrite WriterApp.putN_cons. pose proof (put1_calls_ge st b). pose proof (IH (WriterApp.put1 st b)). lia.
Qed.
Lemma wcalls_nonneg : forall st, 0 <= wcalls st.
Proof. intros st. unfold wcalls. lia. Qed.
(* ---- the cap-aware journal count (FSH_Fn_writer.v wevk): wev0 of the call log when the call starts at cap = 0
   (the first request is fuzz_realloc's p = 0 arm, 1 event), 3 per request otherwise ---- *)
Definition wev0l (l : list Z) : Z := match l with [] => 0 | _ :: r => 1 + 3 * Z.of_nat (length r) end.
Lemma wevk_l : forall c st, wevk c st =
  if c =? 0 then wev0l (WriterApp.w_calls st) else 3 * Z.of_nat (length (WriterApp.w_calls st)).
Proof. intros c st. unfold wevk, wev0, wev0l, wcalls, EV_fuzz_malloc, EV_fuzz_realloc. reflexivity. Qed.
Lemma wev0l_nonneg : forall l, 0 <= wev0l l.
Proof. intros [|x r]; cbn [wev0l]; lia. Qed.
Lemma wev0l_app_ne : forall l1 l2, l1 <> [] -> wev0l (l1 ++ l2) = wev0l l1 + 3 * Z.of_nat (length l2).
Proof. intros [|x r] l2 H; [contradiction|]. cbn [app wev0l]. rewrite length_app. lia. Qed.
Lemma wev0l_app_ge : forall l1 l2, wev0l l1 + wev0l l2 <= wev0l (l1 ++ l2).
Proof.
intros [|x r] l2; [cbn [app wev0l]; lia|].
rewrite (wev0l_app_ne (x :: r) l2 ltac:(discriminate)). destruct l2 as [|y r2]; cbn [wev0l length]; lia.
Qed.
Lemma wevk_nonneg : forall c st, 0 <= wevk c st.
Proof. intros c st. rewrite wevk_l. destruct (c =? 0); [apply wev0l_nonneg | lia]. Qed.
(* the log one put1 adds is the log of the same put from an empty log *)
Lemma put1_calls_app : forall st b,
  WriterApp.w_calls (WriterApp.put1 st b) = WriterApp.w_calls st ++
    WriterApp.w_calls (WriterApp.put1 (WriterApp.mkW (WriterApp.w_failed st) (WriterApp.w_text st) (WriterApp.w_cap st)
              (WriterApp.w_cnt st) (WriterApp.w_fail st) []) b).
Proof.
intros [f t c n fl cs] b. unfold WriterApp.put1.
cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls].
destruct (negb (f =? 0)); [cbn [WriterApp.w_calls]; rewrite app_nil_r; reflexivity|].
destruct (_ <=? c); [cbn [WriterApp.w_calls]; rewrite app_nil_r; reflexivity|].
destruct (n =? fl); reflexivity.
Qed.
Lemma putN_calls_app : forall P st, exists X, WriterApp.w_calls (WriterApp.putN st P) = WriterApp.w_calls st ++ X.
Proof.
induction P as [|b P IH]; intros st; [exists []; rewrite app_nil_r; reflexivity|].
rewrite WriterApp.putN_cons. destruct (IH (WriterApp.put1 st b)) as (X & EX).
rewrite EX, put1_calls_app, <- app_assoc. eexists. reflexivity.
Qed.
(* the capacity moves only by a request: a grow appends one, the failed alloc appends one and keeps the cap *)
Lemma put1_cap_calls : forall st b, WriterApp.w_cap (WriterApp.put1 st b) <> WriterApp.w_cap st ->
  (length (WriterApp.w_calls st) < length (WriterApp.w_calls (WriterApp.put1 st b)))%nat.
Proof.
intros [f t c n fl cs] b. unfold WriterApp.put1.
cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls].
destruct (negb (f =? 0)); [cbn [WriterApp.w_cap]; intros H; exfalso; exact (H eq_refl)|].
destruct (_ <=? c); [cbn [WriterApp.w_cap]; intros H; exfalso; exact (H eq_refl)|].
intros _. destruct (n =? fl); cbn [WriterApp.w_calls]; rewrite length_app; cbn [length]; lia.
Qed.
Lemma putN_calls_len : forall P st,
  (length (WriterApp.w_calls st) <= length (WriterApp.w_calls (WriterApp.putN st P)))%nat.
Proof. intros P st. destruct (putN_calls_app P st) as (X & EX). rewrite EX, length_app. lia. Qed.
Lemma putN_cap_calls : forall P st, WriterApp.w_cap (WriterApp.putN st P) <> WriterApp.w_cap st ->
  (length (WriterApp.w_calls st) < length (WriterApp.w_calls (WriterApp.putN st P)))%nat.
Proof.
induction P as [|b P IH]; intros st H; [exfalso; exact (H eq_refl)|].
rewrite WriterApp.putN_cons in *.
destruct (Z.eq_dec (WriterApp.w_cap (WriterApp.put1 st b)) (WriterApp.w_cap st)) as [E | N].
- pose proof (IH (WriterApp.put1 st b) ltac:(rewrite E; exact H)) as H1.
  pose proof (f_equal (@length Z) (put1_calls_app st b)) as H2. rewrite length_app in H2. lia.
- pose proof (put1_cap_calls st b N) as H1. pose proof (putN_calls_len P (WriterApp.put1 st b)) as H2. lia.
Qed.
(* the count rises by one per request, with no wrap under the call's own bound *)
Lemma put1_cnt_step : forall st b, 0 <= WriterApp.w_cnt st ->
  WriterApp.w_cnt st + (wcalls (WriterApp.put1 st b) - wcalls st) < 2 ^ 64 ->
  WriterApp.w_cnt (WriterApp.put1 st b) = WriterApp.w_cnt st + (wcalls (WriterApp.put1 st b) - wcalls st).
Proof.
intros [f t c n fl cs] b H0 Hb. cbn [WriterApp.w_cnt] in *. unfold wcalls, WriterApp.put1 in *.
cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls] in *.
destruct (negb (f =? 0)); [cbn [WriterApp.w_cnt WriterApp.w_calls length] in *; lia|].
destruct (_ <=? c); [cbn [WriterApp.w_cnt WriterApp.w_calls length] in *; lia|].
destruct (n =? fl); cbn [WriterApp.w_cnt WriterApp.w_calls] in *; rewrite !length_app in *; cbn [length] in *;
  (rewrite Z.mod_small by lia); lia.
Qed.
Lemma repeat_app_z : forall {T} (x : T) a b, repeat x (a + b)%nat = repeat x a ++ repeat x b.
Proof. intros T x a b. induction a as [|a IH]; [reflexivity|]. cbn [repeat Nat.add app]. rewrite IH. reflexivity. Qed.
(* the two words a frame chain reads, from the bytes being present *)
Lemma rdword_present : forall (H : word -> bool) m a, (forall i, 0 <= i < 8 -> apresent H m (a + i)) ->
  exists v, rdword (aview tfibsegs H m) a = Some v.
Proof.
intros H m a Hp.
assert (E : forall i, 0 <= i < 8 -> exists b, aview tfibsegs H m (a + i) = Some b).
{ intros i Hi. destruct (Hp i Hi) as (Hh & b & Hb). exists (bv_unsigned b).
  unfold aview, mbyte, mrestrict. rewrite Hh, Hb. reflexivity. }
unfold rdword.
destruct (E 0 ltac:(lia)) as (b0 & E0). rewrite Z.add_0_r in E0. rewrite E0.
destruct (E 1 ltac:(lia)) as (b1 & E1). rewrite E1.
destruct (E 2 ltac:(lia)) as (b2 & E2). rewrite E2.
destruct (E 3 ltac:(lia)) as (b3 & E3). rewrite E3.
destruct (E 4 ltac:(lia)) as (b4 & E4). rewrite E4.
destruct (E 5 ltac:(lia)) as (b5 & E5). rewrite E5.
destruct (E 6 ltac:(lia)) as (b6 & E6). rewrite E6.
destruct (E 7 ltac:(lia)) as (b7 & E7). rewrite E7.
eexists. reflexivity.
Qed.

Definition ind_cs : list YP09.chunk :=
  [YP09.mkChunk 24 (CVal 8 (SOff 32 0)); YP09.mkChunk 16 (CVal 8 (SOff 33 0));
   YP09.mkChunk 8 (CVal 8 (SOff 34 0)); YP09.mkChunk 0 (CVal 8 (SOff 35 0))].
Ltac ics := unfold acallee_saved;
  repeat (lazymatch goal with |- context [bv_unsigned ?q] =>
    let z := eval vm_compute in (bv_unsigned q) in change (bv_unsigned q) with z end); lia.

(* the callee-saved registers at indent's ret: ra, s0, s1, s2 reloaded from the frame (extra atoms 32..35), sp back up *)
Definition ind_expect (r : bv 5) : sv :=
  match bv_unsigned r with 1 => SOff 32 0 | 2 => SOff 2 32 | 8 => SOff 33 0 | 9 => SOff 34 0 | 18 => SOff 35 0
  | z => SOff (Z.to_nat z) 0 end.
(* addiw s0, s0, -1 on s0 = v, 1 <= v < 2^31 *)
Lemma U_addiw_m1 : forall E n v, ew E n = Z_to_bv 64 v -> 1 <= v < 2 ^ 31 ->
  U E (SAluw ALU_ADD (SOff n 0) (SLit (-1))) = v - 1.
Proof.
intros E n v Hn Hv.
rewrite U_of_S, S_SAluw. cbn [zalu_raw]. rewrite (U_atom E n v Hn ltac:(lia)), U_SLit.
change (zcanon (-1) mod 2 ^ 32) with (2 ^ 32 - 1).
rewrite (Z.mod_small v (2 ^ 32)) by lia.
unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
change (bv_modulus 64) with (2 ^ 64).
replace (v + (2 ^ 32 - 1) + 2 ^ 31) with ((v - 1 + 2 ^ 31) + 1 * 2 ^ 32) by lia.
rewrite Z.mod_add by lia. rewrite (Z.mod_small (v - 1 + 2 ^ 31)) by lia.
replace (v - 1 + 2 ^ 31 - 2 ^ 31) with (v - 1) by lia. apply Z.mod_small. lia.
Qed.
(* the signed value of an atom holding a small signed number, and a signed branch on it *)
Lemma S_atom : forall E n v, ew E n = Z_to_bv 64 v -> - 2 ^ 63 <= v < 2 ^ 63 -> Sg E (SOff n 0) = v.
Proof.
intros E n v Hn Hv. rewrite S_SOff, Hn, Z.add_0_r, Z_to_bv_unsigned, bv_swrap_wrap. apply swrap64_id. unfold half64. lia.
Qed.
Lemma branch_ge_S : forall E a b, branch_taken BC_GE (sv_denot E a) (sv_denot E b) = negb (Sg E a <? Sg E b).
Proof. intros E a b. cbn [branch_taken]. unfold bv_lts, Sg. reflexivity. Qed.
Lemma repeat_snoc : forall {T} (x : T) n, repeat x n ++ [x] = repeat x (S n).
Proof. intros T x n. induction n as [|n IH]; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.
Lemma concat_repeat2_len : forall k, length (concat (repeat [32; 32] k)) = (2 * k)%nat.
Proof. induction k as [|k IH]; [reflexivity|]. cbn [repeat concat]. rewrite length_app, IH. cbn. lia. Qed.
Lemma cs_in : forall r : bv 5, acallee_saved (bv_unsigned r) -> In r CALLEE_SAVED.
Proof.
intros r Hr.
assert (Hin : In (Z_to_bv 5 (bv_unsigned r) : bv 5) CALLEE_SAVED).
{ remember (bv_unsigned r) as z eqn:Ez. clear Ez r. unfold acallee_saved in Hr. cbv [CALLEE_SAVED In].
  assert (Hc : z = 2 \/ z = 3 \/ z = 4 \/ z = 8 \/ z = 9 \/ z = 18 \/ z = 19 \/ z = 20 \/ z = 21 \/ z = 22 \/ z = 23 \/
    z = 24 \/ z = 25 \/ z = 26 \/ z = 27) by lia.
  repeat (destruct Hc as [->|Hc]; [repeat (first [left; apply bv_eq; reflexivity | right])|]).
  subst. repeat (first [left; apply bv_eq; reflexivity | right]). }
rewrite Z_to_bv_bv_unsigned in Hin. exact Hin.
Qed.

(* the frame's chunks right after the prologue, under the entry env: ra, s0, s1, s2 as atoms 1, 8, 9, 18 *)
Definition ind_cs0 : list YP09.chunk :=
  [YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
   YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].

(* ---- memory kept outside one byte window [lo, hi) (a run's frame writes) ---- *)
Definition sout (lo hi : Z) (m m' : word -> option byte) : Prop :=
  forall x : word, ~ (lo <= bv_unsigned x < hi) -> m' x = m x.
Lemma sout_refl : forall lo hi m, sout lo hi m m.
Proof. intros lo hi m x _. reflexivity. Qed.
Lemma sout_trans : forall lo hi m1 m2 m3, sout lo hi m1 m2 -> sout lo hi m2 m3 -> sout lo hi m1 m3.
Proof. intros lo hi m1 m2 m3 H1 H2 x Hx. rewrite (H2 x Hx). exact (H1 x Hx). Qed.
Lemma sout_frame1 : forall E (r : YP09.region) m m', frame_of E [r] m m' ->
  sout (base_val E (YP09.r_base r) + YP09.r_wlo r) (base_val E (YP09.r_base r) + YP09.r_whi r) m m'.
Proof.
intros E r m m' HF x Hx. apply HF. intros (r' & Hin & Hr). destruct Hin as [<- | []]. exact (Hx Hr).
Qed.
Lemma sout_mrestrict : forall lo hi m m' (H : word -> bool) a, sout lo hi m m' -> 0 <= a < 2 ^ 64 ->
  ~ (lo <= a < hi) -> mrestrict H m' (Z_to_bv 64 a) = mrestrict H m (Z_to_bv 64 a).
Proof.
intros lo hi m m' H a Hs Ha Hn. unfold mrestrict. rewrite (Hs (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by lia. exact Hn.
Qed.
Lemma sout_mbyte : forall lo hi m m' (H : word -> bool) a, sout lo hi m m' -> 0 <= a < 2 ^ 64 ->
  ~ (lo <= a < hi) -> mbyte tfibsegs (mrestrict H m') a = mbyte tfibsegs (mrestrict H m) a.
Proof.
intros lo hi m m' H a Hs Ha Hn. unfold mbyte. rewrite (sout_mrestrict lo hi m m' H a Hs Ha Hn). reflexivity.
Qed.
Lemma sout_val_mem : forall lo hi m m' (H : word -> bool) a (n : nat) v, sout lo hi m m' ->
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (a + Z.of_nat n <= lo \/ hi <= a) ->
  val_mem tfibsegs (mrestrict H m) a n v -> val_mem tfibsegs (mrestrict H m') a n v.
Proof.
intros lo hi m m' H a n v Hs H0 H1 Hd Hv k Hk.
rewrite (sout_mbyte lo hi m m' H (a + Z.of_nat k) Hs ltac:(lia) ltac:(lia)). exact (Hv k Hk).
Qed.
Lemma sout_garr8 : forall lo hi m m' (H : word -> bool) a l, sout lo hi m m' ->
  0 <= a -> a + Z.of_nat (length l) <= 2 ^ 64 -> (a + Z.of_nat (length l) <= lo \/ hi <= a) ->
  garr8 tfibsegs (mrestrict H m) a l -> garr8 tfibsegs (mrestrict H m') a l.
Proof.
intros lo hi m m' H a l Hs H0 H1 Hd Hg j Hj. destruct (Hg j Hj) as [Hv Hb]. split; [|exact Hb].
apply (sout_val_mem lo hi m m' H (a + Z.of_nat j) 1 _ Hs); [lia | lia | lia | exact Hv].
Qed.
Lemma sout_writable : forall lo hi m m' (H : word -> bool) a, sout lo hi m m' -> 0 <= a < 2 ^ 64 ->
  ~ (lo <= a < hi) -> writable_at tfibsegs (mrestrict H m) a -> writable_at tfibsegs (mrestrict H m') a.
Proof.
intros lo hi m m' H a Hs Ha Hn. apply writable_at_eq. exact (sout_mrestrict lo hi m m' H a Hs Ha Hn).
Qed.
Lemma sout_writable_iff : forall lo hi m m' (H : word -> bool) a, sout lo hi m m' -> 0 <= a < 2 ^ 64 ->
  ~ (lo <= a < hi) -> (writable_at tfibsegs (mrestrict H m) a <-> writable_at tfibsegs (mrestrict H m') a).
Proof.
intros lo hi m m' H a Hs Ha Hn. split; apply writable_at_eq;
  [exact (sout_mrestrict lo hi m m' H a Hs Ha Hn) | symmetry; exact (sout_mrestrict lo hi m m' H a Hs Ha Hn)].
Qed.
Lemma sout_apresent : forall lo hi m m' (H : word -> bool) a, sout lo hi m m' -> 0 <= a < 2 ^ 64 ->
  ~ (lo <= a < hi) -> apresent H m a -> apresent H m' a.
Proof.
intros lo hi m m' H a Hs Ha Hn (Hh & b & Hb). split; [exact Hh|]. exists b.
rewrite (Hs (Z_to_bv 64 a)); [exact Hb|]. rewrite unsigned_lit_small by lia. exact Hn.
Qed.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis IMG : fs_img_facts tfibsegs B.
Hypothesis PUT : @put_spec fx rc SK B tfibsegs.

Lemma sout_same_below : forall lo hi m m', sout lo hi m m' -> alloc_ceiling <= lo -> same_below m m' alloc_ceiling.
Proof.
intros lo hi m m' Hs Hl x Hx. pose proof asan_consts as (C1 & _). apply Hs.
rewrite unsigned_lit_small by lia. lia.
Qed.

(* the out-object kept across a memory change outside [lo, hi), the window above alloc_ceiling and below o *)
Lemma wout_ok_sout : forall ly S (W : world tfibsegs) m m' o buf cap failed text lo hi mx md,
  AR tfibsegs B ly S W mx md -> sout lo hi m m' -> alloc_ceiling <= lo -> hi <= o -> o + 32 <= 2 ^ 64 ->
  wout_ok B tfibsegs ly S W m o buf cap failed text -> wout_ok B tfibsegs ly S W m' o buf cap failed text.
Proof.
intros ly S W m m' o buf cap failed text lo hi mx md HAR Hs Hl Hh Ho
  (Ho8 & Ho0 & Hot & Hwa & Hb & Hc & V0 & V8 & V16 & V24 & Hf & Hbo & Hbuf).
pose proof asan_consts as (C1 & _).
split; [exact Ho8|]. split; [exact Ho0|]. split; [exact Hot|].
split.
{ intros i Hi. destruct (Hwa i Hi) as [Hw Hp]. split.
  - apply (sout_writable lo hi m m' _ (o + i) Hs); [lia | lia | exact Hw].
  - apply (sout_apresent lo hi m m' _ (o + i) Hs); [lia | lia | exact Hp]. }
split; [exact Hb|]. split; [exact Hc|].
split; [apply (sout_val_mem lo hi m m' _ o 8 _ Hs); [lia | cbn; lia | right; lia | exact V0]|].
split; [apply (sout_val_mem lo hi m m' _ (o + 8) 8 _ Hs); [lia | cbn; lia | right; lia | exact V8]|].
split; [apply (sout_val_mem lo hi m m' _ (o + 16) 8 _ Hs); [lia | cbn; lia | right; lia | exact V16]|].
split; [apply (sout_val_mem lo hi m m' _ (o + 24) 4 _ Hs); [lia | cbn; lia | right; lia | exact V24]|].
split; [exact Hf|]. split; [exact Hbo|].
destruct Hbuf as [Hz | (Hj & Hrb & Hlen & Hzb)]; [left; exact Hz | right].
pose proof Hrb as (Hin & Hal & Hcap & Hvh).
destruct (fsw_ablock_low B ly S W mx md _ _ HAR Hin) as (A1 & A2 & A3).
split; [exact Hj|]. split.
- split; [exact Hin|]. split; [exact Hal|]. split; [exact Hcap|].
  apply (sout_val_mem lo hi m m' _ (buf - HEAD) 8 _ Hs); [unfold HEAD in *; lia | cbn; unfold HEAD in *; lia
  | left; cbn; unfold HEAD in *; lia | exact Hvh].
- split; [exact Hlen|]. unfold zbytes_at in *.
  apply (sout_garr8 lo hi m m' _ buf _ Hs); [unfold HEAD in *; lia | rewrite length_app; cbn [length]; unfold HEAD in *; lia
  | left; rewrite length_app; cbn [length]; unfold HEAD in *; lia | exact Hzb].
Qed.

(* every byte of [s, ot) is kept by a change outside [lo, hi) with hi <= s *)
Lemma wkeep_sout : forall (W : world tfibsegs) m m' lo hi s ot o n, sout lo hi m m' -> hi <= s -> 0 <= s -> ot <= 2 ^ 64 ->
  wkeep tfibsegs W W m m' s ot o n.
Proof.
intros W m m' lo hi s ot o n Hs Hh H0 Ht a Ha _. split.
- apply (sout_mbyte lo hi m m' _ a Hs); lia.
- apply (sout_writable_iff lo hi m m' _ a Hs); lia.
Qed.

(* an 8-byte word the walk knows by val_mem, as the frame-chain clause reads it *)
Lemma rdword_of_val_mem : forall (ly : alayout) (H : word -> bool) m a v, 0 <= v < 2 ^ 64 ->
  val_mem tfibsegs (mrestrict H m) a 8 v -> rdword (aview tfibsegs H m) a = Some v.
Proof.
intros ly H m a v Hv Hvm. apply (rdword_cell B ly _ a v Hv).
unfold cell_holds. cbn [c_at c_val c_w z8 c8 aeval]. intros k Hk.
unfold aview. rewrite (Hvm k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N]. change (2 ^ 8) with 256.
unfold le_byte, YO0f.le_byte.
generalize (Z.shiftr (v mod 2 ^ (8 * Z.of_nat 8)) (8 * Z.of_nat k)). intros z.
rewrite Z.mod_mod by lia. reflexivity.
Qed.
(* a word kept by a callee's wkeep is read the same after the call *)
Lemma rdword_keep : forall (W1 W2 : world tfibsegs) m1 m2 a,
  (forall i, 0 <= i < 8 -> mbyte tfibsegs (mrestrict (w_H W2) m2) (a + i) = mbyte tfibsegs (mrestrict (w_H W1) m1) (a + i)) ->
  rdword (aview tfibsegs (w_H W2) m2) a = rdword (aview tfibsegs (w_H W1) m1) a.
Proof.
intros W1 W2 m1 m2 a Hk. apply rdword_ext. intros k Hk8. unfold aview. rewrite (Hk k Hk8). reflexivity.
Qed.

(* the unpoisoned reading and the machine's own agree on the stack *)
Lemma rdword_unpoison : forall ly S U (W : world tfibsegs) mem md a, ARU tfibsegs B ly S U W mem md ->
  kHighMemBeg <= a -> a + 8 <= 2 ^ 64 ->
  rdword (aview tfibsegs (w_H W) (unpoison U mem)) a = rdword (aview tfibsegs (w_H W) mem) a.
Proof.
intros ly S U W mem md a HA H1 H2. apply rdword_ext. intros k Hk.
exact (fsw_aview_unpoison_high B ly S U W mem md (a + k) HA ltac:(lia)).
Qed.

(* ---- the writer budget (lib/B/FSH_Fn_writer.v:123-141): what is left is never negative while cap <= WMAX ---- *)
Lemma wbudget_kept_refl : forall S failed cap cnt, cap <= WMAX -> wbudget_kept S S failed cap cnt failed cap cnt.
Proof. intros S failed cap cnt Hc. unfold wbudget_kept. lia. Qed.

(* indent_spec's post, named (lib/B/FSH_Fn_writer.v:320-335) *)
Definition ind_post (regs : bvmap 5 word) ly S U (W : world tfibsegs) mem md ot o pretty depth buf cap failed text
    live peak cnt fail : world tfibsegs -> config -> Prop :=
  fun W' c' => exists (st' : WriterApp.wst) buf' U',
    st' = WriterApp.putN (WriterApp.mkW failed text cap cnt fail [])
            (WriterValue.wind (negb (pretty =? 0)) depth) /\
    uswap U U' buf buf' cap /\
    @wpost fx rc SK B tfibsegs STK_indent ot (FS_PSTAT_FP ++ wbuf_fp buf cap) regs ly S U W mem md (wevk cap st') U'
      (fun ly' S' W' regs' mem' md' =>
         wout_ok B tfibsegs ly' S' W' mem' o buf' (WriterApp.w_cap st') (WriterApp.w_failed st') (WriterApp.w_text st') /\
         wbudget_kept S S' failed cap cnt (WriterApp.w_failed st') (WriterApp.w_cap st') (WriterApp.w_cnt st') /\
         bswap (ablocks B ly S) (ablocks B ly' S') buf buf' cap (WriterApp.w_cap st') /\
         wkeep tfibsegs W W' mem mem' (spZ regs) ot o 32 /\
         (exists peak', peak <= peak' <= Z.max peak (live - cap + WriterApp.w_cap st') /\
            fs_glob tfibsegs W' mem' (live + WriterApp.w_cap st' - cap) peak'
              (WriterApp.w_cnt st') (WriterApp.w_fail st')))
      W' c'.

(* ================= the pretty = 0 arm: beqz a1 taken, no put, the epilogue returns ================= *)
Lemma indent_arm0 : forall ly S U W regs mem md ch ot o pretty depth buf cap failed text live peak cnt fail,
  fpreU tfibsegs B STK_indent ly S U W regs mem md ch ->
  getr regs 11 = w64 pretty -> pretty = 0 ->
  wout_ok B tfibsegs ly S W mem o buf cap failed text -> fs_glob tfibsegs W mem live peak cnt fail ->
  spZ regs <= o -> o + 32 <= ot -> ot mod 16 = 0 -> ot <= ly_top ly ->
  (forall a, spZ regs <= a < ot -> apresent (w_H W) mem a) -> cap <= WMAX ->
  SRr tfibsegs W (cfg_at tfibsegs A_indent regs mem md)
    (ind_post regs ly S U W mem md ot o pretty depth buf cap failed text live peak cnt fail).
Proof.
intros ly S U W regs mem md ch ot o pretty depth buf cap failed text live peak cnt fail
  HPRE H11 Hp0 Hwo Hglob Hso Hot Hot16 Htop Hwin Hcap.
pose proof Hwo as (_ & _ & _ & _ & _ & Hcap0 & _).
subst pretty.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof fs_segs_low as HSL. pose proof fs_wx as HWX.
destruct HPRE as [HAPU HRO].
pose proof (fsw_sp B _ ly S U W regs mem md ch HAPU) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _).
pose proof HAPU as (HAP & _ & _).
pose proof HAP as (HAR & Hra & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & _ & _ & _ & Hhi47 & _ & Htop0 & Htop2).
(* the frame budget's value, computed (not pinned), so a budget change in FSH_Gen / FSH_Base needs no edit here *)
assert (FS : STK_indent = ltac:(let v := eval vm_compute in STK_indent in exact v)) by reflexivity.
pose proof (fsw_entry B STK_indent 32 ly S U W regs mem md ch A_indent HAPU ltac:(lia) ltac:(vm_compute; reflexivity))
  as HS.
pose proof (fsw_ajournal_init_ot B STK_indent (FS_PSTAT_FP ++ wbuf_fp buf cap) ly S U W regs mem md ch ot HAPU
  ltac:(lia) Hot16 Htop Hwin) as HJ.
pose proof (fsw_ARU B _ ly S U W regs mem md ch HAPU) as HARU.
set (E := Ereg regs []) in HS.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs [] 2 2%bv eq_refl); reflexivity).
assert (E11 : ew E 11 = Z_to_bv 64 0) by (subst E; rewrite (ew_Ereg_nat regs [] 11 11%bv eq_refl); exact H11).
unfold cfg_at. change (w64 A_indent) with (Z_to_bv 64 A_indent).
(* ---- 0x86368 .. the branch at 0x8637c ---- *)
fsw_aj_runU fsw_wr_tbl_ok HS HJ HARU.
{ change (ss_mem (fss0 A_indent 32)) with [fstk 32].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spZ regs - ot);
    [reflexivity | rewrite Usp; lia | cbn; lia | cbn; lia | apply awr_ok_nil]. }
assert (SO1 : sout (spZ regs - 32) (spZ regs) mem (ms_mem ms)).
{ change (frame_of E [fstk 32] mem (ms_mem ms)) in HF. pose proof (sout_frame1 E _ _ _ HF) as H.
  cbn [fstk YP09.r_base YP09.r_wlo YP09.r_whi base_val] in H. rewrite Usp in H.
  replace (spZ regs + -32) with (spZ regs - 32) in H by lia. rewrite Z.add_0_r in H. exact H. }
eapply SRr_sym_branch with (c := BC_EQ) (a := SOff 11 0) (b := SLit 0); [exact HS | |].
2: { intros Hb _. exfalso. rewrite branch_eq_U in Hb.
     rewrite (U_atom E 11 0 E11 ltac:(lia)), U_SLit in Hb. cbn in Hb. discriminate Hb. }
intros _ HS2. clear HS.
(* ---- taken: 0x863c0 .. the return at 0x863d4 ---- *)
fsw_aj_runU fsw_wr_tbl_ok HS2 HJ HARU.
{ cbn [add_cond ss_mem].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spZ regs - ot);
    [reflexivity | rewrite Usp; lia | cbn; lia | cbn; lia | apply awr_ok_nil]. }
assert (SO2 : sout (spZ regs - 32) (spZ regs) mem (ms_mem ms0)).
{ cbn [add_cond ss_mem] in HF0. pose proof (sout_frame1 E _ _ _ HF0) as H.
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in H. rewrite Usp in H.
  replace (spZ regs + -32) with (spZ regs - 32) in H by lia. rewrite Z.add_0_r in H.
  exact (sout_trans _ _ _ _ _ SO1 H). }
pose proof (fsw_reg_atom _ regs [] _ ms0 1%bv 1%bv 1 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R1.
eapply (SRr_ret_at tfibsegs fsw_wr_tbl fsw_wr_tbl_ok fs_wx); [exact HS2 | reflexivity | vm_compute; reflexivity |].
intros mat2.
assert (Hpc : v_jalr (YK11.getr (ms_regs ms0) 1) 0 = YK11.getr regs 1) by (rewrite R1; exact Hra).
rewrite Hpc.
exists (WriterApp.mkW failed text cap cnt fail []), buf, U.
split; [reflexivity|]. split; [left; split; reflexivity|].
unfold wpost, fpostU.
do 5 eexists. split; [reflexivity|].
split.
{ apply (ajournal_materialize tfibsegs B LAWS HSL). eapply ajournal_mono_k; [exact HJ|].
  apply wevk_nonneg. }
split; [exact (proj1 (proj2 HARU))|].
split; [exact (proj2 (proj2 HARU))|].
split; [eapply (aregs_preserved_of_st_ok tfibsegs _ E _ _ regs [] HS2); [apply env_agree_refl | vm_compute; reflexivity]|].
cbn [WriterApp.w_cap WriterApp.w_failed WriterApp.w_text WriterApp.w_cnt WriterApp.w_fail].
split; [exact (wout_ok_sout ly S W mem (ms_mem ms0) o buf cap failed text _ _ _ _ HAR SO2 ltac:(lia) Hso ltac:(lia) Hwo)|].
split; [exact (wbudget_kept_refl S failed cap cnt Hcap)|].
split; [left; split; [reflexivity | split; reflexivity]|].
split; [apply (wkeep_sout W mem (ms_mem ms0) _ _ _ _ _ _ SO2); lia|].
exists peak. split; [lia|]. replace (live + cap - cap) with live by lia.
exact (fs_glob_below W mem (ms_mem ms0) live peak cnt fail (sout_same_below _ _ _ _ SO2 ltac:(lia)) Hglob).
Qed.

(* ================= journal and image facts for a program call from indent ================= *)
(* a byte in a range one image segment holds *)
Lemma in_img_of_range : forall lo hi a,
  existsb (fun sg => (Z.of_N (seg_base sg) <=? lo) && (hi <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) tfibsegs
    = true ->
  lo <= a < hi -> in_img tfibsegs a.
Proof.
intros lo hi a Hb Ha. apply existsb_exists in Hb as (sg & Hin & Hs). apply andb_prop in Hs as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. exists sg. split; [exact Hin | lia].
Qed.
(* fuzz/alloc.c's four statics are image bytes *)
Lemma pstat_img : forall a, inFP FS_PSTAT_FP a -> in_img tfibsegs a.
Proof.
intros a (r & Hin & Hr). unfold FS_PSTAT_FP in Hin. cbn [In] in Hin.
destruct Hin as [<- | [<- | [<- | [<- | []]]]]; cbn [fst snd] in Hr;
  (refine (in_img_of_range _ _ a _ Hr); vm_compute; reflexivity).
Qed.
(* the read-only view's addresses are image bytes below FS_IMG_END *)
Lemma in_roP_img : forall a, in_roP tfibsegs FS_RLO FS_RHI a -> in_img tfibsegs a.
Proof.
intros a [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr]|].
refine (in_img_of_range FS_RLO FS_RHI a _ Hr). vm_compute. reflexivity.
Qed.

(* a journal's tick bound reset to any k' that bounds st_nev *)
(* an address range that no read-only segment covers and that misses the relro window *)
Lemma not_roP_range : forall lo hi a,
  forallb (fun sg => seg_writable sg || ((hi <=? Z.of_N (seg_base sg)) ||
    (Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <=? lo))) tfibsegs = true ->
  (hi <= FS_RLO \/ FS_RHI <= lo) -> lo <= a < hi -> ~ in_roP tfibsegs FS_RLO FS_RHI a.
Proof.
intros lo hi a Hb Hrel Ha [(sg & Hin & Hw & Hr) | Hr]; [|unfold FS_RLO, FS_RHI in *; lia].
pose proof (proj1 (forallb_forall _ _) Hb sg Hin) as H. cbn beta in H. rewrite Hw in H. cbn [orb] in H.
apply orb_prop in H as [H | H]; apply Z.leb_le in H; lia.
Qed.
(* fuzz/alloc.c's four statics are writable image bytes, so they are not in the read-only view *)
Lemma pstat_not_roP : forall a, inFP FS_PSTAT_FP a -> ~ in_roP tfibsegs FS_RLO FS_RHI a.
Proof.
intros a (r & Hin & Hr). unfold FS_PSTAT_FP in Hin. cbn [In] in Hin.
destruct Hin as [<- | [<- | [<- | [<- | []]]]]; cbn [fst snd] in Hr;
  [ refine (not_roP_range 0xa41c0 0xa41c8 a _ _ Hr)
  | refine (not_roP_range 0x5daac0 0x5daac8 a _ _ Hr)
  | refine (not_roP_range 0x5daae0 0x5daae8 a _ _ Hr)
  | refine (not_roP_range 0x5dab00 0x5dab08 a _ _ Hr)];
  first [vm_compute; reflexivity | unfold FS_RLO, FS_RHI; lia].
Qed.

(* the machine's memory and its unpoisoned reading agree below the shadow *)
Lemma ind_low_unpoison : forall ly S U (W : world tfibsegs) mem md a, ARU tfibsegs B ly S U W mem md ->
  0 <= a < SHADOW_OFF -> aview tfibsegs (w_H W) (unpoison U mem) a = aview tfibsegs (w_H W) mem a.
Proof.
intros ly S U W mem md a HA Ha. apply (aview_at tfibsegs).
apply (ARU_mem_low tfibsegs B ly S U W mem md); [exact HA|]. rewrite unsigned_lit_small by (unfold SHADOW_OFF in *; lia).
lia.
Qed.
Lemma in_roP_low : forall a, in_roP tfibsegs FS_RLO FS_RHI a -> 0 <= a < SHADOW_OFF.
Proof. intros a H. pose proof (fs_segs_img a (in_roP_img a H)). unfold FS_IMG_END, SHADOW_OFF in *. lia. Qed.
Lemma arodata_unpoison : forall ly S U (W : world tfibsegs) mem md, ARU tfibsegs B ly S U W mem md ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) mem) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) (unpoison U mem)).
Proof.
intros ly S U W mem md HA HRO a Hro Hno Her. rewrite (ind_low_unpoison ly S U W mem md a HA (in_roP_low a Hro)).
exact (HRO a Hro Hno Her).
Qed.
(* the read-only view across a callee journal whose footprint leaves the sink head alone *)
Lemma arodata_journal : forall STK sp0 FP lyc Sc Uc (Wc : world tfibsegs) memC mdC ly' S' U' W' mem' md' k,
  ajournal tfibsegs B STK sp0 FP lyc Sc Wc (unpoison Uc memC) mdC [] ly' S' W' (unpoison U' mem') md' k ->
  ARU tfibsegs B lyc Sc Uc Wc memC mdC -> ARU tfibsegs B ly' S' U' W' mem' md' -> ~ YI16.sink_open_fp FP ->
  (forall a, in_roP tfibsegs FS_RLO FS_RHI a -> ~ inFP FP a) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H Wc) memC) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W') mem').
Proof.
intros STK sp0 FP lyc Sc Uc Wc memC mdC ly' S' U' W' mem' md' k HJ HA HA' Hcl HFPI HRO a Hro Hno Her.
pose proof (in_roP_low a Hro) as Hlow.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite <- (ind_low_unpoison ly' S' U' W' mem' md' a HA' Hlow).
rewrite (F3 a (in_roP_img a Hro) Hno Her (HFPI a Hro) (fp_spares_closed FP a Hcl)).
rewrite (ind_low_unpoison lyc Sc Uc Wc memC mdC a HA Hlow).
exact (HRO a Hro Hno Her).
Qed.

(* ================= the writer's buffer, heads and footprint across one put ================= *)
Lemma ablocks_nodup_mid : forall ly S (W : world tfibsegs) mx md X x Y, AR tfibsegs B ly S W mx md ->
  ablocks B ly S = X ++ x :: Y -> ~ In x (X ++ Y).
Proof.
intros ly S W mx md X [p n] Y HAR E Hin.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
assert (Hx : In (p, n) (ablocks B ly S)) by (rewrite E; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hx) as (_ & _ & _ & _ & _ & Hpw & Hn).
rewrite E, map_app in Hpw. cbn [map] in Hpw.
apply (pairwise_dup zdisjoint _ _ _) in Hpw;
  [| rewrite <- map_app; exact (in_map (fun b : Z * Z => (fst b, req_size (snd b))) _ _ Hin)].
unfold zdisjoint in Hpw. cbn [fst snd] in Hpw. pose proof (req_size_pos n ltac:(lia)). lia.
Qed.
Lemma U_nodup_mid : forall ly S U X x Y, upoison_ok B ly S U -> U = X ++ x :: Y -> ~ In x (X ++ Y).
Proof.
intros ly S U X x Y (HF & Hpw) E Hin. subst U.
pose proof (pairwise_dup zdisjoint X x Y Hpw Hin) as Hd.
assert (Hx : In x (X ++ x :: Y)) by (apply in_or_app; right; left; reflexivity).
pose proof (proj1 (Forall_forall _ _) HF x Hx) as (_ & H8 & _). unfold zdisjoint in Hd. lia.
Qed.
Lemma U_low : forall ly S U (W : world tfibsegs) mx md r, AR tfibsegs B ly S W mx md -> upoison_ok B ly S U ->
  In r U -> 4096 <= fst r.
Proof.
intros ly S U W mx md r HAR (HF & _) Hin.
destruct (proj1 (Forall_forall _ _) HF r Hin) as (_ & _ & _ & p & n & Hpn & Hp & _).
destruct (fsw_ablock_low B ly S W mx md p n HAR Hpn) as (H1 & _). lia.
Qed.
(* the out-object's buffer: none, or a live block *)
Lemma wout_buf : forall ly S (W : world tfibsegs) m o buf cap f t, wout_ok B tfibsegs ly S W m o buf cap f t ->
  (cap = 0 /\ buf = 0) \/ (0 < cap /\ In (buf - HEAD, cap + HEAD) (ablocks B ly S)).
Proof.
intros ly S W m o buf cap f t (_ & _ & _ & _ & _ & Hc & _ & _ & _ & _ & _ & _ & Hbuf).
destruct Hbuf as [(H1 & H2 & _) | ((j & Hj & Ec) & (Hin & _) & _)]; [left; split; assumption | right].
split; [|exact Hin]. rewrite Ec. pose proof (Z.pow_pos_nonneg 2 j ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma low_block_absent : forall ly S (W : world tfibsegs) mx md n, AR tfibsegs B ly S W mx md ->
  ~ In (0 - HEAD, n) (ablocks B ly S).
Proof.
intros ly S W mx md n HAR Hin. destruct (fsw_ablock_low B ly S W mx md _ _ HAR Hin) as (H1 & _). unfold HEAD in H1. lia.
Qed.

(* the heads keep fs's shape across put (FSW_writer_kit.fs_heads_uswap, its two premises from put's post) *)
Lemma fs_heads_put : forall lyc Sc Uc (Wc : world tfibsegs) mc mdc memC ly' S' U' (W' : world tfibsegs) m' md' mem'
    o bufc capc fc tc o' buf' cap' f' t',
  AR tfibsegs B lyc Sc Wc mc mdc -> AR tfibsegs B ly' S' W' m' md' ->
  upoison_ok B lyc Sc Uc -> upoison_ok B ly' S' U' -> fs_heads B lyc Sc Uc ->
  uswap Uc U' bufc buf' capc -> bswap (ablocks B lyc Sc) (ablocks B ly' S') bufc buf' capc cap' ->
  wout_ok B tfibsegs lyc Sc Wc memC o bufc capc fc tc -> wout_ok B tfibsegs ly' S' W' mem' o' buf' cap' f' t' ->
  fs_heads B ly' S' U'.
Proof.
intros lyc Sc Uc Wc mc mdc memC ly' S' U' W' m' md' mem' o bufc capc fc tc o' buf' cap' f' t'
  HAR HAR' OKc OK' HU Hus Hbs Hwoc Hwo'.
eapply fs_heads_uswap; [exact HU | exact Hus | |].
- intros [r1 r2] Hr' Hrc. destruct (HU _ Hrc) as (Hsnd & m & Hm & H16). cbn [fst snd] in *.
  destruct Hbs as [(_ & _ & EA) | [(_ & C1 & C2 & EA' & EC) | (X1 & X2 & C1 & C2 & EA & EA' & EC)]].
  + exists m. rewrite EA. split; assumption.
  + exists m. rewrite EA'. split; [exact (in_realloc C1 C2 _ _ _ EC Hm) | exact H16].
  + rewrite EA in Hm. apply in_app_or in Hm as [Hm | [Hm | Hm]].
    * exists m. rewrite EA'. split; [|exact H16].
      apply (in_realloc C1 C2 (X1 ++ X2)); [exact EC | apply in_or_app; left; exact Hm].
    * injection Hm as Ef Em.
      destruct (Z.eq_dec buf' bufc) as [Eb | Nb].
      -- destruct (wout_buf _ _ _ _ _ _ _ _ _ Hwo') as [(Hc' & Hb') | (Hc' & Hin')].
         ++ exfalso. apply (low_block_absent lyc Sc Wc mc mdc (capc + HEAD) HAR). rewrite <- Hb', Eb, EA.
            apply in_or_app. right. left. reflexivity.
         ++ exists (cap' + HEAD). split; [rewrite <- Ef, <- Eb; exact Hin'|].
            pose proof (req_size_pos (cap' + HEAD) ltac:(unfold HEAD; lia)). unfold HEAD in *. lia.
      -- exfalso. subst r1 r2.
         destruct Hus as [[_ Eb] | [(Y1 & Y2 & EU & EU') | (Hc0 & EU')]].
         ++ exact (Nb Eb).
         ++ rewrite EU' in Hr'. apply in_app_or in Hr' as [Hr' | Hr'].
            ** apply (U_nodup_mid lyc Sc Uc Y1 _ Y2 OKc EU). apply in_or_app. left. exact Hr'.
            ** apply in_app_or in Hr' as [Hr' | [Hr' | []]].
               --- apply (U_nodup_mid lyc Sc Uc Y1 _ Y2 OKc EU). apply in_or_app. right. exact Hr'.
               --- injection Hr' as E1. apply Nb. lia.
         ++ destruct (wout_buf _ _ _ _ _ _ _ _ _ Hwoc) as [(_ & Hb0) | (Hc1 & _)]; [|lia].
            apply (low_block_absent lyc Sc Wc mc mdc (capc + HEAD) HAR). rewrite <- Hb0, EA.
            apply in_or_app. right. left. reflexivity.
    * exists m. rewrite EA'. split; [|exact H16].
      apply (in_realloc C1 C2 (X1 ++ X2)); [exact EC | apply in_or_app; right; exact Hm].
- intros r Hr' Hnr. pose proof (uswap_new_head Uc U' bufc buf' capc r Hus Hr' Hnr) as Er. split; [exact Er|].
  destruct (wout_buf _ _ _ _ _ _ _ _ _ Hwo') as [(Hc' & Hb') | (Hc' & Hin')].
  + exfalso. subst r. pose proof (U_low ly' S' U' W' m' md' _ HAR' OK' Hr') as H. cbn [fst] in H. rewrite Hb' in H.
    unfold HEAD in H. lia.
  + exists (cap' + HEAD). split; [exact Hin'|].
    pose proof (req_size_pos (cap' + HEAD) ltac:(unfold HEAD; lia)). unfold HEAD in *. lia.
Qed.

(* put's footprint at a call of indent, against indent's (the first three arms of FSW_K3.fsw_fp_sub) *)
Lemma ind_fp_cond : forall ly S lyc Sc (Wc : world tfibsegs) mc mdc buf cap bufc capc,
  AR tfibsegs B lyc Sc Wc mc mdc ->
  bswap (ablocks B ly S) (ablocks B lyc Sc) buf bufc cap capc ->
  (capc = 0 /\ bufc = 0) \/ (0 < capc /\ In (bufc - HEAD, capc + HEAD) (ablocks B lyc Sc)) ->
  forall a, inFP (FS_PSTAT_FP ++ wbuf_fp bufc capc) a ->
    (inFP (FS_PSTAT_FP ++ wbuf_fp buf cap) a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
    in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a \/
    (inFP (FS_PSTAT_FP ++ wbuf_fp buf cap) a /\ in_img tfibsegs a).
Proof.
intros ly S lyc Sc Wc mc mdc buf cap bufc capc HAR Hbs Hbc a Ha.
apply inFP_app in Ha as [Ha | Ha].
- right. right. split; [apply inFP_app; left; exact Ha | exact (pstat_img a Ha)].
- unfold wbuf_fp in Ha. destruct (capc =? 0) eqn:Ec; [destruct Ha as (r & [] & _)|].
  apply Z.eqb_neq in Ec.
  destruct Hbc as [(Hc & _) | (Hc & Hin)]; [lia|].
  destruct Ha as (r & [<- | []] & Hr). cbn [fst snd] in Hr.
  assert (Hrs : capc + HEAD <= req_size (capc + HEAD))
    by (pose proof (req_size_pos (capc + HEAD) ltac:(unfold HEAD; lia)); lia).
  destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (bufc - HEAD, capc + HEAD) (ablocks B ly S))
    as [HinA | HnA].
  + left. split; [|exists (bufc - HEAD), (capc + HEAD); split; [exact Hin | lia]].
    apply inFP_app. right.
    destruct Hbs as [(-> & -> & _) | [(Hc0 & C1 & C2 & EA' & EC) | (X1 & X2 & C1 & C2 & EA & EA' & EC)]].
    * unfold wbuf_fp. destruct (cap =? 0) eqn:E0; [apply Z.eqb_eq in E0; lia|].
      exists (buf - HEAD, buf + cap). split; [left; reflexivity | cbn [fst snd]; lia].
    * exfalso. apply (ablocks_nodup_mid lyc Sc Wc mc mdc C1 _ C2 HAR EA'). rewrite EC. exact HinA.
    * rewrite EA in HinA. apply in_app_or in HinA as [HinA | [HinA | HinA]].
      -- exfalso. apply (ablocks_nodup_mid lyc Sc Wc mc mdc C1 _ C2 HAR EA'). rewrite EC.
         apply in_or_app. left. exact HinA.
      -- injection HinA as E1 E2. unfold wbuf_fp. destruct (cap =? 0) eqn:E0; [apply Z.eqb_eq in E0; lia|].
         exists (buf - HEAD, buf + cap). split; [left; reflexivity | cbn [fst snd]; lia].
      -- exfalso. apply (ablocks_nodup_mid lyc Sc Wc mc mdc C1 _ C2 HAR EA'). rewrite EC.
         apply in_or_app. right. exact HinA.
  + right. left. exists (bufc - HEAD), (capc + HEAD). split; [exact Hin|]. split; [exact HnA | lia].
Qed.

(* the bytes of one of fs's read-only literals, from the image facts at an AR state *)
Lemma ind_str_bytes : forall lyc Sc Uc (Wc : world tfibsegs) memC mdC s bs,
  ARU tfibsegs B lyc Sc Uc Wc memC mdC -> arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H Wc) memC) ->
  In (s, bs) FS_RO_STRS -> s + Z.of_nat (length bs) + 1 <= SHADOW_OFF ->
  zbytes_at tfibsegs Wc memC s bs /\ 4096 <= s /\ s + Z.of_nat (length bs) + 1 <= alloc_ceiling.
Proof.
intros lyc Sc Uc Wc memC mdC s bs HA HRO Hin Hlow.
destruct IMG as [_ HIMG].
destruct (HIMG lyc Sc Wc (unpoison Uc memC) mdC (proj1 HA) (arodata_unpoison lyc Sc Uc Wc memC mdC HA HRO))
  as (_ & _ & Hstrs & _).
destruct (proj1 (Forall_forall _ _) Hstrs (s, bs) Hin) as [Hok _]. cbn [fst snd] in Hok.
destruct Hok as ((Hg & _) & H4096 & Hac & _).
split; [|split; [exact H4096 | exact Hac]].
intros j Hj. destruct (Hg j ltac:(rewrite length_app; cbn [length]; lia)) as [Hv Hb].
rewrite app_nth1 in Hv, Hb by exact Hj. split; [|exact Hb].
intros k Hk. rewrite <- (Hv k Hk).
unfold mbyte, mrestrict. rewrite (ARU_mem_low tfibsegs B lyc Sc Uc Wc memC mdC _ HA); [reflexivity|].
assert (Hk0 : (k = 0)%nat) by lia. subst k.
rewrite unsigned_lit_small by (unfold SHADOW_OFF in *; lia). lia.
Qed.

Lemma wkeep_trans : forall (W1 W2 W3 : world tfibsegs) m1 m2 m3 s s' ot o n,
  wkeep tfibsegs W1 W2 m1 m2 s ot o n -> wkeep tfibsegs W2 W3 m2 m3 s' ot o n -> s' <= s ->
  wkeep tfibsegs W1 W3 m1 m3 s ot o n.
Proof.
intros W1 W2 W3 m1 m2 m3 s s' ot o n H1 H2 Hs a Ha Hn. destruct (H1 a Ha Hn) as [E1 I1].
destruct (H2 a ltac:(lia) Hn) as [E2 I2]. split; [rewrite E2; exact E1 | tauto].
Qed.
Lemma wkeep_sout_r : forall (W1 W2 : world tfibsegs) m1 m2 m3 lo hi s ot o n,
  wkeep tfibsegs W1 W2 m1 m2 s ot o n -> sout lo hi m2 m3 -> hi <= s -> 0 <= s -> ot <= 2 ^ 64 ->
  wkeep tfibsegs W1 W2 m1 m3 s ot o n.
Proof.
intros W1 W2 m1 m2 m3 lo hi s ot o n H1 Hs Hh H0 Ht a Ha Hn. destruct (H1 a Ha Hn) as [E1 I1].
split; [rewrite (sout_mbyte lo hi m2 m3 _ a Hs ltac:(lia) ltac:(lia)); exact E1|].
pose proof (sout_writable_iff lo hi m2 m3 (w_H W2) a Hs ltac:(lia) ltac:(lia)). tauto.
Qed.
Lemma val_mem_mbyte_eq : forall (m m' : word -> option byte) a (n : nat) v,
  (forall k, (k < n)%nat -> mbyte tfibsegs m' (a + Z.of_nat k) = mbyte tfibsegs m (a + Z.of_nat k)) ->
  val_mem tfibsegs m a n v -> val_mem tfibsegs m' a n v.
Proof. intros m m' a n v He Hv k Hk. rewrite (He k Hk). exact (Hv k Hk). Qed.

(* ================= indent's walk, the entry data fixed (indent_spec's premises as Section hypotheses) ================= *)
Section L.
Variables (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z)) (ot o pretty depth buf cap failed : Z)
  (text : list Z) (live peak cnt fail : Z).
Hypothesis HPRE : fpreU tfibsegs B STK_indent ly S U W regs mem md ch.
Hypothesis HHD : fs_heads B ly S U.
Hypothesis HFRL : Z.of_nat (length (frames S)) <= FRL_CRT_CALLEE.
Hypothesis HWO : wout_ok B tfibsegs ly S W mem o buf cap failed text.
Hypothesis HGL : fs_glob tfibsegs W mem live peak cnt fail.
Hypothesis HSO : spZ regs <= o.
Hypothesis HOT : o + 32 <= ot.
Hypothesis HOT16 : ot mod 16 = 0.
Hypothesis HTOP : ot <= ly_top ly.
Hypothesis HWIN : forall a, spZ regs <= a < ot -> apresent (w_H W) mem a.
Hypothesis HCAP : cap <= WMAX.
Hypothesis HCL : cap <= live.
Hypothesis HHU : cap <> 0 -> In (buf - HEAD, HEAD) U.
Hypothesis HWB : wbudget_pre S cap cnt live
  (WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) (WriterValue.wind (negb (pretty =? 0)) depth)).
Hypothesis HCH : (o = spZ regs + 8 /\ raZ regs < alloc_ceiling) \/
  (spZ regs + 16 <= o /\ exists ra nfp,
     rdword (aview tfibsegs (w_H W) (unpoison U mem)) (o - 8) = Some ra /\
     rdword (aview tfibsegs (w_H W) (unpoison U mem)) (o - 16) = Some nfp /\ (ra < 4096 \/ nfp < alloc_ceiling)).
Hypothesis H10 : getr regs 10 = w64 o.
Hypothesis H11 : getr regs 11 = w64 pretty.
Hypothesis H12 : getr regs 12 = w64 depth.
Hypothesis HPR : 0 <= pretty < alloc_ceiling.
Hypothesis HDEP : - 2 ^ 31 <= depth < 2 ^ 31.
Hypothesis HWM : Z.of_nat (length text) + Z.of_nat (length (concat (WriterValue.wind (negb (pretty =? 0)) depth))) + 1
  <= WMAX.

(* what the entry premise says of sp, the layout top and the fixed registers. B's stack numerals (lib/B/FSH_Base.v):
   STK_put = FRAME_put 112 + STK_fuzz_realloc, STK_indent = FRAME_indent 32 + STK_put (values computed, not pinned) *)
Lemma iSP : spZ regs mod 16 = 0 /\ alloc_ceiling + STK_indent <= spZ regs /\ spZ regs <= 2 ^ 47 /\
  ly_top ly <= 2 ^ 47 /\ STK_indent = ltac:(let v := eval vm_compute in STK_indent in exact v) /\
  STK_put = ltac:(let v := eval vm_compute in STK_put in exact v) /\
  YK0s.ret_ok (getr regs 1) /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B).
Proof.
destruct HPRE as [HAPU _]. pose proof (fsw_sp B _ ly S U W regs mem md ch HAPU) as (Hal16 & Hceil & H47 & HS0).
pose proof HAPU as (HAP & _ & _). pose proof HAP as (_ & Hra & _ & Hgp & Htp & Hstk & _).
pose proof Hstk as (_ & _ & _ & _ & _ & Hhi47 & _ & _ & Htop2).
repeat split; try assumption; try reflexivity; lia.
Qed.

(* the writer state after the pieces P *)
Definition iw (P : list (list Z)) : WriterApp.wst := WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) P.
Lemma iw_snoc : forall P bs, iw (P ++ [bs]) = WriterApp.put1 (iw P) bs.
Proof. intros P bs. unfold iw. rewrite WriterApp.putN_app. reflexivity. Qed.
Definition ifull : list (list Z) := WriterValue.wind (negb (pretty =? 0)) depth.
Lemma iw_cap0 : 0 <= cap.
Proof. pose proof HWO as (_ & _ & _ & _ & _ & Hc & _). lia. Qed.
Lemma iw_mono : forall P R, wcalls (iw P) <= wcalls (iw (P ++ R)) /\
  WriterApp.w_cap (iw P) <= WriterApp.w_cap (iw (P ++ R)) /\ cap <= WriterApp.w_cap (iw P).
Proof.
intros P R. pose proof iw_cap0 as Hc0.
assert (Hcp : cap <= WriterApp.w_cap (iw P))
  by exact (putN_cap_ge P (WriterApp.mkW failed text cap cnt fail []) ltac:(cbn [WriterApp.w_cap]; lia)).
unfold iw in *. rewrite WriterApp.putN_app.
split; [apply putN_calls_ge|]. split; [apply putN_cap_ge; lia | exact Hcp].
Qed.
Lemma iw_calls_snoc : forall P bs, wcalls (iw (P ++ [bs])) = wcalls (iw P) +
  wcalls (WriterApp.put1 (WriterApp.mkW (WriterApp.w_failed (iw P)) (WriterApp.w_text (iw P)) (WriterApp.w_cap (iw P))
            (WriterApp.w_cnt (iw P)) (WriterApp.w_fail (iw P)) []) bs).
Proof. intros P bs. rewrite iw_snoc. apply put1_calls_split. Qed.
(* indent's post count wevk cap adds up across the puts: at cap = 0 the first request is the cheap one, and it is
   made by the first put that requests (from then on the buffer exists, or the writer has failed and requests nothing
   more); at cap <> 0 every request costs 3 *)
Lemma iw_calls_snoc_l : forall P bs, WriterApp.w_calls (iw (P ++ [bs])) = WriterApp.w_calls (iw P) ++
  WriterApp.w_calls (WriterApp.put1 (WriterApp.mkW (WriterApp.w_failed (iw P)) (WriterApp.w_text (iw P))
     (WriterApp.w_cap (iw P)) (WriterApp.w_cnt (iw P)) (WriterApp.w_fail (iw P)) []) bs).
Proof. intros P bs. rewrite iw_snoc. apply put1_calls_app. Qed.
Lemma iw_wevk_step : forall P bs,
  wevk cap (iw P) + wevk (WriterApp.w_cap (iw P))
    (WriterApp.put1 (WriterApp.mkW (WriterApp.w_failed (iw P)) (WriterApp.w_text (iw P)) (WriterApp.w_cap (iw P))
       (WriterApp.w_cnt (iw P)) (WriterApp.w_fail (iw P)) []) bs) <= wevk cap (iw (P ++ [bs])).
Proof.
intros P bs. pose proof iw_cap0 as Hc0. pose proof (proj2 (proj2 (iw_mono P []))) as HcP.
rewrite !wevk_l, iw_calls_snoc_l.
destruct (Z.eqb_spec cap 0) as [E0 | N0];
  destruct (Z.eqb_spec (WriterApp.w_cap (iw P)) 0) as [E1 | N1]; cbv beta iota.
- apply wev0l_app_ge.
- assert (Hne : WriterApp.w_calls (iw P) <> []).
  { intros Hn. unfold iw in N1, Hn.
    pose proof (putN_cap_calls P (WriterApp.mkW failed text cap cnt fail []) ltac:(cbn [WriterApp.w_cap]; lia))
      as Hlt.
    rewrite Hn in Hlt. cbn [length WriterApp.w_calls] in Hlt. lia. }
  rewrite (wev0l_app_ne _ _ Hne). lia.
- lia.
- rewrite length_app. lia.
Qed.
Lemma iw_wevk_mono : forall Q R, wevk cap (iw Q) <= wevk cap (iw (Q ++ R)).
Proof.
intros Q R. assert (E : iw (Q ++ R) = WriterApp.putN (iw Q) R) by (unfold iw; apply WriterApp.putN_app).
rewrite E, !wevk_l. destruct (putN_calls_app R (iw Q)) as (X & EX). rewrite EX.
destruct (cap =? 0); cbv beta iota;
  [pose proof (wev0l_app_ge (WriterApp.w_calls (iw Q)) X); pose proof (wev0l_nonneg X); lia|].
rewrite length_app. lia.
Qed.

Definition iextra : list word := [getr regs 1; getr regs 8; getr regs 9; getr regs 18].
Definition ipost : world tfibsegs -> config -> Prop :=
  ind_post regs ly S U W mem md ot o pretty depth buf cap failed text live peak cnt fail.

(* what indent's own post needs of a state after the pieces P, the buffer at bufc *)
Definition iRI (P : list (list Z)) (Wc : world tfibsegs) lyc Sc Uc memC bufc : Prop :=
  wle W Wc /\ frames Sc = frames S /\ fs_heads B lyc Sc Uc /\
  (WriterApp.w_cap (iw P) <> 0 -> In (bufc - HEAD, HEAD) Uc) /\
  uswap U Uc buf bufc cap /\
  bswap (ablocks B ly S) (ablocks B lyc Sc) buf bufc cap (WriterApp.w_cap (iw P)) /\
  wbudget_kept S Sc failed cap cnt (WriterApp.w_failed (iw P)) (WriterApp.w_cap (iw P)) (WriterApp.w_cnt (iw P)) /\
  WriterApp.w_cnt (iw P) = cnt + wcalls (iw P) /\
  wout_ok B tfibsegs lyc Sc Wc memC o bufc (WriterApp.w_cap (iw P)) (WriterApp.w_failed (iw P)) (WriterApp.w_text (iw P)) /\
  wkeep tfibsegs W Wc mem memC (spZ regs) ot o 32 /\
  (exists peak1, peak <= peak1 <= Z.max peak (live - cap + WriterApp.w_cap (iw P)) /\
     fs_glob tfibsegs Wc memC (live + WriterApp.w_cap (iw P) - cap) peak1
       (WriterApp.w_cnt (iw P)) (WriterApp.w_fail (iw P))).
(* the frame's saved words *)
Definition iFR (Wc : world tfibsegs) memC : Prop :=
  val_mem tfibsegs (mrestrict (w_H Wc) memC) (spZ regs - 8) 8 (bv_unsigned (getr regs 1)) /\
  val_mem tfibsegs (mrestrict (w_H Wc) memC) (spZ regs - 16) 8 (bv_unsigned (getr regs 8)) /\
  val_mem tfibsegs (mrestrict (w_H Wc) memC) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) /\
  val_mem tfibsegs (mrestrict (w_H Wc) memC) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)).
(* the registers between the prologue and the epilogue: sp down by 32, s1 = o, the other callee-saved ones kept *)
Definition iRG (regsC : bvmap 5 word) : Prop :=
  spZ regsC = spZ regs - 32 /\ getr regsC 9 = w64 o /\
  (forall r : bv 5, acallee_saved (bv_unsigned r) -> bv_unsigned r <> 2 -> bv_unsigned r <> 8 -> bv_unsigned r <> 9 ->
     bv_unsigned r <> 18 -> getr regsC r = getr regs r).
Lemma iRG_call : forall regsC regs', iRG regsC -> aregs_preserved regsC regs' -> iRG regs'.
Proof.
intros regsC regs' (H2 & H9 & Hr) HP. split; [|split].
- unfold spZ. rewrite (fsw_pres regsC regs' 2%bv HP ltac:(ics)). exact H2.
- rewrite (fsw_pres regsC regs' 9%bv HP ltac:(ics)). exact H9.
- intros r Hc N2 N8 N9 N18. rewrite (fsw_pres regsC regs' r HP Hc). exact (Hr r Hc N2 N8 N9 N18).
Qed.

Lemma iRI_init : iRI [] W ly S U mem buf.
Proof.
pose proof HWO as (_ & _ & _ & _ & _ & Hc0 & _).
unfold iRI, iw. cbn [WriterApp.putN fold_left WriterApp.w_cap WriterApp.w_failed WriterApp.w_text WriterApp.w_cnt
  WriterApp.w_fail].
split; [apply wle_refl|]. split; [reflexivity|]. split; [exact HHD|]. split; [exact HHU|].
split; [left; split; reflexivity|]. split; [left; split; [reflexivity | split; reflexivity]|].
split; [exact (wbudget_kept_refl S failed cap cnt HCAP)|].
split; [unfold wcalls; cbn [WriterApp.w_calls length]; lia|]. split; [exact HWO|].
split; [intros a _ _; split; [reflexivity | tauto]|].
exists peak. split; [lia|]. replace (live + cap - cap) with live by lia. exact HGL.
Qed.

(* across a run that writes only the frame [sp - 32, sp) *)
Lemma iRI_sout : forall P (Wc : world tfibsegs) lyc Sc Uc m1 m2 bufc mx mdx,
  iRI P Wc lyc Sc Uc m1 bufc -> sout (spZ regs - 32) (spZ regs) m1 m2 -> AR tfibsegs B lyc Sc Wc mx mdx ->
  iRI P Wc lyc Sc Uc m2 bufc.
Proof.
intros P Wc lyc Sc Uc m1 m2 bufc mx mdx (Hwle & Hfr & Hhd & Hhu & Hus & Hbs & Hbk & Hcn & Hwo & Hwk & (pk & Hpk & Hgl))
  Hs HAR.
pose proof iSP as (Hal16 & Hceil & H47 & Htop47 & FS & _).
pose proof asan_consts as (C1 & _).
split; [exact Hwle|]. split; [exact Hfr|]. split; [exact Hhd|]. split; [exact Hhu|]. split; [exact Hus|].
split; [exact Hbs|].
split; [exact Hbk|]. split; [exact Hcn|].
assert (L1 : alloc_ceiling <= spZ regs - 32) by lia.
assert (L2 : spZ regs <= o) by exact HSO.
assert (L3 : o + 32 <= 2 ^ 64) by lia.
assert (L4 : 0 <= spZ regs) by lia.
assert (L5 : ot <= 2 ^ 64) by lia.
split; [exact (wout_ok_sout lyc Sc Wc m1 m2 o bufc _ _ _ (spZ regs - 32) (spZ regs) mx mdx HAR Hs L1 L2 L3 Hwo)|].
split; [exact (wkeep_sout_r W Wc mem m1 m2 (spZ regs - 32) (spZ regs) (spZ regs) ot o 32 Hwk Hs (Z.le_refl _) L4 L5)|].
exists pk. split; [exact Hpk|]. exact (fs_glob_below Wc m1 m2 _ _ _ _ (sout_same_below (spZ regs - 32) (spZ regs) m1 m2 Hs L1) Hgl).
Qed.

(* across one put: put's post composed onto the state before it *)
Lemma iRI_put : forall P bs (Wc : world tfibsegs) lyc Sc Uc memC mc mdc bufc (W' : world tfibsegs) ly' S' U' mem' m' md'
    buf' st'',
  iRI P Wc lyc Sc Uc memC bufc ->
  AR tfibsegs B lyc Sc Wc mc mdc -> AR tfibsegs B ly' S' W' m' md' ->
  upoison_ok B lyc Sc Uc -> upoison_ok B ly' S' U' ->
  wle Wc W' -> frames S' = frames Sc ->
  st'' = WriterApp.put1 (WriterApp.mkW (WriterApp.w_failed (iw P)) (WriterApp.w_text (iw P)) (WriterApp.w_cap (iw P))
           (WriterApp.w_cnt (iw P)) (WriterApp.w_fail (iw P)) []) bs ->
  uswap Uc U' bufc buf' (WriterApp.w_cap (iw P)) ->
  wout_ok B tfibsegs ly' S' W' mem' o buf' (WriterApp.w_cap st'') (WriterApp.w_failed st'') (WriterApp.w_text st'') ->
  wbudget_kept Sc S' (WriterApp.w_failed (iw P)) (WriterApp.w_cap (iw P)) (WriterApp.w_cnt (iw P))
    (WriterApp.w_failed st'') (WriterApp.w_cap st'') (WriterApp.w_cnt st'') ->
  bswap (ablocks B lyc Sc) (ablocks B ly' S') bufc buf' (WriterApp.w_cap (iw P)) (WriterApp.w_cap st'') ->
  wkeep tfibsegs Wc W' memC mem' (spZ regs - 32) ot o 32 ->
  cnt + wcalls (iw (P ++ [bs])) < 2 ^ 64 -> 0 <= cnt ->
  (exists peak1, peak <= peak1 <= Z.max peak (live - cap + WriterApp.w_cap st'') /\
     fs_glob tfibsegs W' mem' (live + WriterApp.w_cap st'' - cap) peak1 (WriterApp.w_cnt st'') (WriterApp.w_fail st'')) ->
  iRI (P ++ [bs]) W' ly' S' U' mem' buf'.
Proof.
intros P bs Wc lyc Sc Uc memC mc mdc bufc W' ly' S' U' mem' m' md' buf' st''
  (Hwle & Hfr & Hhd & Hhu & Hus & Hbs & Hbk & Hcn & Hwo & Hwk & _) HARc HAR' OKc OK' Hwle' Hfr' Est Hus' Hwo' Hbk' Hbs' Hwk'
  Hcnb Hcn0 Hpk'.
pose proof HWO as (_ & _ & _ & _ & _ & Hc0 & _).
pose proof (put1_fields (iw P) bs) as (F1 & F2 & F3 & F4 & F5). cbv zeta in F1, F2, F3, F4, F5.
rewrite <- Est in F1, F2, F3, F4, F5.
assert (Hcw : cap <= WriterApp.w_cap (iw P))
  by exact (putN_cap_ge P (WriterApp.mkW failed text cap cnt fail []) ltac:(cbn [WriterApp.w_cap]; lia)).
unfold iRI. rewrite iw_snoc, <- F1, <- F2, <- F3, <- F4, <- F5.
split; [exact (wle_trans _ _ _ _ Hwle Hwle')|]. split; [rewrite Hfr'; exact Hfr|].
split; [exact (fs_heads_put lyc Sc Uc Wc mc mdc memC ly' S' U' W' m' md' mem' o bufc _ _ _ o buf' _ _ _
  HARc HAR' OKc OK' Hhd Hus' Hbs' Hwo Hwo')|].
(* the head of the new buffer is in U': put's uswap keeps U and the buffer (the buffer then existed before, or both
   were none and stay none), or adds the new head *)
split.
{ intros Hc2. destruct Hus' as [[EU Eb] | [(Y1 & Y2 & EU & EU') | (Hc3 & EU')]].
  - rewrite EU, Eb. destruct (Z.eq_dec (WriterApp.w_cap (iw P)) 0) as [Hz | Hnz]; [|exact (Hhu Hnz)].
    exfalso. destruct (wout_buf _ _ _ _ _ _ _ _ _ Hwo) as [(_ & Hb0) | (Hc1 & _)]; [|lia].
    destruct (wout_buf _ _ _ _ _ _ _ _ _ Hwo') as [(Hc4 & _) | (_ & Hin')]; [lia|].
    rewrite Eb, Hb0 in Hin'. exact (low_block_absent ly' S' W' m' md' _ HAR' Hin').
  - rewrite EU'. apply in_or_app. right. apply in_or_app. right. left. reflexivity.
  - rewrite EU'. apply in_or_app. right. left. reflexivity. }
split.
{ apply (uswap_trans U Uc U' buf bufc buf' cap (WriterApp.w_cap (iw P)) Hus Hus').
  - intros X Y E. exact (U_nodup_mid lyc Sc Uc X _ Y OKc E).
  - intros Hc Hin. destruct (wout_buf _ _ _ _ _ _ _ _ _ Hwo) as [(_ & Hb0) | (Hc1 & _)]; [|lia].
    pose proof (U_low lyc Sc Uc Wc mc mdc _ HARc OKc Hin) as H. cbn [fst] in H. rewrite Hb0 in H. unfold HEAD in H. lia.
  - intros Hc. lia. }
split.
{ apply (bswap_trans _ _ _ buf bufc buf' cap (WriterApp.w_cap (iw P)) (WriterApp.w_cap st'') Hbs Hbs').
  - intros X Y E. exact (ablocks_nodup_mid lyc Sc Wc mc mdc X _ Y HARc E).
  - intros Hc Hin. destruct (wout_buf _ _ _ _ _ _ _ _ _ Hwo) as [(_ & Hb0) | (Hc1 & _)]; [|lia].
    rewrite Hb0 in Hin. exact (low_block_absent lyc Sc Wc mc mdc _ HARc Hin). }
split; [exact (wbudget_kept_trans _ _ _ _ _ _ _ _ _ _ _ _ Hbk Hbk')|].
split.
{ rewrite F4. pose proof (wcalls_nonneg (iw P)) as Hw0.
  assert (Hb64 : WriterApp.w_cnt (iw P) + (wcalls (WriterApp.put1 (iw P) bs) - wcalls (iw P)) < 2 ^ 64)
    by (rewrite <- iw_snoc; lia).
  rewrite (put1_cnt_step (iw P) bs ltac:(lia) Hb64). lia. }
split; [exact Hwo'|].
split; [exact (wkeep_trans W Wc W' mem memC mem' _ _ _ _ _ Hwk Hwk' ltac:(lia))|].
exact Hpk'.
Qed.

(* ---- one put call from indent, through PUT: put's premises from the state at the call, then the resumed state at
   the return address r (journal composed, frame read back from put's keep clause, invariant moved by one piece) ---- *)
Lemma ind_call : forall P bs s r (Wc : world tfibsegs) lyc Sc Uc regsC memC mdC bufc kc s0v,
  ajournal tfibsegs B (STK_indent + (ot - spZ regs)) ot (FS_PSTAT_FP ++ wbuf_fp buf cap) ly S W (unpoison U mem) md []
    lyc Sc Wc (unpoison Uc memC) mdC kc ->
  ARU tfibsegs B lyc Sc Uc Wc memC mdC ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H Wc) memC) ->
  iRI P Wc lyc Sc Uc memC bufc -> iFR Wc memC ->
  getr regsC 1 = w64 r -> 4096 <= r < 2 ^ 64 -> r mod 2 = 0 ->
  iRG regsC -> getr regsC 10 = w64 o -> getr regsC 11 = w64 s -> getr regsC 12 = w64 (Z.of_nat (length bs)) ->
  getr regsC 8 = w64 s0v -> 0 <= s0v < 2 ^ 64 -> (s0v < alloc_ceiling \/ ly_top ly - 16 <= s0v) ->
  In (s, bs) FS_RO_STRS -> s + Z.of_nat (length bs) + 1 <= SHADOW_OFF -> WriterSpec.bytes_ok bs ->
  Z.of_nat (length (WriterApp.w_text (iw P))) + Z.of_nat (length bs) + 1 <= WMAX ->
  kc <= wevk cap (iw P) -> (exists R, ifull = (P ++ [bs]) ++ R) ->
  (forall (W' : world tfibsegs) ly' S' U' regs' mem' md' buf' k', wle Wc W' -> k' <= wevk cap (iw (P ++ [bs])) ->
     ajournal tfibsegs B (STK_indent + (ot - spZ regs)) ot (FS_PSTAT_FP ++ wbuf_fp buf cap) ly S W (unpoison U mem) md []
       ly' S' W' (unpoison U' mem') md' k' ->
     ARU tfibsegs B ly' S' U' W' mem' md' ->
     arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W') mem') ->
     iRI (P ++ [bs]) W' ly' S' U' mem' buf' -> iFR W' mem' -> aregs_preserved regsC regs' ->
     st_ok tfibsegs (Ereg regs' iextra) (fss_ret r 32 ind_cs)
       (restrict (w_H W') (YK11.mkst regs' (Z_to_bv 64 r) mem' (YK11.seg_rom tfibsegs))) ->
     SRr tfibsegs W' (mkCfg (YK11.mkst regs' (Z_to_bv 64 r) mem' (YK11.seg_rom tfibsegs)) md') ipost) ->
  SRr tfibsegs Wc (cfg_at tfibsegs A_put regsC memC mdC) ipost.
Proof.
intros P bs s r Wc lyc Sc Uc regsC memC mdC bufc kc s0v HJc HARUc HROc HRI HFR H1 Hr Hr2 HRG H10c H11c H12c
  H8c Hs0 Hs0r HinS Hlow Hbo Htl Hkc Hpref K.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1 & _ & C3 & _).
pose proof iSP as (Hal16 & Hceil & H47 & Htop47 & FS & FP' & Hra & Hgp & Htp).
pose proof HWO as (_ & _ & _ & _ & _ & Hc0 & _).
pose proof HJc as (HARc & Hly & _ & _ & _ & Hfrs & Hnev & Hk0 & _ & _ & _ & _ & _ & Hpresc & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof HRI as (Hwle & Hfr & Hhd & HHUc & Hus & Hbs & Hbk & Hcn & Hwo & Hwk & (peakc & Hpk1 & Hglc)).
pose proof Hbk as (Hbk1 & Hbk2 & Hbk3).
pose proof HGL as (_ & _ & _ & _ & _ & _ & Hcnt0 & _).
pose proof (fsw_ARU B _ ly S U W regs mem md ch (proj1 HPRE)) as HARU0.
pose proof Hwo as (_ & _ & _ & _ & _ & Hcc & _).
destruct HRG as (Hspc & H9c & Hcs).
assert (Hgpc : getr regsC 3 = w64 (as_gp B)) by (rewrite (Hcs 3%bv ltac:(ics) ltac:(ics) ltac:(ics) ltac:(ics) ltac:(ics)); exact Hgp).
assert (Htpc : getr regsC 4 = w64 (as_tp B)) by (rewrite (Hcs 4%bv ltac:(ics) ltac:(ics) ltac:(ics) ltac:(ics) ltac:(ics)); exact Htp).
assert (HRA : raZ regsC = r) by (unfold raZ; rewrite H1; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
(* ---- put's premises ---- *)
assert (HPc : fpreU tfibsegs B STK_put lyc Sc Uc Wc regsC memC mdC []).
{ split; [|exact HROc]. split; [|split; [exact (proj1 (proj2 HARUc)) | exact (proj2 (proj2 HARUc))]].
  assert (E1 : spZ regsC = ot + (spZ regsC - ot)) by lia.
  assert (E2 : (spZ regsC - ot) mod 16 = 0) by lia.
  assert (E3 : spZ regsC - ot <= 0) by lia.
  assert (E4 : 0 <= STK_put) by lia.
  assert (E5 : STK_put - (spZ regsC - ot) <= STK_indent + (ot - spZ regs)) by lia.
  assert (E6 : YK0s.ret_ok (getr regsC 1))
    by (rewrite H1; apply ret_ok_even; unfold w64; rewrite unsigned_lit_small by lia; exact Hr2).
  assert (E7 : 4096 <= raZ regsC) by lia.
  assert (E8 : achain lyc (aview tfibsegs (w_H Wc) (unpoison Uc memC)) (spZ regsC) (s0Z regsC) []).
  { left. split; [|reflexivity]. unfold s0Z. rewrite H8c. unfold w64. rewrite unsigned_lit_small by lia.
    destruct Hs0r as [Hs0r | Hs0r]; [left; exact Hs0r | right; left; rewrite Etop; exact Hs0r]. }
  exact (afn_pre_at tfibsegs B _ ot _ ly S W (unpoison U mem) md [] lyc Sc Wc (unpoison Uc memC) mdC kc regsC STK_put
    (spZ regsC - ot) [] HJc E1 E2 E3 E4 E5 E6 E7 Hgpc Htpc E8). }
assert (HFRc : Z.of_nat (length (frames Sc)) <= FRL_CRT_CALLEE + 1) by (rewrite Hfrs; cbn [app]; lia).
assert (Hsoc : spZ regsC <= o) by lia.
assert (HTOPc : ot <= ly_top lyc) by (rewrite Etop; exact HTOP).
assert (HWINc : forall a, spZ regsC <= a < ot -> apresent (w_H Wc) memC a).
{ intros a Ha. apply (fsw_apresent_unpoison B lyc Sc Uc Wc memC mdC a HARUc); [lia|]. apply Hpresc. lia. }
destruct (ind_str_bytes lyc Sc Uc Wc memC mdC s bs HARUc HROc HinS Hlow) as (Hzb & Hs4096 & Hsac).
assert (Hsrc : wsrc_kept B tfibsegs lyc Sc Uc Wc memC bufc s bs)
  by (right; right; right; exists bs; split; [exact HinS | exact (Nat.le_succ_diag_r _)]).
assert (Hsr : 0 <= s /\ s + Z.of_nat (length bs) <= alloc_ceiling) by lia.
assert (Hsd : s + Z.of_nat (length bs) <= o \/ ot <= s) by (left; lia).
assert (Hcapc : WriterApp.w_cap (iw P) <= WMAX) by exact Hbk1.
assert (HCLc : WriterApp.w_cap (iw P) <= live + WriterApp.w_cap (iw P) - cap) by lia.
(* the frame-chain clause put reads at o, from indent's own (the two words lie in [sp, ot) outside the object, or
   are this frame's saved ra) *)
set (st2 := WriterApp.put1 (WriterApp.mkW (WriterApp.w_failed (iw P)) (WriterApp.w_text (iw P))
  (WriterApp.w_cap (iw P)) (WriterApp.w_cnt (iw P)) (WriterApp.w_fail (iw P)) []) bs) in *.
assert (HCHc : (o = spZ regsC + 8 /\ raZ regsC < alloc_ceiling) \/
  (spZ regsC + 16 <= o /\ exists ra nfp,
     rdword (aview tfibsegs (w_H Wc) (unpoison Uc memC)) (o - 8) = Some ra /\
     rdword (aview tfibsegs (w_H Wc) (unpoison Uc memC)) (o - 16) = Some nfp /\
     (ra < 4096 \/ nfp < alloc_ceiling))).
{ right. split; [lia|].
  destruct HCH as [(Eo & Hra8) | (Hgeo & ra0 & nfp0 & Hra0 & Hnfp0 & Hd)].
  - destruct HFR as (V1 & _).
    assert (HP8 : forall i, 0 <= i < 8 -> apresent (w_H Wc) memC (o - 8 + i)).
    { intros i Hi. apply (fsw_apresent_unpoison B lyc Sc Uc Wc memC mdC _ HARUc); [lia|]. apply Hpresc. lia. }
    destruct (rdword_present (w_H Wc) memC (o - 8) HP8) as (rv & Hrv).
    exists rv, (raZ regs). split; [|split; [|right; exact Hra8]].
    + rewrite (rdword_unpoison lyc Sc Uc Wc memC mdC (o - 8) HARUc ltac:(lia) ltac:(lia)). exact Hrv.
    + rewrite (rdword_unpoison lyc Sc Uc Wc memC mdC (o - 16) HARUc ltac:(lia) ltac:(lia)).
      apply (rdword_of_val_mem lyc (w_H Wc) memC (o - 16) (raZ regs) (u64_range _)).
      replace (o - 16) with (spZ regs - 8) by lia. exact V1.
  - rewrite (rdword_unpoison ly S U W mem md (o - 8) HARU0 ltac:(lia) ltac:(lia)) in Hra0.
    rewrite (rdword_unpoison ly S U W mem md (o - 16) HARU0 ltac:(lia) ltac:(lia)) in Hnfp0.
    exists ra0, nfp0. split; [|split; [|exact Hd]].
    + rewrite (rdword_unpoison lyc Sc Uc Wc memC mdC (o - 8) HARUc ltac:(lia) ltac:(lia)), <- Hra0.
      apply rdword_keep. intros i Hi. exact (proj1 (Hwk (o - 8 + i) ltac:(lia) ltac:(lia))).
    + rewrite (rdword_unpoison lyc Sc Uc Wc memC mdC (o - 16) HARUc ltac:(lia) ltac:(lia)), <- Hnfp0.
      apply rdword_keep. intros i Hi. exact (proj1 (Hwk (o - 16 + i) ltac:(lia) ltac:(lia))). }
(* the budget put spends is what this call's own model records *)
destruct Hpref as (R & Hpref).
assert (HWB' : wbudget_pre S cap cnt live (iw ifull)) by exact HWB.
pose proof (iw_mono (P ++ [bs]) R) as (Mc & Mcap & _). rewrite <- Hpref in Mc, Mcap.
assert (ECs : wcalls (iw (P ++ [bs])) = wcalls (iw P) + wcalls st2)
  by (subst st2; exact (iw_calls_snoc P bs)).
assert (ECap : WriterApp.w_cap st2 = WriterApp.w_cap (iw (P ++ [bs])))
  by (rewrite iw_snoc; subst st2; exact (proj1 (proj2 (proj2 (put1_fields (iw P) bs))))).
pose proof (wcalls_nonneg st2) as Hw2. pose proof (wcalls_nonneg (iw P)) as HwP.
pose proof HWB' as (Wev & Wlv & Wliv & Wcn).
(* the events: indent's own count so far plus this put's is within the count of the pieces up to this put *)
assert (Kst : wevk cap (iw P) + wevk (WriterApp.w_cap (iw P)) st2 <= wevk cap (iw (P ++ [bs])))
  by exact (iw_wevk_step P bs).
assert (Kmo : wevk cap (iw (P ++ [bs])) <= wevk cap (iw ifull)) by (rewrite Hpref; apply iw_wevk_mono).
assert (Hwbp : wbudget_pre Sc (WriterApp.w_cap (iw P)) (WriterApp.w_cnt (iw P))
  (live + WriterApp.w_cap (iw P) - cap) st2).
{ split; [lia|]. split; [lia|]. split; [lia|]. rewrite Hcn. lia. }
(* ---- the call ---- *)
eapply SRr_bind;
  [exact (PUT lyc Sc Uc Wc regsC memC mdC [] ot o s (Z.of_nat (length bs)) bufc (WriterApp.w_cap (iw P))
     (WriterApp.w_failed (iw P)) (WriterApp.w_text (iw P)) bs (live + WriterApp.w_cap (iw P) - cap) peakc
     (WriterApp.w_cnt (iw P)) (WriterApp.w_fail (iw P)) HPc Hhd HFRc H10c H11c H12c Hwo Hglc HHUc Hsoc HOT HOT16
     HTOPc HCHc HWINc Hzb Hsrc eq_refl Hbo Hsr Hsd Htl Hcapc HCLc Hwbp) |].
intros W2 c2 Hwle2 (st'' & buf' & U' & Est & Hus' & Hpost).
unfold wpost, fpostU in Hpost.
destruct Hpost as (ly' & S' & regs' & mem' & md' & Ec2 & HJp & OKp & POp & HPp &
  (Hwo' & Hbk' & Hbs' & Hwk' & (peak' & Hpk' & Hgl') & _)).
subst c2. rewrite H1.
pose proof HJp as (_ & _ & _ & _ & _ & Hfrs' & _).
cbn [app] in Hfrs'.
pose proof (wout_buf _ _ _ _ _ _ _ _ _ Hwo) as Hbufc.
assert (HFPc := ind_fp_cond ly S lyc Sc Wc (unpoison Uc memC) mdC buf cap bufc (WriterApp.w_cap (iw P)) HARc Hbs Hbufc).
assert (HCHK : Forall (YP09.chunk_ok tfibsegs (Ereg regs' iextra) (mrestrict (w_H Wc) memC) (spZ regsC)) ind_cs).
{ pose proof HFR as (V1 & V8 & V9 & V18). unfold ind_cs, iextra.
  constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
  - apply (chunk_ok_val tfibsegs _ _ _ 24 8%N (SOff 32 0) (bv_unsigned (getr regs 1)));
      [rewrite fsw_SOff0; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; cbn [nth];
       symmetry; apply Z_to_bv_bv_unsigned
      | apply u64_range | cbn; lia | replace (spZ regsC + 24) with (spZ regs - 8) by lia; exact V1].
  - apply (chunk_ok_val tfibsegs _ _ _ 16 8%N (SOff 33 0) (bv_unsigned (getr regs 8)));
      [rewrite fsw_SOff0; change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; cbn [nth];
       symmetry; apply Z_to_bv_bv_unsigned
      | apply u64_range | cbn; lia | replace (spZ regsC + 16) with (spZ regs - 16) by lia; exact V8].
  - apply (chunk_ok_val tfibsegs _ _ _ 8 8%N (SOff 34 0) (bv_unsigned (getr regs 9)));
      [rewrite fsw_SOff0; change 34%nat with (32 + 2)%nat; rewrite ew_Ereg_extra; cbn [nth];
       symmetry; apply Z_to_bv_bv_unsigned
      | apply u64_range | cbn; lia | replace (spZ regsC + 8) with (spZ regs - 24) by lia; exact V9].
  - apply (chunk_ok_val tfibsegs _ _ _ 0 8%N (SOff 35 0) (bv_unsigned (getr regs 18)));
      [rewrite fsw_SOff0; change 35%nat with (32 + 3)%nat; rewrite ew_Ereg_extra; cbn [nth];
       symmetry; apply Z_to_bv_bv_unsigned
      | apply u64_range | cbn; lia | replace (spZ regsC + 0) with (spZ regs - 32) by lia; exact V18]. }
assert (HKEEP : forall a, spZ regsC <= a < spZ regsC + 32 ->
  mbyte tfibsegs (mrestrict (w_H W2) mem') a = mbyte tfibsegs (mrestrict (w_H Wc) memC) a).
{ intros a Ha. exact (proj1 (Hwk' a ltac:(lia) ltac:(lia))). }
assert (HFP5 : fsw_fp_sub B ly S lyc Sc [] (FS_PSTAT_FP ++ wbuf_fp buf cap)
  (FS_PSTAT_FP ++ wbuf_fp bufc (WriterApp.w_cap (iw P)))).
{ intros a Ha. destruct (HFPc a Ha) as [H | [H | H]]; [left; exact H | right; left; exact H | right; right; left; exact H]. }
destruct (fsw_after_callFPU_win B (STK_indent + (ot - spZ regs)) ot (FS_PSTAT_FP ++ wbuf_fp buf cap) [] ly S U Wc mem md
  W lyc Sc Uc memC mdC kc STK_put (FS_PSTAT_FP ++ wbuf_fp bufc (WriterApp.w_cap (iw P))) ot 32 regsC ly' S' U' W2
  regs' mem' md' (wevk (WriterApp.w_cap (iw P)) st'') iextra ind_cs r Wc memC
  HJc HARUc HJp HFP5 OKp POp HPp ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(vm_compute; reflexivity) HCHK HKEEP) as (HJ2 & HARU2 & HS2).
assert (Hcl : ~ YI16.sink_open_fp (FS_PSTAT_FP ++ wbuf_fp bufc (WriterApp.w_cap (iw P)))).
{ apply sink_closed_pos. apply Forall_app. split; [unfold FS_PSTAT_FP; repeat constructor; cbn; lia|].
  unfold wbuf_fp. destruct (WriterApp.w_cap (iw P) =? 0) eqn:Ez; [constructor|].
  apply Z.eqb_neq in Ez. destruct Hbufc as [(Hz & _) | (_ & Hin)]; [lia|].
  destruct (fsw_ablock_low B lyc Sc Wc _ _ _ _ HARc Hin) as (A1 & _).
  constructor; [|constructor]. cbn [fst]. lia. }
assert (HFPI : forall a, in_roP tfibsegs FS_RLO FS_RHI a ->
  ~ inFP (FS_PSTAT_FP ++ wbuf_fp bufc (WriterApp.w_cap (iw P))) a).
{ intros a Hro Hfp. apply inFP_app in Hfp as [Hfp | Hfp]; [exact (pstat_not_roP a Hfp Hro)|].
  unfold wbuf_fp in Hfp. destruct (WriterApp.w_cap (iw P) =? 0) eqn:Ez; [destruct Hfp as (rr & [] & _)|].
  apply Z.eqb_neq in Ez. destruct Hbufc as [(Hz & _) | (_ & Hin)]; [lia|].
  destruct Hfp as (rr & [<- | []] & Hrr). cbn [fst snd] in Hrr.
  pose proof (req_size_pos (WriterApp.w_cap (iw P) + HEAD) ltac:(unfold HEAD; lia)) as Hrq.
  exact (blk_img tfibsegs B LAWS lyc Sc Wc (unpoison Uc memC) mdC _ _ a HARc Hin ltac:(unfold HEAD in *; lia)
    (in_roP_img a Hro)). }
pose proof (arodata_journal _ _ _ lyc Sc Uc Wc memC mdC ly' S' U' W2 mem' md' _ HJp HARUc HARU2 Hcl HFPI HROc) as HRO2.
assert (Hcge : WriterApp.w_cap (iw P) <= WriterApp.w_cap st'').
{ rewrite Est. exact (put1_cap_ge (WriterApp.mkW _ _ (WriterApp.w_cap (iw P)) _ _ []) bs ltac:(cbn [WriterApp.w_cap]; lia)). }
assert (HRI2 : iRI (P ++ [bs]) W2 ly' S' U' mem' buf').
{ apply (iRI_put P bs Wc lyc Sc Uc memC (unpoison Uc memC) mdC bufc W2 ly' S' U' mem' (unpoison U' mem') md' buf' st''
    HRI HARc (proj1 HARU2) (proj1 (proj2 HARUc)) OKp Hwle2 Hfrs' Est Hus' Hwo' Hbk' Hbs'
    ltac:(rewrite <- Hspc; exact Hwk') ltac:(lia) ltac:(lia)).
  exists peak'. split; [lia|].
  replace (live + WriterApp.w_cap st'' - cap) with (live + WriterApp.w_cap (iw P) - cap + WriterApp.w_cap st''
    - WriterApp.w_cap (iw P)) by lia.
  exact Hgl'. }
assert (HFR2 : iFR W2 mem').
{ pose proof HFR as (V1 & V8 & V9 & V18).
  assert (KK : forall a (n : nat) v, spZ regs - 32 <= a -> a + Z.of_nat n <= spZ regs ->
    val_mem tfibsegs (mrestrict (w_H Wc) memC) a n v -> val_mem tfibsegs (mrestrict (w_H W2) mem') a n v).
  { intros a n v Ha Hn Hv. apply (val_mem_mbyte_eq (mrestrict (w_H Wc) memC) (mrestrict (w_H W2) mem') a n v); [|exact Hv].
    intros k Hk. apply HKEEP. lia. }
  split; [apply KK; [lia | cbn; lia | exact V1]|].
  split; [apply KK; [lia | cbn; lia | exact V8]|].
  split; [apply KK; [lia | cbn; lia | exact V9]|].
  apply KK; [lia | cbn; lia | exact V18]. }
assert (ECs2 : wevk (WriterApp.w_cap (iw P)) st'' = wevk (WriterApp.w_cap (iw P)) st2) by (rewrite Est; reflexivity).
assert (Hk2 : kc + wevk (WriterApp.w_cap (iw P)) st'' <= wevk cap (iw (P ++ [bs])))
  by (clear - Hkc Kst ECs2; lia).
exact (K W2 ly' S' U' regs' mem' md' buf' (kc + wevk (WriterApp.w_cap (iw P)) st'') Hwle2 Hk2 HJ2 HARU2 HRO2 HRI2 HFR2
  HPp HS2).
Qed.

(* ---- registers and frame read off a symbolic state ---- *)
(* the callee-saved registers other than sp, s0, s1, s2 still hold the entry values when the state keeps them as atoms
   of an env whose registers already did *)
Lemma iRG_of_st : forall (H : word -> bool) regs0 xs ss ms,
  st_ok tfibsegs (Ereg regs0 xs) ss (restrict H ms) ->
  (forall r : bv 5, acallee_saved (bv_unsigned r) -> bv_unsigned r <> 2 -> bv_unsigned r <> 8 -> bv_unsigned r <> 9 ->
     bv_unsigned r <> 18 -> getr regs0 r = getr regs r) ->
  forallb (fun r : bv 5 => (bv_unsigned r =? 2) || (bv_unsigned r =? 8) || (bv_unsigned r =? 9) || (bv_unsigned r =? 18) ||
    sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) CALLEE_SAVED = true ->
  spZ (ms_regs ms) = spZ regs - 32 -> getr (ms_regs ms) 9 = w64 o -> iRG (ms_regs ms).
Proof.
intros H regs0 xs ss ms HS Hk Hchk Hsp H9. split; [exact Hsp|]. split; [exact H9|].
intros r Hc N2 N8 N9 N18. rewrite <- (Hk r Hc N2 N8 N9 N18).
pose proof (proj1 (forallb_forall _ _) Hchk r (cs_in r Hc)) as Hq. cbn beta in Hq.
apply Z.eqb_neq in N2, N8, N9, N18. rewrite N2, N8, N9, N18 in Hq. cbn [orb] in Hq. apply sv_eqb_eq in Hq.
apply (fsw_reg_atom H regs0 xs ss ms r r _ HS Hq). pose proof (bv_unsigned_in_range _ r) as Hr. rewrite Z2Nat.id; lia.
Qed.
(* the frame's saved words, from a state whose first region is the resumed frame (atoms 32..35 = iextra) *)
Lemma iFR_of_ret : forall (Wc : world tfibsegs) regs1 ss ms,
  st_ok tfibsegs (Ereg regs1 iextra) ss (restrict (w_H Wc) ms) ->
  nth_error (ss_mem ss) 0 = Some (fstk_ret 32 ind_cs) -> spZ regs1 = spZ regs - 32 ->
  iFR Wc (ms_mem ms).
Proof.
intros Wc regs1 ss ms HS Hn Hsp.
pose proof (fsw_region_nth _ _ _ 0 _ HS Hn) as HR0. cbn [ms_mem restrict] in HR0. unfold fstk_ret in HR0.
assert (E2 : bv_unsigned (ew (Ereg regs1 iextra) 2) = spZ regs - 32)
  by (rewrite (ew_Ereg_nat regs1 iextra 2 2%bv eq_refl); exact Hsp).
unfold iFR, ind_cs in *.
split; [|split; [|split]].
- replace (spZ regs - 8) with (spZ regs - 32 + 24) by lia.
  apply (fsw_field _ _ 2 _ _ _ _ _ _ 24 8%N (SOff 32 0) _ HR0 E2); [cbn; tauto | | apply u64_range | cbn; lia].
  rewrite fsw_SOff0. change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. cbn [nth iextra].
  symmetry. apply Z_to_bv_bv_unsigned.
- replace (spZ regs - 16) with (spZ regs - 32 + 16) by lia.
  apply (fsw_field _ _ 2 _ _ _ _ _ _ 16 8%N (SOff 33 0) _ HR0 E2); [cbn; tauto | | apply u64_range | cbn; lia].
  rewrite fsw_SOff0. change 33%nat with (32 + 1)%nat. rewrite ew_Ereg_extra. cbn [nth iextra].
  symmetry. apply Z_to_bv_bv_unsigned.
- replace (spZ regs - 24) with (spZ regs - 32 + 8) by lia.
  apply (fsw_field _ _ 2 _ _ _ _ _ _ 8 8%N (SOff 34 0) _ HR0 E2); [cbn; tauto | | apply u64_range | cbn; lia].
  rewrite fsw_SOff0. change 34%nat with (32 + 2)%nat. rewrite ew_Ereg_extra. cbn [nth iextra].
  symmetry. apply Z_to_bv_bv_unsigned.
- replace (spZ regs - 32) with (spZ regs - 32 + 0) by lia.
  apply (fsw_field _ _ 2 _ _ _ _ _ _ 0 8%N (SOff 35 0) _ HR0 E2); [cbn; tauto | | apply u64_range | cbn; lia].
  rewrite fsw_SOff0. change 35%nat with (32 + 3)%nat. rewrite ew_Ereg_extra. cbn [nth iextra].
  symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* ---- the return: the state at indent's ret, after the epilogue reloaded ra / s0 / s1 / s2 ---- *)
Lemma ind_ret : forall P (W1 : world tfibsegs) ly1 S1 U1 regs1 ssf msf md1 buf1 k1,
  P = WriterValue.wind (negb (pretty =? 0)) depth ->
  st_ok tfibsegs (Ereg regs1 iextra) ssf (restrict (w_H W1) msf) -> ss_resv ssf = None ->
  clookup fsw_wr_tbl (ss_pc ssf) = Some RET_WORD_r ->
  sr_get (ss_regs ssf) 1%bv = SOff 32 0 ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ssf) r) (ind_expect r)) CALLEE_SAVED = true ->
  iRG regs1 ->
  ajournal tfibsegs B (STK_indent + (ot - spZ regs)) ot (FS_PSTAT_FP ++ wbuf_fp buf cap) ly S W (unpoison U mem) md []
    ly1 S1 W1 (unpoison U1 (ms_mem msf)) md1 k1 -> k1 <= wevk cap (iw P) ->
  ARU tfibsegs B ly1 S1 U1 W1 (ms_mem msf) md1 ->
  iRI P W1 ly1 S1 U1 (ms_mem msf) buf1 ->
  SRr tfibsegs W1 (mkCfg msf md1) ipost.
Proof.
intros P W1 ly1 S1 U1 regs1 ssf msf md1 buf1 k1 HP HSf Hrv Hpc H1f Hregs HRG HJ Hk1 HARU HRI.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof iSP as (Hal16 & Hceil & H47 & Htop47 & FS & FP' & Hra & Hgp & Htp).
pose proof HWO as (_ & _ & _ & _ & _ & Hc0 & _).
pose proof HRI as (Hwle & Hfr & Hhd & Hhu & Hus & Hbs & Hbk & Hcn & Hwo & Hwk & Hpk).
pose proof Hwo as (_ & _ & _ & _ & _ & Hcc & _).
pose proof Hbk as (Hbk1 & Hbk2 & _).
destruct HRG as (Hspc & H9c & Hcs).
pose proof (fsw_reg_extra _ regs1 iextra _ msf 1%bv 0 HSf H1f) as R1F. unfold iextra in R1F. cbn [nth] in R1F.
eapply (SRr_ret_at tfibsegs fsw_wr_tbl fsw_wr_tbl_ok fs_wx); [exact HSf | exact Hrv | exact Hpc |].
intros mat.
assert (Hpc' : v_jalr (getr (ms_regs msf) 1) 0 = getr regs 1) by (rewrite R1F; exact Hra).
rewrite Hpc'.
exists (iw P), buf1, U1.
split; [unfold iw; rewrite HP; reflexivity|].
split; [exact Hus|].
unfold wpost, fpostU. do 5 eexists. split; [reflexivity|].
split.
{ apply (ajournal_materialize tfibsegs B LAWS fs_segs_low).
  eapply ajournal_mono_k; [exact HJ | exact Hk1]. }
split; [exact (proj1 (proj2 HARU))|]. split; [exact (proj2 (proj2 HARU))|].
split.
{ apply (fsw_preserved (w_H W1) (Ereg regs1 iextra) ssf msf regs ind_expect HSf Hregs).
  intros r Hr. cbv [CALLEE_SAVED In] in Hr.
  repeat (destruct Hr as [<-|Hr]); [..|destruct Hr];
  lazymatch goal with |- sv_denot _ (ind_expect ?q) = _ =>
    let e := eval vm_compute in (ind_expect q) in change (ind_expect q) with e end;
  first
  [ exact (fsw_extra_atom regs1 iextra 0) | exact (fsw_extra_atom regs1 iextra 1)
  | exact (fsw_extra_atom regs1 iextra 2) | exact (fsw_extra_atom regs1 iextra 3)
  | (eapply fsw_sp_back; rewrite (ew_Ereg_nat regs1 iextra 2 2%bv eq_refl); unfold spZ in *; lia)
  | (lazymatch goal with |- sv_denot _ (SOff ?n 0) = getr _ ?q =>
       rewrite fsw_SOff0, (ew_Ereg_nat regs1 iextra n q eq_refl); apply Hcs; ics end) ]. }
split; [exact Hwo|]. split; [exact Hbk|]. split; [exact Hbs|]. split; [exact Hwk|]. exact Hpk.
Qed.

Lemma wind_ne : pretty <> 0 -> WriterValue.wind (negb (pretty =? 0)) depth = [10] :: repeat [32; 32] (Z.to_nat depth).
Proof. intros Hp. unfold WriterValue.wind. rewrite (proj2 (Z.eqb_neq _ _) Hp). reflexivity. Qed.
(* the text budget of the next two-space put after the newline and k two-space puts *)
Lemma iw_budget : forall k, pretty <> 0 -> (k + 1 <= Z.to_nat depth)%nat ->
  Z.of_nat (length (WriterApp.w_text (iw ([10] :: repeat [32; 32] k)))) + Z.of_nat (length [32; 32]) + 1 <= WMAX.
Proof.
intros k Hp Hk. pose proof HWM as H. rewrite (wind_ne Hp) in H.
pose proof (putN_text_le ([10] :: repeat [32; 32] k) (WriterApp.mkW failed text cap cnt fail [])) as Ht.
unfold iw. cbn [concat length WriterApp.w_text] in *. rewrite length_app, concat_repeat2_len in *.
cbn [length] in *. lia.
Qed.
Lemma iw_budget0 : pretty <> 0 -> Z.of_nat (length (WriterApp.w_text (iw []))) + Z.of_nat (length [10]) + 1 <= WMAX.
Proof.
intros Hp. pose proof HWM as H. rewrite (wind_ne Hp) in H. unfold iw. cbn [WriterApp.putN fold_left WriterApp.w_text].
cbn [concat length] in *. rewrite length_app, concat_repeat2_len in H. cbn [length] in *. lia.
Qed.
(* the pieces still to come after the newline and k + 1 two-space puts: ind_call's prefix premise *)
Lemma ind_pref : forall k, pretty <> 0 -> (k + 1 <= Z.to_nat depth)%nat ->
  exists R, ifull = (([10] :: repeat [32; 32] k) ++ [[32; 32]]) ++ R.
Proof.
intros k Hp Hk. exists (repeat [32; 32] (Z.to_nat depth - (k + 1))).
unfold ifull. rewrite (wind_ne Hp). cbn [app]. f_equal.
rewrite repeat_snoc, <- repeat_app_z. f_equal. lia.
Qed.
Lemma ind_pref0 : pretty <> 0 -> exists R, ifull = ([] ++ [[10]]) ++ R.
Proof. intros Hp. exists (repeat [32; 32] (Z.to_nat depth)). unfold ifull. rewrite (wind_ne Hp). reflexivity. Qed.
(* the frame's saved words right after the prologue *)
Lemma iFR_of_entry : forall ss ms,
  st_ok tfibsegs (Ereg regs []) ss (restrict (w_H W) ms) ->
  nth_error (ss_mem ss) 0 = Some (YP09.mkRegion (Some 2%nat) (-32) 0 (-32) 0 ind_cs0) ->
  iFR W (ms_mem ms).
Proof.
intros ss ms HS Hn.
pose proof (fsw_region_nth _ _ _ 0 _ HS Hn) as HR0. cbn [ms_mem restrict] in HR0.
assert (E2 : bv_unsigned (ew (Ereg regs []) 2) = spZ regs) by (rewrite (ew_Ereg_nat regs [] 2 2%bv eq_refl); reflexivity).
unfold iFR, ind_cs0 in *.
split; [|split; [|split]].
- replace (spZ regs - 8) with (spZ regs + -8) by lia.
  apply (fsw_field _ _ 2 _ _ _ _ _ _ (-8) 8%N (SOff 1 0) _ HR0 E2); [cbn; tauto | | apply u64_range | cbn; lia].
  rewrite fsw_SOff0, (ew_Ereg_nat regs [] 1 1%bv eq_refl). symmetry. apply Z_to_bv_bv_unsigned.
- replace (spZ regs - 16) with (spZ regs + -16) by lia.
  apply (fsw_field _ _ 2 _ _ _ _ _ _ (-16) 8%N (SOff 8 0) _ HR0 E2); [cbn; tauto | | apply u64_range | cbn; lia].
  rewrite fsw_SOff0, (ew_Ereg_nat regs [] 8 8%bv eq_refl). symmetry. apply Z_to_bv_bv_unsigned.
- replace (spZ regs - 24) with (spZ regs + -24) by lia.
  apply (fsw_field _ _ 2 _ _ _ _ _ _ (-24) 8%N (SOff 9 0) _ HR0 E2); [cbn; tauto | | apply u64_range | cbn; lia].
  rewrite fsw_SOff0, (ew_Ereg_nat regs [] 9 9%bv eq_refl). symmetry. apply Z_to_bv_bv_unsigned.
- replace (spZ regs - 32) with (spZ regs + -32) by lia.
  apply (fsw_field _ _ 2 _ _ _ _ _ _ (-32) 8%N (SOff 18 0) _ HR0 E2); [cbn; tauto | | apply u64_range | cbn; lia].
  rewrite fsw_SOff0, (ew_Ereg_nat regs [] 18 18%bv eq_refl). symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* ---- the loop: back at 0x863b8 after a two-space put, s0 = m + 1 (m two-space puts still to come) ---- *)
Lemma ind_loop : forall m (W1 : world tfibsegs) ly1 S1 U1 regs1 mem1 md1 buf1 k1,
  pretty <> 0 -> Z.of_nat m + 1 <= depth ->
  ajournal tfibsegs B (STK_indent + (ot - spZ regs)) ot (FS_PSTAT_FP ++ wbuf_fp buf cap) ly S W (unpoison U mem) md []
    ly1 S1 W1 (unpoison U1 mem1) md1 k1 -> k1 <= wevk cap (iw ([10] :: repeat [32; 32] (Z.to_nat depth - m))) ->
  ARU tfibsegs B ly1 S1 U1 W1 mem1 md1 ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W1) mem1) ->
  iRI ([10] :: repeat [32; 32] (Z.to_nat depth - m)) W1 ly1 S1 U1 mem1 buf1 ->
  iRG regs1 -> getr regs1 8 = w64 (Z.of_nat m + 1) -> getr regs1 18 = w64 0x21300 ->
  st_ok tfibsegs (Ereg regs1 iextra) (fss_ret 0x863b8 32 ind_cs)
    (restrict (w_H W1) (YK11.mkst regs1 (Z_to_bv 64 0x863b8) mem1 (YK11.seg_rom tfibsegs))) ->
  SRr tfibsegs W1 (mkCfg (YK11.mkst regs1 (Z_to_bv 64 0x863b8) mem1 (YK11.seg_rom tfibsegs)) md1) ipost.
Proof.
induction m as [|m IH]; intros W1 ly1 S1 U1 regs1 mem1 md1 buf1 k1 Hpn Hm HJ Hk1 HARU HRO HRI HRG H8 H18 HS;
  pose proof (AR_laws_ok tfibsegs B) as LAWS;
  pose proof iSP as (Hal16 & Hceil & H47 & Htop47 & FS & FP' & Hra & Hgp & Htp);
  pose proof asan_consts as (C1 & _);
  pose proof HRG as (Hsp1 & H91 & Hcs1);
  set (E := Ereg regs1 iextra) in HS;
  assert (E2 : bv_unsigned (ew E 2) = spZ regs - 32)
    by (subst E; rewrite (ew_Ereg_nat regs1 iextra 2 2%bv eq_refl); exact Hsp1);
  (lazymatch type of H8 with getr _ _ = w64 ?v =>
     assert (E8 : ew E 8 = Z_to_bv 64 v) by (subst E; rewrite (ew_Ereg_nat regs1 iextra 8 8%bv eq_refl); exact H8);
     pose proof (U_addiw_m1 E 8 v E8 ltac:(lia)) as Ua end);
  (fsw_aj_runU fsw_wr_tbl_ok HS HJ HARU;
   [ cbn [fss_ret ss_mem];
     eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spZ regs - 32 - ot);
       [reflexivity | rewrite E2; lia | cbn; lia | cbn; lia | apply awr_ok_nil] |]);
  (assert (SO1 : sout (spZ regs - 32) (spZ regs) mem1 (ms_mem ms));
   [ cbn [fss_ret ss_mem] in HF; pose proof (sout_frame1 E _ _ _ HF) as Hso;
     cbn [fstk_ret YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hso; rewrite E2 in Hso;
     replace (spZ regs - 32 + 0) with (spZ regs - 32) in Hso by lia;
     replace (spZ regs - 32 + 32) with (spZ regs) in Hso by lia; exact Hso |]);
  (eapply SRr_sym_branch with (c := BC_NE) (a := SAluw ALU_ADD (SOff 8 0) (SLit (-1))) (b := SLit 0); [exact HS | |]).
- (* m = 0, taken: impossible *)
  intros Hb _. exfalso. replace (Z.of_nat 0 + 1 - 1) with 0 in Ua by lia.
  rewrite branch_ne_U, Ua, U_SLit in Hb. cbn in Hb. discriminate Hb.
- (* m = 0, not taken: the epilogue and the return *)
  intros _ HS2. clear HS.
  fsw_aj_runU fsw_wr_tbl_ok HS2 HJ HARU.
  { cbn [add_cond ss_mem].
    eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spZ regs - 32 - ot);
      [reflexivity | rewrite E2; lia | cbn; lia | cbn; lia | apply awr_ok_nil]. }
  assert (SO2 : sout (spZ regs - 32) (spZ regs) mem1 (ms_mem ms0)).
  { cbn [add_cond ss_mem] in HF0. pose proof (sout_frame1 E _ _ _ HF0) as Hso.
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hso. rewrite E2 in Hso.
    replace (spZ regs - 32 + 0) with (spZ regs - 32) in Hso by lia.
    replace (spZ regs - 32 + 32) with (spZ regs) in Hso by lia. exact (sout_trans _ _ _ _ _ SO1 Hso). }
  pose proof (iRI_sout _ W1 ly1 S1 U1 mem1 (ms_mem ms0) buf1 _ _ HRI SO2 (proj1 HARU)) as HRI2.
  apply (ind_ret ([10] :: repeat [32; 32] (Z.to_nat depth - 0)) W1 ly1 S1 U1 regs1 _ ms0 _ buf1 _
    ltac:(rewrite (wind_ne Hpn), Nat.sub_0_r; reflexivity) HS2 eq_refl ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HRG HJ Hk1 HARU HRI2).
- (* m = S m', taken: the next two-space put *)
  intros Hb HS2. clear HS. replace (Z.of_nat (Datatypes.S m) + 1 - 1) with (Z.of_nat (Datatypes.S m)) in Ua by lia.
  fsw_aj_run_toU fsw_wr_tbl_ok HS2 HJ HARU A_put.
  { cbn [add_cond ss_mem].
    eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spZ regs - 32 - ot);
      [reflexivity | rewrite E2; lia | cbn; lia | cbn; lia | apply awr_ok_nil]. }
  assert (SO2 : sout (spZ regs - 32) (spZ regs) mem1 (ms_mem ms0)).
  { cbn [add_cond ss_mem] in HF0. pose proof (sout_frame1 E _ _ _ HF0) as Hso.
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hso. rewrite E2 in Hso.
    replace (spZ regs - 32 + 0) with (spZ regs - 32) in Hso by lia.
    replace (spZ regs - 32 + 32) with (spZ regs) in Hso by lia. exact (sout_trans _ _ _ _ _ SO1 Hso). }
  pose proof (iRI_sout _ W1 ly1 S1 U1 mem1 (ms_mem ms0) buf1 _ _ HRI SO2 (proj1 HARU)) as HRI2.
  pose proof (arodata_below B W1 mem1 (ms_mem ms0) (sout_same_below _ _ _ _ SO2 ltac:(lia)) HRO) as HRO2.
  pose proof (fsw_reg_lit _ E _ ms0 1%bv 0x863b8 HS2 ltac:(vm_compute; reflexivity) ltac:(lia)) as R1.
  pose proof (fsw_reg_off _ E _ ms0 2%bv 2 0 (spZ regs - 32) HS2 ltac:(vm_compute; reflexivity) E2 ltac:(lia)) as R2.
  pose proof (fsw_reg_atom _ regs1 iextra _ ms0 9%bv 9%bv 9 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R9.
  pose proof (fsw_reg_atom _ regs1 iextra _ ms0 10%bv 9%bv 9 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R10.
  pose proof (fsw_reg_atom _ regs1 iextra _ ms0 11%bv 18%bv 18 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R11.
  pose proof (fsw_reg_lit _ E _ ms0 12%bv 2 HS2 ltac:(vm_compute; reflexivity) ltac:(lia)) as R12.
  pose proof (fsw_reg_atom _ regs1 iextra _ ms0 18%bv 18%bv 18 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R18.
  assert (R8 : getr (ms_regs ms0) 8 = w64 (Z.of_nat (Datatypes.S m))).
  { rewrite (st_ok_restrict_reg tfibsegs _ E _ ms0 8%bv HS2).
    lazymatch goal with |- sv_denot _ ?t = _ => let t' := eval vm_compute in t in change t with t' end.
    rewrite denot_lit_U, Ua. reflexivity. }
  assert (HRGc : iRG (ms_regs ms0)).
  { apply (iRG_of_st (w_H W1) regs1 iextra _ ms0 HS2 Hcs1 ltac:(vm_compute; reflexivity)).
    - unfold spZ at 1. rewrite R2. lia.
    - rewrite R9. exact H91. }
  pose proof (iFR_of_ret W1 regs1 _ ms0 HS2 ltac:(vm_compute; reflexivity) Hsp1) as HFR2.
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W1) E _ ms0 HS2 eq_refl). cbn [ss_pc].
  apply (ind_call ([10] :: repeat [32; 32] (Z.to_nat depth - Datatypes.S m)) [32; 32] 0x21300 0x863b8 W1 ly1 S1 U1 (ms_regs ms0)
    (ms_mem ms0) _ buf1 _ (Z.of_nat (Datatypes.S m)) HJ HARU HRO2 HRI2 HFR2 R1 ltac:(lia) eq_refl HRGc
    ltac:(rewrite R10; exact H91) ltac:(rewrite R11; exact H18) R12 R8 ltac:(lia) ltac:(left; lia)
    ltac:(unfold FS_RO_STRS; cbn [In]; repeat (first [left; reflexivity | right])) ltac:(unfold SHADOW_OFF; cbn; lia)
    ltac:(repeat constructor; lia) (iw_budget (Z.to_nat depth - Datatypes.S m) Hpn ltac:(lia)) Hk1
    (ind_pref (Z.to_nat depth - Datatypes.S m) Hpn ltac:(lia))).
  intros W' ly' S' U' regs' mem' md' buf' k' Hwle Hk' HJ' HARU' HRO' HRI' HFR' HP' HS'.
  assert (EP : ([10] :: repeat [32; 32] (Z.to_nat depth - Datatypes.S m)) ++ [[32; 32]] =
    [10] :: repeat [32; 32] (Z.to_nat depth - m)).
  { cbn [app]. rewrite repeat_snoc. f_equal. f_equal. lia. }
  rewrite EP in HRI', Hk'.
  apply (IH W' ly' S' U' regs' mem' md' buf' k' Hpn ltac:(lia) HJ' Hk' HARU' HRO' HRI' (iRG_call _ _ HRGc HP')).
  + rewrite (fsw_pres _ _ 8%bv HP' ltac:(ics)), R8. unfold w64. f_equal. lia.
  + rewrite (fsw_pres _ _ 18%bv HP' ltac:(ics)), R18. exact H18.
  + exact HS'.
- (* m = S m', not taken: impossible *)
  intros Hb _. exfalso. replace (Z.of_nat (Datatypes.S m) + 1 - 1) with (Z.of_nat (Datatypes.S m)) in Ua by lia.
  rewrite branch_ne_U, Ua, U_SLit in Hb. try (replace (zcanon 0) with 0 in Hb by reflexivity).
  destruct (Z.of_nat (Datatypes.S m) =? 0) eqn:Ez; [apply Z.eqb_eq in Ez; lia | discriminate Hb].
Qed.

(* ---- back at 0x8639c after the newline put: blez s0 (depth <= 0: return), else the first two-space put ---- *)
Lemma ind_r80 : forall (W1 : world tfibsegs) ly1 S1 U1 regs1 mem1 md1 buf1 k1,
  pretty <> 0 ->
  ajournal tfibsegs B (STK_indent + (ot - spZ regs)) ot (FS_PSTAT_FP ++ wbuf_fp buf cap) ly S W (unpoison U mem) md []
    ly1 S1 W1 (unpoison U1 mem1) md1 k1 -> k1 <= wevk cap (iw [[10]]) ->
  ARU tfibsegs B ly1 S1 U1 W1 mem1 md1 ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W1) mem1) ->
  iRI [[10]] W1 ly1 S1 U1 mem1 buf1 ->
  iRG regs1 -> getr regs1 8 = w64 depth ->
  st_ok tfibsegs (Ereg regs1 iextra) (fss_ret 0x8639c 32 ind_cs)
    (restrict (w_H W1) (YK11.mkst regs1 (Z_to_bv 64 0x8639c) mem1 (YK11.seg_rom tfibsegs))) ->
  SRr tfibsegs W1 (mkCfg (YK11.mkst regs1 (Z_to_bv 64 0x8639c) mem1 (YK11.seg_rom tfibsegs)) md1) ipost.
Proof.
intros W1 ly1 S1 U1 regs1 mem1 md1 buf1 k1 Hpn HJ Hk1 HARU HRO HRI HRG H8 HS.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof iSP as (Hal16 & Hceil & H47 & Htop47 & FS & FP' & Hra & Hgp & Htp).
pose proof asan_consts as (C1 & _).
pose proof HRG as (Hsp1 & H91 & Hcs1).
set (E := Ereg regs1 iextra) in HS.
assert (E2 : bv_unsigned (ew E 2) = spZ regs - 32)
  by (subst E; rewrite (ew_Ereg_nat regs1 iextra 2 2%bv eq_refl); exact Hsp1).
assert (E8 : ew E 8 = Z_to_bv 64 depth) by (subst E; rewrite (ew_Ereg_nat regs1 iextra 8 8%bv eq_refl); exact H8).
fsw_aj_runU fsw_wr_tbl_ok HS HJ HARU.
{ cbn [fss_ret ss_mem].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spZ regs - 32 - ot);
    [reflexivity | rewrite E2; lia | cbn; lia | cbn; lia | apply awr_ok_nil]. }
assert (SO1 : sout (spZ regs - 32) (spZ regs) mem1 (ms_mem ms)).
{ cbn [fss_ret ss_mem] in HF. pose proof (sout_frame1 E _ _ _ HF) as Hso.
  cbn [fstk_ret YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hso. rewrite E2 in Hso.
  replace (spZ regs - 32 + 0) with (spZ regs - 32) in Hso by lia.
  replace (spZ regs - 32 + 32) with (spZ regs) in Hso by lia. exact Hso. }
assert (Hsd : Sg E (SOff 8 0) = depth) by exact (S_atom E 8 depth E8 ltac:(lia)).
eapply SRr_sym_branch with (c := BC_GE) (a := SLit 0) (b := SOff 8 0); [exact HS | |].
- (* depth <= 0: the epilogue and the return *)
  intros Hb HS2. clear HS.
  rewrite branch_ge_S, Hsd, S_SLit in Hb. change (bv_swrap 64 0) with 0 in Hb.
  destruct (0 <? depth) eqn:Ed; [discriminate Hb|]. apply Z.ltb_ge in Ed.
  fsw_aj_runU fsw_wr_tbl_ok HS2 HJ HARU.
  { cbn [add_cond ss_mem].
    eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spZ regs - 32 - ot);
      [reflexivity | rewrite E2; lia | cbn; lia | cbn; lia | apply awr_ok_nil]. }
  assert (SO2 : sout (spZ regs - 32) (spZ regs) mem1 (ms_mem ms0)).
  { cbn [add_cond ss_mem] in HF0. pose proof (sout_frame1 E _ _ _ HF0) as Hso.
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hso. rewrite E2 in Hso.
    replace (spZ regs - 32 + 0) with (spZ regs - 32) in Hso by lia.
    replace (spZ regs - 32 + 32) with (spZ regs) in Hso by lia. exact (sout_trans _ _ _ _ _ SO1 Hso). }
  pose proof (iRI_sout _ W1 ly1 S1 U1 mem1 (ms_mem ms0) buf1 _ _ HRI SO2 (proj1 HARU)) as HRI2.
  apply (ind_ret [[10]] W1 ly1 S1 U1 regs1 _ ms0 _ buf1 _
    ltac:(rewrite (wind_ne Hpn); replace (Z.to_nat depth) with 0%nat by lia; reflexivity) HS2 eq_refl
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HRG HJ Hk1 HARU HRI2).
- (* depth > 0: the first two-space put, at 0x863b4 *)
  intros Hb HS2. clear HS.
  rewrite branch_ge_S, Hsd, S_SLit in Hb. change (bv_swrap 64 0) with 0 in Hb.
  destruct (0 <? depth) eqn:Ed; [|discriminate Hb]. apply Z.ltb_lt in Ed.
  fsw_aj_run_toU fsw_wr_tbl_ok HS2 HJ HARU A_put.
  { cbn [add_cond ss_mem].
    eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spZ regs - 32 - ot);
      [reflexivity | rewrite E2; lia | cbn; lia | cbn; lia | apply awr_ok_nil]. }
  assert (SO2 : sout (spZ regs - 32) (spZ regs) mem1 (ms_mem ms0)).
  { cbn [add_cond ss_mem] in HF0. pose proof (sout_frame1 E _ _ _ HF0) as Hso.
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hso. rewrite E2 in Hso.
    replace (spZ regs - 32 + 0) with (spZ regs - 32) in Hso by lia.
    replace (spZ regs - 32 + 32) with (spZ regs) in Hso by lia. exact (sout_trans _ _ _ _ _ SO1 Hso). }
  pose proof (iRI_sout _ W1 ly1 S1 U1 mem1 (ms_mem ms0) buf1 _ _ HRI SO2 (proj1 HARU)) as HRI2.
  pose proof (arodata_below B W1 mem1 (ms_mem ms0) (sout_same_below _ _ _ _ SO2 ltac:(lia)) HRO) as HRO2.
  pose proof (fsw_reg_lit _ E _ ms0 1%bv 0x863b8 HS2 ltac:(vm_compute; reflexivity) ltac:(lia)) as R1.
  pose proof (fsw_reg_off _ E _ ms0 2%bv 2 0 (spZ regs - 32) HS2 ltac:(vm_compute; reflexivity) E2 ltac:(lia)) as R2.
  pose proof (fsw_reg_atom _ regs1 iextra _ ms0 8%bv 8%bv 8 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R8.
  pose proof (fsw_reg_atom _ regs1 iextra _ ms0 9%bv 9%bv 9 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R9.
  pose proof (fsw_reg_atom _ regs1 iextra _ ms0 10%bv 9%bv 9 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R10.
  pose proof (fsw_reg_lit _ E _ ms0 11%bv 0x21300 HS2 ltac:(vm_compute; reflexivity) ltac:(lia)) as R11.
  pose proof (fsw_reg_lit _ E _ ms0 12%bv 2 HS2 ltac:(vm_compute; reflexivity) ltac:(lia)) as R12.
  pose proof (fsw_reg_lit _ E _ ms0 18%bv 0x21300 HS2 ltac:(vm_compute; reflexivity) ltac:(lia)) as R18.
  assert (HRGc : iRG (ms_regs ms0)).
  { apply (iRG_of_st (w_H W1) regs1 iextra _ ms0 HS2 Hcs1 ltac:(vm_compute; reflexivity)).
    - unfold spZ at 1. rewrite R2. lia.
    - rewrite R9. exact H91. }
  pose proof (iFR_of_ret W1 regs1 _ ms0 HS2 ltac:(vm_compute; reflexivity) Hsp1) as HFR2.
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W1) E _ ms0 HS2 eq_refl). cbn [ss_pc].
  apply (ind_call [[10]] [32; 32] 0x21300 0x863b8 W1 ly1 S1 U1 (ms_regs ms0) (ms_mem ms0) _ buf1 _ depth
    HJ HARU HRO2 HRI2 HFR2 R1 ltac:(lia) eq_refl HRGc ltac:(rewrite R10; exact H91) R11 R12
    ltac:(rewrite R8; exact H8) ltac:(lia) ltac:(left; lia)
    ltac:(unfold FS_RO_STRS; cbn [In]; repeat (first [left; reflexivity | right])) ltac:(unfold SHADOW_OFF; cbn; lia)
    ltac:(repeat constructor; lia) (iw_budget 0 Hpn ltac:(lia)) Hk1 (ind_pref 0 Hpn ltac:(lia))).
  intros W' ly' S' U' regs' mem' md' buf' k' Hwle Hk' HJ' HARU' HRO' HRI' HFR' HP' HS'.
  assert (EP : [[10]] ++ [[32; 32]] = [10] :: repeat [32; 32] (Z.to_nat depth - (Z.to_nat depth - 1))).
  { replace (Z.to_nat depth - (Z.to_nat depth - 1))%nat with 1%nat by lia. reflexivity. }
  rewrite EP in HRI', Hk'.
  apply (ind_loop (Z.to_nat depth - 1) W' ly' S' U' regs' mem' md' buf' k' Hpn ltac:(lia) HJ' Hk' HARU' HRO' HRI'
    (iRG_call _ _ HRGc HP')).
  + rewrite (fsw_pres _ _ 8%bv HP' ltac:(ics)), R8, H8. unfold w64. f_equal. lia.
  + rewrite (fsw_pres _ _ 18%bv HP' ltac:(ics)), R18. reflexivity.
  + exact HS'.
Qed.

(* ---- pretty <> 0, from the entry: the prologue, beqz a1 not taken, the newline put at 0x86398 ---- *)
Lemma ind_arm1 : pretty <> 0 -> SRr tfibsegs W (cfg_at tfibsegs A_indent regs mem md) ipost.
Proof.
intros Hpn.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof fs_segs_low as HSL. pose proof fs_wx as HWX.
pose proof iSP as (Hal16 & Hceil & H47 & Htop47 & FS & FP' & Hra & Hgp & Htp).
pose proof asan_consts as (C1 & _).
pose proof HPRE as [HAPU HRO].
pose proof HAPU as (HAP & _ & _).
pose proof (fsw_entry B STK_indent 32 ly S U W regs mem md ch A_indent HAPU ltac:(lia) ltac:(vm_compute; reflexivity))
  as HS.
pose proof (fsw_ajournal_init_ot B STK_indent (FS_PSTAT_FP ++ wbuf_fp buf cap) ly S U W regs mem md ch ot HAPU
  ltac:(lia) HOT16 HTOP HWIN) as HJ.
pose proof (fsw_ARU B _ ly S U W regs mem md ch HAPU) as HARU.
set (E := Ereg regs []) in HS.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs [] 2 2%bv eq_refl); reflexivity).
assert (E11 : ew E 11 = Z_to_bv 64 pretty) by (subst E; rewrite (ew_Ereg_nat regs [] 11 11%bv eq_refl); exact H11).
unfold cfg_at. change (w64 A_indent) with (Z_to_bv 64 A_indent).
fsw_aj_runU fsw_wr_tbl_ok HS HJ HARU.
{ change (ss_mem (fss0 A_indent 32)) with [fstk 32].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spZ regs - ot);
    [reflexivity | rewrite Usp; lia | cbn; lia | cbn; lia | apply awr_ok_nil]. }
assert (SO1 : sout (spZ regs - 32) (spZ regs) mem (ms_mem ms)).
{ change (frame_of E [fstk 32] mem (ms_mem ms)) in HF. pose proof (sout_frame1 E _ _ _ HF) as H.
  cbn [fstk YP09.r_base YP09.r_wlo YP09.r_whi base_val] in H. rewrite Usp in H.
  replace (spZ regs + -32) with (spZ regs - 32) in H by lia. rewrite Z.add_0_r in H. exact H. }
eapply SRr_sym_branch with (c := BC_EQ) (a := SOff 11 0) (b := SLit 0); [exact HS | |].
{ intros Hb _. exfalso. rewrite branch_eq_U in Hb.
  rewrite (U_atom E 11 pretty E11 ltac:(lia)), U_SLit in Hb. change (zcanon 0) with 0 in Hb.
  apply Z.eqb_eq in Hb. exact (Hpn Hb). }
intros _ HS2. clear HS.
(* ---- not taken: 0x86380 .. the jal put at 0x86398 ---- *)
fsw_aj_run_toU fsw_wr_tbl_ok HS2 HJ HARU A_put.
{ cbn [add_cond ss_mem].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spZ regs - ot);
    [reflexivity | rewrite Usp; lia | cbn; lia | cbn; lia | apply awr_ok_nil]. }
assert (SO2 : sout (spZ regs - 32) (spZ regs) mem (ms_mem ms0)).
{ cbn [add_cond ss_mem] in HF0. pose proof (sout_frame1 E _ _ _ HF0) as H.
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in H. rewrite Usp in H.
  replace (spZ regs + -32) with (spZ regs - 32) in H by lia. rewrite Z.add_0_r in H.
  exact (sout_trans _ _ _ _ _ SO1 H). }
pose proof (iRI_sout [] W ly S U mem (ms_mem ms0) buf _ _ iRI_init SO2 (proj1 HARU)) as HRI2.
pose proof (arodata_below B W mem (ms_mem ms0) (sout_same_below _ _ _ _ SO2 ltac:(lia)) HRO) as HRO2.
pose proof (fsw_reg_lit _ E _ ms0 1%bv 0x8639c HS2 ltac:(vm_compute; reflexivity) ltac:(lia)) as R1.
pose proof (fsw_reg_off _ E _ ms0 2%bv 2 (-32) (spZ regs) HS2 ltac:(vm_compute; reflexivity) Usp ltac:(lia)) as R2.
pose proof (fsw_reg_atom _ regs [] _ ms0 8%bv 12%bv 12 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R8.
pose proof (fsw_reg_atom _ regs [] _ ms0 9%bv 10%bv 10 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R9.
pose proof (fsw_reg_atom _ regs [] _ ms0 10%bv 10%bv 10 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R10.
pose proof (fsw_reg_lit _ E _ ms0 11%bv 0x21040 HS2 ltac:(vm_compute; reflexivity) ltac:(lia)) as R11.
pose proof (fsw_reg_lit _ E _ ms0 12%bv 1 HS2 ltac:(vm_compute; reflexivity) ltac:(lia)) as R12.
assert (HRGc : iRG (ms_regs ms0)).
{ apply (iRG_of_st (w_H W) regs [] _ ms0 HS2 ltac:(intros; reflexivity) ltac:(vm_compute; reflexivity)).
  - unfold spZ at 1. rewrite R2. lia.
  - rewrite R9. exact H10. }
pose proof (iFR_of_entry _ ms0 HS2 ltac:(vm_compute; reflexivity)) as HFR2.
set (s0v := bv_unsigned (w64 depth)).
assert (Hs0 : 0 <= s0v < 2 ^ 64) by apply u64_range.
assert (Es0 : s0v = depth mod 2 ^ 64) by (subst s0v; unfold w64; rewrite Z_to_bv_unsigned; reflexivity).
assert (R8' : getr (ms_regs ms0) 8 = w64 s0v) by (rewrite R8, H12; subst s0v; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (Hs0r : s0v < alloc_ceiling \/ ly_top ly - 16 <= s0v).
{ rewrite Es0. destruct (Z_lt_le_dec depth 0) as [Hn | Hp].
  - right. replace (depth mod 2 ^ 64) with (depth + 2 ^ 64); [lia|].
    symmetry. rewrite <- (Z.mod_add depth 1 (2 ^ 64)) by lia. apply Z.mod_small. lia.
  - left. rewrite Z.mod_small by lia. lia. }
assert (Hk0 : 0 <= wevk cap (iw [])) by apply wevk_nonneg.
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E _ ms0 HS2 eq_refl). cbn [ss_pc].
apply (ind_call [] [10] 0x21040 0x8639c W ly S U (ms_regs ms0) (ms_mem ms0) _ buf _ s0v
  HJ HARU HRO2 HRI2 HFR2 R1 ltac:(lia) eq_refl HRGc ltac:(rewrite R10; exact H10) R11 R12 R8' Hs0 Hs0r
  ltac:(unfold FS_RO_STRS; cbn [In]; repeat (first [left; reflexivity | right])) ltac:(unfold SHADOW_OFF; cbn; lia)
  ltac:(repeat constructor; lia) (iw_budget0 Hpn) Hk0 (ind_pref0 Hpn)).
intros W' ly' S' U' regs' mem' md' buf' k' Hwle Hk' HJ' HARU' HRO' HRI' HFR' HP' HS'.
apply (ind_r80 W' ly' S' U' regs' mem' md' buf' k' Hpn HJ' Hk' HARU' HRO' HRI' (iRG_call _ _ HRGc HP')).
- rewrite (fsw_pres _ _ 8%bv HP' ltac:(ics)), R8. exact H12.
- exact HS'.
Qed.

End L.

(* ================= indent_spec ================= *)
Theorem indent_proof : @indent_spec fx rc SK B tfibsegs.
Proof.
intros ly S U W regs mem md ch ot o pretty depth buf cap failed text live peak cnt fail HPRE HHD HFRL H10 H11 H12
  HPR HDEP HWO HGL HHU HSO HOT HOT16 HTOP HCH HWIN HWM HCAP HCL HWB.
destruct (Z.eq_dec pretty 0) as [Hp0 | Hp0].
- exact (indent_arm0 ly S U W regs mem md ch ot o pretty depth buf cap failed text live peak cnt fail HPRE H11 Hp0 HWO HGL
    HSO HOT HOT16 HTOP HWIN HCAP).
- (* ind_arm1 takes the 20 entry variables, then the Section L hypotheses its proof uses *)
  apply (ind_arm1 ly S U W regs mem md ch ot o pretty depth buf cap failed text live peak cnt fail); assumption.
Qed.

End W.
