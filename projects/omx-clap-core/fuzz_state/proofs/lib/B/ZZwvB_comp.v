(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACer.v, with its module paths and module names changed; 1338 of its 1373 lines of code are new or changed and 261 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_K.v, with its module paths and module names changed; 486 of its 581 lines of code are new or changed and 1278 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) twin of lib/A/ZZwv_comp.v (a working branch
   1a5dc5b2e7c): same lemma names, statements and proofs; imports point at lib/B's image files and walk kit (YB1v, YB1w,
   FSH_Base, FSPstat, FSW_K, FSW_ret, FSW_K3, FSH_Fn_writer); the image-agnostic FSupoison, FSupoisonU, FSH_YC20, FSH_Gen
   stay lib/A's. lib/B has no FSW_writer_kit: its two lemmas this file uses (fs_heads_uswap, uswap_new_head) are copied
   below, statements and proofs verbatim, from lib/A/FSW_writer_kit.v at 1a5dc5b2e7c (they are image-agnostic: no
   segment, address or frame in them); zz_eq_dec is Reusable/YI04.v's.
   rule 24: proves no function (kind: segment lemma) - the container arms of write_value B. *)
(*   fs WRITER, write_value's CONTAINER arms (fs.asan-ubsan 0x84010, preset_file.c:525-575), the COMPOSITION half:
   what chaining several writer calls (put, indent, put_string, write_value) inside one function body gives,
   over the live definitions of lib/B/FSH_Fn_writer.v (wcalls :98, wev0 :107, wevk :120, wbudget_pre :123,
   wbudget_kept :140, uswap :165, wbuf_fp :173, bswap :179, WMAX / bsz :67,87), lib/A/FSH_Gen.v (HEAD :56,
   wkeep :236), lib/A/FSupoisonU.v (fs_heads :119), lib/A/FSupoison.v (upoison_ok / ARU :27,34), lib/B/FSW_K3.v
   (fsw_fp_sub :263) and lib/Prog/WriterApp.v (wst / put1 / putN).
   No walk, no engine run, no function contract: a caller `apply`s these at each call site of an arm.

   Reused, not copied (LOOKUP RULE, donors by import): lib/Prog/WriterRet.v:73 putN_cap (wv_cap_mono), :88
   putN_text (wv_room_mid), :31 putN_calls_ex (the calls prefix), :117 in_mid, :163 newcap_pos (zzwv_put1_inv0);
   lib/Prog/WriterApp.v:40 putN_failed (wv_wevk_split); lib/Reusable/YI04.v zz_eq_dec (wv_heads_swap);
   lib/Reusable/YG0d.v al_blocks through YG0q.v
   AR_laws_ok (a live block starts at 4096 or above, and the live blocks are pairwise disjoint and of positive
   request size, so a list of live blocks carries no repeat and splits at a live block in one way only);
   lib/Reusable/YI04.v inFP_app. Copied (lib/B has no donor module): fs_heads_uswap / uswap_new_head, lib/A/FSW_writer_kit.v.
   Templated, cited and not imported: zzwv_split_uniq follows FSW_pj_write.v
   pjw_f_split_uniq (a working branch b6c5b22a453 :1534-1546), and zzwv_put1_inv0's grow arm the
   same file's pjw_m_newcap_pos (:721-727), for which WriterRet.newcap_pos is the imported donor.

   Where a statement differs from the form first asked for, it is because that form is false or because it
   needs a fact the caller already holds at the MIDDLE state (never a new assumption):
   - wv_cap_mono needs `0 <= w_cap st`: newcap doubles, so from a negative cap the cap FALLS (the donor
     WriterRet.putN_cap carries the same premise). wout_ok (lib/B/FSH_Fn_writer.v:146) gives it.
   - wv_cnt_calls needs `w_calls st = []`: with calls already recorded the equation counts them twice
     (P = [] and w_calls st = [c] make the two sides differ by one). The composition idiom starts each call's
     model state at `wv_rst s1`, whose calls are [], so the premise is closed by reflexivity.
   - wv_wevk_split / wv_wevk_mono need `w_calls st = []` and `0 <= w_cap st`. At cap <> 0 both sides are
     EV_fuzz_realloc per request (the cap only grows, wv_cap_mono) and the requests split (wv_putN_split). At
     cap = 0 the cheap first request is charged once: zzwv_putN_inv0 says that at the boundary either no request
     was made yet (so the count restarts there at cap 0), or the buffer exists (every later request costs
     EV_fuzz_realloc), or `failed` is set (no later request). wv_wevk_nonneg holds for every cap and state.
   - wv_budget_pre_prefix needs `0 <= cap` (same cap monotonicity); its event clause is wv_wevk_mono.
   - wv_budget_pre_mid follows wbudget_pre's cap-aware event count: premise 1 is `0 <= cap`, and the middle
     state's events are bounded by `wevk cap` of the first piece; the event clause is wv_wevk_split.
   - wv_uswap_trans needs AR at the middle state and `0 <= c0 <= c1`: with the first step a no-op and the
     second allocating from scratch, `c1 = 0` has to push back to `c0 = 0`, which is cap monotonicity; and the
     appended head (0 - HEAD, HEAD) is ruled out by AR, which fs_heads alone does not give.
   - wv_bswap_trans composes two calls of the realloc shape (the new block anywhere in the list): when the
     second call reallocates the middle buffer, AR at the middle state makes the two splits of the middle list
     at that buffer equal (zzwv_ab_split_uniq), so the second call's C-lists rejoin the first call's old list.
     Its `(c1 <> 0 -> In (b1 - HEAD, c1 + HEAD) A1)`, `0 <= c1` and `0 <= c2` premises turn out not to be
     needed (the membership comes out of each bswap shape), and are kept only so that the caller's application
     does not change.
   - wv_fp_sub_swap needs AR at the middle state (the new buffer's block is live there, and live blocks do not
     repeat, which is what makes the block either the old buffer or a tmp block).
   - wv_wkeep_mono RAISES the window's start: wkeep's clause runs over [s, ot), so the low start is the strong
     one and `sp <= sp' -> wkeep .. sp .. -> wkeep .. sp' ..` is the direction that holds.
   LOOKUP RULE record: the 42 names A defines here are A's lookup (lib/A/ZZwv_comp.v's header at 1a5dc5b2e7c, the same
   names); this twin defines no name of its own beyond them except the two lib/A/FSW_writer_kit.v copies above. *)
(* Modified by Theorem Labs, 2026-10-29: lib/B now has FSW_writer_kit.v (a Theorem Labs lane): fs_heads_uswap and uswap_new_head are Required from it (same statements); the copies described above are removed. *)

From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSPstat FSW_K FSW_ret FSW_K3 FSH_Fn_writer.
(* lib/Prog modules are Required, never Imported (a Theorem Labs lane 21:43Z) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterApp WriterRet.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import FSW_writer_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance
   resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* fs_heads_uswap / uswap_new_head come from lib/B/FSW_writer_kit.v (a Theorem Labs lane, on a working branch), Required above. *)

Section C. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}. Variable B : asyms.

(* ================= list facts the two swap relations need ================= *)

(* a list that carries the same element twice relates that element to itself; with zdisjoint and a range of
   positive length that is a contradiction *)
Lemma zzwv_pairwise_dup : forall {X : Type} (R : X -> X -> Prop) (l1 l2 : list X) (x : X),
  pairwise R (l1 ++ x :: l2) -> In x (l1 ++ l2) -> R x x.
Proof.
  intros X R l1. induction l1 as [|y l1 IH]; intros l2 x HP Hin.
  - cbn in HP. destruct HP as [HF _]. rewrite Forall_forall in HF. apply HF. exact Hin.
  - cbn in HP. destruct HP as [HF HP]. cbn in Hin. destruct Hin as [-> | Hin].
    + rewrite Forall_forall in HF. apply HF. apply in_or_app. right. left. reflexivity.
    + exact (IH l2 x HP Hin).
Qed.

(* removing one occurrence of x from l ++ [x] either removes the appended one, or x was already in l *)
Lemma zzwv_app_last_split : forall {X : Type} (l la lb : list X) (x : X),
  la ++ x :: lb = l ++ [x] -> (la = l /\ lb = []) \/ In x l.
Proof.
  intros X l la. revert l. induction la as [|y la IH]; intros l lb x E.
  - destruct l as [|z l].
    + cbn in E. injection E as E. left. split; [reflexivity | exact E].
    + cbn in E. injection E as E1 E2. right. left. symmetry. exact E1.
  - destruct l as [|z l].
    + cbn in E. injection E as E1 E2. exfalso. destruct la; discriminate E2.
    + cbn in E. injection E as E1 E2. destruct (IH l lb x E2) as [(-> & ->) | Hin].
      * left. split; [rewrite E1; reflexivity | reflexivity].
      * right. right. exact Hin.
Qed.

(* an element dropped into the middle of a list keeps every element the list had *)
Lemma zzwv_in_ins : forall {X : Type} (C1 C2 : list X) (x y : X), In y (C1 ++ C2) -> In y (C1 ++ x :: C2).
Proof.
  intros X C1 C2 x y H. apply in_app_or in H. apply in_or_app.
  destruct H as [H | H]; [left; exact H | right; right; exact H].
Qed.

(* an element whose image overlaps itself sits at one place only in a list whose images are pairwise R-related
   (template, cited and not imported: FSW_pj_write.v pjw_f_split_uniq, a working branch
   b6c5b22a453 :1534-1546, there for heads; here through a map, for live blocks) *)
Lemma zzwv_split_uniq : forall {X Y : Type} (f : X -> Y) (R : Y -> Y -> Prop) (x : X) (l1 l2 l3 l4 : list X),
  pairwise R (map f (l1 ++ x :: l2)) -> ~ R (f x) (f x) -> l1 ++ x :: l2 = l3 ++ x :: l4 -> l1 = l3 /\ l2 = l4.
Proof.
  intros X Y f R x l1. induction l1 as [|u l1 IH]; intros l2 l3 l4 HP Hx E; destruct l3 as [|v l3];
    cbn [app map pairwise] in HP, E.
  - injection E as E. split; [reflexivity | exact E].
  - injection E as E1 E2. subst v. exfalso. apply Hx. destruct HP as [HF _]. rewrite Forall_forall in HF.
    apply HF. rewrite E2. apply in_map. apply in_or_app. right. left. reflexivity.
  - injection E as E1 E2. subst u. exfalso. apply Hx. destruct HP as [HF _]. rewrite Forall_forall in HF.
    apply HF. apply in_map. apply in_or_app. right. left. reflexivity.
  - injection E as E1 E2. subst v. destruct HP as [_ HP].
    destruct (IH l2 l3 l4 HP Hx E2) as [E3 E4]. rewrite E3, E4. split; reflexivity.
Qed.

(* ================= live blocks: the low bound and the no-repeat fact ================= *)

Lemma zzwv_block_low : forall ly S W mem md p n,
  AR tfibsegs B ly S W mem md -> In (p, n) (ablocks B ly S) -> 4096 <= p /\ 0 <= n.
Proof.
  intros ly S W mem md p n HAR Hin.
  destruct (al_blocks tfibsegs B (AR_laws_ok tfibsegs B) ly S W mem md p n HAR Hin)
    as (_ & H4096 & _ & _ & _ & _ & Hn).
  split; [exact H4096 | lia].
Qed.

(* nothing at or below address 0 is a live block, so a writer buffer at NULL has none *)
Lemma zzwv_zero_blk_absurd : forall ly S W mem md c,
  AR tfibsegs B ly S W mem md -> In (0 - HEAD, c) (ablocks B ly S) -> False.
Proof.
  intros ly S W mem md c HAR Hin.
  destruct (zzwv_block_low ly S W mem md _ _ HAR Hin) as (H4 & _). unfold HEAD in H4. lia.
Qed.

Lemma zzwv_zero_head_absurd : forall ly S W mem md U c,
  AR tfibsegs B ly S W mem md -> fs_heads B ly S U -> In (0 - HEAD, c) U -> False.
Proof.
  intros ly S W mem md U c HAR HU Hin.
  destruct (HU _ Hin) as (_ & m & Hm & _). cbn [fst] in Hm.
  exact (zzwv_zero_blk_absurd ly S W mem md m HAR Hm).
Qed.

(* a block that is live twice overlaps itself, which a block of positive request size cannot *)
Lemma zzwv_ab_mid_dup : forall ly S W mem md C1 C2 x,
  AR tfibsegs B ly S W mem md -> ablocks B ly S = C1 ++ x :: C2 -> In x (C1 ++ C2) -> False.
Proof.
  intros ly S W mem md C1 C2 [p n] HAR E Hin.
  assert (Hx : In (p, n) (ablocks B ly S))
    by (rewrite E; apply in_or_app; right; left; reflexivity).
  destruct (al_blocks tfibsegs B (AR_laws_ok tfibsegs B) ly S W mem md p n HAR Hx)
    as (_ & _ & _ & _ & _ & Hpw & Hn).
  rewrite E, map_app in Hpw. cbn [map] in Hpw.
  assert (Hin2 : In (p, req_size n) (map (fun b : Z * Z => (fst b, req_size (snd b))) C1 ++
                                     map (fun b : Z * Z => (fst b, req_size (snd b))) C2)).
  { rewrite <- map_app. exact (in_map (fun b : Z * Z => (fst b, req_size (snd b))) (C1 ++ C2) (p, n) Hin). }
  pose proof (zzwv_pairwise_dup zdisjoint _ _ _ Hpw Hin2) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. unfold req_size in Hd.
  destruct (Z.eqb_spec n 0); lia.
Qed.

Lemma zzwv_ab_app_dup : forall ly S W mem md A x,
  AR tfibsegs B ly S W mem md -> ablocks B ly S = A ++ [x] -> In x A -> False.
Proof.
  intros ly S W mem md A x HAR E Hin.
  apply (zzwv_ab_mid_dup ly S W mem md A [] x HAR E). rewrite app_nil_r. exact Hin.
Qed.

(* the live-block list splits at a live block in one way only (live blocks are pairwise disjoint and of
   positive request size, YG0d.v AR_blocks_law) *)
Lemma zzwv_ab_split_uniq : forall ly S W mem md l1 l2 l3 l4 x,
  AR tfibsegs B ly S W mem md -> ablocks B ly S = l1 ++ x :: l2 -> ablocks B ly S = l3 ++ x :: l4 ->
  l1 ++ l2 = l3 ++ l4.
Proof.
  intros ly S W mem md l1 l2 l3 l4 [p n] HAR E1 E2.
  assert (Hx : In (p, n) (ablocks B ly S))
    by (rewrite E1; apply in_or_app; right; left; reflexivity).
  destruct (al_blocks tfibsegs B (AR_laws_ok tfibsegs B) ly S W mem md p n HAR Hx)
    as (_ & _ & _ & _ & _ & Hpw & Hn).
  rewrite E1 in Hpw.
  assert (Hnd : ~ zdisjoint ((fun b : Z * Z => (fst b, req_size (snd b))) (p, n))
                            ((fun b : Z * Z => (fst b, req_size (snd b))) (p, n))).
  { cbv beta. unfold zdisjoint, req_size. cbn [fst snd]. destruct (Z.eqb_spec n 0); lia. }
  rewrite E1 in E2.
  destruct (zzwv_split_uniq (fun b : Z * Z => (fst b, req_size (snd b))) zdisjoint (p, n) l1 l2 l3 l4
              Hpw Hnd E2) as (E3 & E4).
  rewrite E3, E4. reflexivity.
Qed.

Lemma zzwv_u_mid_dup : forall U U1 U2 x,
  pairwise zdisjoint U -> U = U1 ++ x :: U2 -> In x (U1 ++ U2) -> 0 < snd x -> False.
Proof.
  intros U U1 U2 x HP E Hin Hpos. rewrite E in HP.
  pose proof (zzwv_pairwise_dup zdisjoint U1 U2 x HP Hin) as Hd.
  unfold zdisjoint in Hd. lia.
Qed.

Lemma zzwv_u_app_dup : forall U L x,
  pairwise zdisjoint U -> U = L ++ [x] -> In x L -> 0 < snd x -> False.
Proof.
  intros U L x HP E Hin Hpos.
  apply (zzwv_u_mid_dup U L [] x HP E); [rewrite app_nil_r; exact Hin | exact Hpos].
Qed.

(* every block but the writer's own buffer is still live after the call *)
Lemma zzwv_bswap_kept : forall A A' buf buf' cap cap' p n,
  bswap A A' buf buf' cap cap' -> In (p, n) A -> (p, n) <> (buf - HEAD, cap + HEAD) -> In (p, n) A'.
Proof.
  intros A A' buf buf' cap cap' p n HS Hin Hne.
  destruct HS as [(_ & _ & ->) | [(_ & C1 & C2 & -> & <-) | (A1 & A2 & C1 & C2 & -> & -> & EC)]].
  - exact Hin.
  - apply zzwv_in_ins. exact Hin.
  - apply zzwv_in_ins. rewrite EC. exact (WriterRet.in_mid _ _ A1 A2 Hin Hne).
Qed.

(* ================= C1: the model split at a call boundary ================= *)

Definition wv_rst (st : WriterApp.wst) : WriterApp.wst := WriterApp.mkW
  (WriterApp.w_failed st) (WriterApp.w_text st) (WriterApp.w_cap st) (WriterApp.w_cnt st)
  (WriterApp.w_fail st) [].

(* the same state with a prefix prepended to the recorded allocator calls *)
Definition zzwv_pre (c : list Z) (st : WriterApp.wst) : WriterApp.wst := WriterApp.mkW
  (WriterApp.w_failed st) (WriterApp.w_text st) (WriterApp.w_cap st) (WriterApp.w_cnt st)
  (WriterApp.w_fail st) (c ++ WriterApp.w_calls st).

Lemma zzwv_put1_pre : forall c st b,
  WriterApp.put1 (zzwv_pre c st) b = zzwv_pre c (WriterApp.put1 st b).
Proof.
  intros c [f t cp n fl cs] b. unfold zzwv_pre, WriterApp.put1.
  cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls].
  destruct (negb (f =? 0)).
  - cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls].
    reflexivity.
  - destruct (_ <=? cp).
    + cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls].
      reflexivity.
    + destruct (n =? fl);
        cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail
             WriterApp.w_calls];
        rewrite app_assoc; reflexivity.
Qed.

Lemma zzwv_putN_pre : forall P c st,
  WriterApp.putN (zzwv_pre c st) P = zzwv_pre c (WriterApp.putN st P).
Proof.
  induction P as [|b P IH]; intros c st; [reflexivity|].
  rewrite !WriterApp.putN_cons, zzwv_put1_pre. apply IH.
Qed.

Lemma zzwv_pre_self : forall st, zzwv_pre (WriterApp.w_calls st) (wv_rst st) = st.
Proof.
  intros [f t cp n fl cs]. unfold zzwv_pre, wv_rst.
  cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls].
  rewrite app_nil_r. reflexivity.
Qed.

(* putN's five other fields never read w_calls, and the calls it records are the ones it records from the
   reset state, appended to what was there *)
Lemma wv_putN_calls_indep : forall st P,
  WriterApp.w_failed (WriterApp.putN st P) = WriterApp.w_failed (WriterApp.putN (wv_rst st) P) /\
  WriterApp.w_text (WriterApp.putN st P) = WriterApp.w_text (WriterApp.putN (wv_rst st) P) /\
  WriterApp.w_cap (WriterApp.putN st P) = WriterApp.w_cap (WriterApp.putN (wv_rst st) P) /\
  WriterApp.w_cnt (WriterApp.putN st P) = WriterApp.w_cnt (WriterApp.putN (wv_rst st) P) /\
  WriterApp.w_fail (WriterApp.putN st P) = WriterApp.w_fail (WriterApp.putN (wv_rst st) P) /\
  WriterApp.w_calls (WriterApp.putN st P)
    = WriterApp.w_calls st ++ WriterApp.w_calls (WriterApp.putN (wv_rst st) P).
Proof.
  intros st P.
  assert (E : WriterApp.putN st P = zzwv_pre (WriterApp.w_calls st) (WriterApp.putN (wv_rst st) P)).
  { rewrite <- zzwv_putN_pre, zzwv_pre_self. reflexivity. }
  rewrite E. unfold zzwv_pre.
  cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls].
  repeat split; reflexivity.
Qed.

Lemma wv_putN_split : forall st P Q,
  WriterApp.w_failed (WriterApp.putN st (P ++ Q))
    = WriterApp.w_failed (WriterApp.putN (wv_rst (WriterApp.putN st P)) Q) /\
  WriterApp.w_text (WriterApp.putN st (P ++ Q))
    = WriterApp.w_text (WriterApp.putN (wv_rst (WriterApp.putN st P)) Q) /\
  WriterApp.w_cap (WriterApp.putN st (P ++ Q))
    = WriterApp.w_cap (WriterApp.putN (wv_rst (WriterApp.putN st P)) Q) /\
  WriterApp.w_cnt (WriterApp.putN st (P ++ Q))
    = WriterApp.w_cnt (WriterApp.putN (wv_rst (WriterApp.putN st P)) Q) /\
  WriterApp.w_fail (WriterApp.putN st (P ++ Q))
    = WriterApp.w_fail (WriterApp.putN (wv_rst (WriterApp.putN st P)) Q) /\
  wcalls (WriterApp.putN st (P ++ Q))
    = wcalls (WriterApp.putN st P) + wcalls (WriterApp.putN (wv_rst (WriterApp.putN st P)) Q).
Proof.
  intros st P Q. rewrite WriterApp.putN_app.
  destruct (wv_putN_calls_indep (WriterApp.putN st P) Q) as (H1 & H2 & H3 & H4 & H5 & H6).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  unfold wcalls. rewrite H6, length_app, Nat2Z.inj_add. reflexivity.
Qed.

(* ================= C2: monotonicity along one call's pieces ================= *)

Lemma wv_cap_mono : forall st P,
  0 <= WriterApp.w_cap st -> WriterApp.w_cap st <= WriterApp.w_cap (WriterApp.putN st P).
Proof. intros st P H. exact (WriterRet.putN_cap P st H). Qed.

Lemma wv_room_mid : forall st P Q,
  (length (WriterApp.w_text (WriterApp.putN st P)) + length (concat Q) <=
   length (WriterApp.w_text st) + length (concat (P ++ Q)))%nat.
Proof.
  intros st P Q. pose proof (WriterRet.putN_text P st) as H.
  rewrite concat_app, length_app. lia.
Qed.

Lemma zzwv_calls_mono : forall P st, wcalls st <= wcalls (WriterApp.putN st P).
Proof.
  intros P st. destruct (WriterRet.putN_calls_ex P st) as [l E].
  unfold wcalls. rewrite E, length_app. lia.
Qed.

Lemma zzwv_put1_step : forall st b,
  (WriterApp.w_cnt (WriterApp.put1 st b) = WriterApp.w_cnt st /\
   wcalls (WriterApp.put1 st b) = wcalls st) \/
  (WriterApp.w_cnt (WriterApp.put1 st b) = (WriterApp.w_cnt st + 1) mod 2 ^ 64 /\
   wcalls (WriterApp.put1 st b) = wcalls st + 1).
Proof.
  intros [f t cp n fl cs] b. unfold WriterApp.put1, wcalls.
  cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls].
  destruct (negb (f =? 0)); [left; split; reflexivity|].
  destruct (_ <=? cp);
    [left; cbn [WriterApp.w_cnt WriterApp.w_calls]; split; reflexivity|].
  destruct (n =? fl); right; cbn [WriterApp.w_cnt WriterApp.w_calls];
    (split; [reflexivity | rewrite length_app; cbn [length]; lia]).
Qed.

Lemma zzwv_cnt_gen : forall P st, 0 <= WriterApp.w_cnt st ->
  WriterApp.w_cnt st + (wcalls (WriterApp.putN st P) - wcalls st) < 2 ^ 64 ->
  WriterApp.w_cnt (WriterApp.putN st P) = WriterApp.w_cnt st + (wcalls (WriterApp.putN st P) - wcalls st).
Proof.
  induction P as [|b P IH]; intros st H0 Hlt; [rewrite WriterApp.putN_nil; lia|].
  rewrite WriterApp.putN_cons in Hlt |- *.
  pose proof (zzwv_calls_mono P (WriterApp.put1 st b)) as Hmono.
  destruct (zzwv_put1_step st b) as [(Ecnt & Ecl) | (Ecnt & Ecl)].
  - rewrite (IH (WriterApp.put1 st b) ltac:(lia) ltac:(lia)). lia.
  - assert (Hsmall : (WriterApp.w_cnt st + 1) mod 2 ^ 64 = WriterApp.w_cnt st + 1)
      by (apply Z.mod_small; lia).
    rewrite Hsmall in Ecnt.
    rewrite (IH (WriterApp.put1 st b) ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma wv_cnt_calls : forall st P, WriterApp.w_calls st = [] ->
  0 <= WriterApp.w_cnt st -> WriterApp.w_cnt st + wcalls (WriterApp.putN st P) < 2 ^ 64 ->
  WriterApp.w_cnt (WriterApp.putN st P) = WriterApp.w_cnt st + wcalls (WriterApp.putN st P).
Proof.
  intros st P Hnil H0 Hlt.
  assert (E0 : wcalls st = 0) by (unfold wcalls; rewrite Hnil; reflexivity).
  pose proof (zzwv_cnt_gen P st H0 ltac:(lia)) as H. lia.
Qed.

(* ================= C2b: the cap-aware event count splits at a call boundary ================= *)

(* along putN from a state with no recorded call and cap 0: either still no call (and cap 0), or a call was
   made and from then on the buffer exists or `failed` is set; put1 records no call once failed <> 0
   (WriterApp.putN_failed), and a granted cap is positive (WriterRet.newcap_pos) *)
Definition zzwv_inv0 (st : WriterApp.wst) : Prop :=
  (WriterApp.w_calls st = [] /\ WriterApp.w_cap st = 0) \/
  (WriterApp.w_calls st <> [] /\ (0 < WriterApp.w_cap st \/ WriterApp.w_failed st <> 0)).

Lemma zzwv_put1_inv0 : forall st b, zzwv_inv0 st -> zzwv_inv0 (WriterApp.put1 st b).
Proof.
  intros [f t cp n fl cs] b H. unfold WriterApp.put1.
  cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls].
  unfold zzwv_inv0 in H. cbn [WriterApp.w_failed WriterApp.w_cap WriterApp.w_calls] in H.
  destruct (Z.eqb_spec f 0) as [Ef | Ef]; cbn [negb].
  2:{ unfold zzwv_inv0. cbn [WriterApp.w_failed WriterApp.w_cap WriterApp.w_calls]. exact H. }
  assert (Hcp : 0 <= cp) by (destruct H as [(_ & Hc) | (_ & [Hp | Hf])]; [lia | lia | contradiction]).
  destruct (_ <=? cp); unfold zzwv_inv0; cbn [WriterApp.w_failed WriterApp.w_cap WriterApp.w_calls].
  - destruct H as [H | (Hc & [Hp | Hf])];
      [left; exact H | right; split; [exact Hc | left; exact Hp] | contradiction].
  - destruct (n =? fl); cbn [WriterApp.w_failed WriterApp.w_cap WriterApp.w_calls]; right;
      (split; [intros E; destruct cs; discriminate E|]).
    + right. lia.
    + left. apply WriterRet.newcap_pos. exact Hcp.
Qed.

Lemma zzwv_putN_inv0 : forall P st, zzwv_inv0 st -> zzwv_inv0 (WriterApp.putN st P).
Proof.
  induction P as [|b P IH]; intros st H; [exact H|].
  rewrite WriterApp.putN_cons. apply IH. apply zzwv_put1_inv0. exact H.
Qed.

Lemma wv_wevk_split : forall st P Q, WriterApp.w_calls st = [] -> 0 <= WriterApp.w_cap st ->
  wevk (WriterApp.w_cap st) (WriterApp.putN st (P ++ Q)) =
  wevk (WriterApp.w_cap st) (WriterApp.putN st P) +
  wevk (WriterApp.w_cap (WriterApp.putN st P)) (WriterApp.putN (wv_rst (WriterApp.putN st P)) Q).
Proof.
  intros st P Q Hnil Hc.
  pose proof (wv_cap_mono st P Hc) as Hm.
  pose proof (zzwv_putN_inv0 P st) as HI.
  rewrite WriterApp.putN_app.
  destruct (wv_putN_calls_indep (WriterApp.putN st P) Q) as (_ & _ & _ & _ & _ & Ecl).
  revert Hm HI Ecl. generalize (WriterApp.putN st P) as s1. intros s1 Hm HI Ecl.
  unfold wevk. destruct (Z.eqb_spec (WriterApp.w_cap st) 0) as [E0 | En]; cbv beta iota.
  - (* cap 0: the first request of the whole call is the only cheap one *)
    assert (HI1 : zzwv_inv0 s1) by (apply HI; left; split; [exact Hnil | exact E0]).
    destruct HI1 as [(Ec1 & Ecap1) | (Hne & [Hpos | Hf])].
    + (* no request before the boundary *)
      unfold wev0. rewrite Ecl, Ec1, Ecap1, Z.eqb_refl. cbn [app]. lia.
    + (* the buffer exists at the boundary: every later request is a real fuzz_realloc *)
      rewrite (proj2 (Z.eqb_neq (WriterApp.w_cap s1) 0) ltac:(lia)).
      unfold wev0, wcalls. rewrite Ecl.
      destruct (WriterApp.w_calls s1) as [|c r] eqn:Ecs;
        [exfalso; apply Hne; first [reflexivity | exact Ecs] |].
      cbn [app]. rewrite length_app, Nat2Z.inj_add. unfold EV_fuzz_realloc. lia.
    + (* failed at the boundary: no later request *)
      rewrite (WriterApp.putN_failed Q s1 Hf), (WriterApp.putN_failed Q (wv_rst s1) Hf).
      unfold wev0, wcalls, wv_rst. cbn [WriterApp.w_calls].
      destruct (WriterApp.w_cap s1 =? 0); cbn [length Z.of_nat]; lia.
  - (* cap <> 0: every request costs EV_fuzz_realloc, and the cap only grows *)
    rewrite (proj2 (Z.eqb_neq (WriterApp.w_cap s1) 0) ltac:(lia)). cbv beta iota.
    unfold wcalls. rewrite Ecl, length_app, Nat2Z.inj_add. unfold EV_fuzz_realloc. lia.
Qed.

Lemma wv_wevk_nonneg : forall c st, 0 <= wevk c st.
Proof.
  intros c st. unfold wevk, wev0, wcalls, EV_fuzz_malloc, EV_fuzz_realloc.
  destruct (c =? 0); [destruct (WriterApp.w_calls st) as [|x r]|]; cbv beta iota; lia.
Qed.

Lemma wv_wevk_mono : forall st P Q, WriterApp.w_calls st = [] -> 0 <= WriterApp.w_cap st ->
  wevk (WriterApp.w_cap st) (WriterApp.putN st P) <= wevk (WriterApp.w_cap st) (WriterApp.putN st (P ++ Q)).
Proof.
  intros st P Q Hnil Hc. rewrite (wv_wevk_split st P Q Hnil Hc).
  pose proof (wv_wevk_nonneg (WriterApp.w_cap (WriterApp.putN st P))
                (WriterApp.putN (wv_rst (WriterApp.putN st P)) Q)) as H0.
  lia.
Qed.

(* ================= C3: the budget split at every call site ================= *)

Lemma wv_budget_pre_prefix : forall S cap cnt live failed text fail P Q,
  0 <= cap ->
  wbudget_pre S cap cnt live (WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) (P ++ Q)) ->
  wbudget_pre S cap cnt live (WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) P).
Proof.
  intros S cap cnt live failed text fail P Q Hcap (H1 & H2 & H3 & H4).
  pose proof (wv_wevk_mono (WriterApp.mkW failed text cap cnt fail []) P Q eq_refl Hcap) as Hmo.
  cbn [WriterApp.w_cap] in Hmo.
  rewrite WriterApp.putN_app in H2, H3, H4.
  assert (Hc0 : 0 <= WriterApp.w_cap (WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) P)).
  { pose proof (wv_cap_mono (WriterApp.mkW failed text cap cnt fail []) P) as Hm.
    cbn [WriterApp.w_cap] in Hm. specialize (Hm Hcap). lia. }
  pose proof (wv_cap_mono _ Q Hc0) as Hcap2.
  pose proof (zzwv_calls_mono Q (WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) P)) as Hcl.
  unfold wbudget_pre. split; [lia|]. split; [lia|]. split; lia.
Qed.

Lemma wv_budget_pre_mid : forall S S1 cap cnt live failed text fail P Q,
  0 <= cap ->
  wbudget_pre S cap cnt live (WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) (P ++ Q)) ->
  st_nev S1 <= st_nev S + wevk cap (WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) P) ->
  blocks_bytes S1 - bsz (WriterApp.w_cap (WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) P))
    <= blocks_bytes S - bsz cap ->
  WriterApp.w_cnt (WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) P)
    = cnt + wcalls (WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) P) ->
  wbudget_pre S1
    (WriterApp.w_cap (WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) P))
    (WriterApp.w_cnt (WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) P))
    (live - cap + WriterApp.w_cap (WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) P))
    (WriterApp.putN (wv_rst (WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) P)) Q).
Proof.
  intros S S1 cap cnt live failed text fail P Q Hcap (H1 & H2 & H3 & H4) Hnev Hbb Hcnt.
  pose proof (wv_wevk_split (WriterApp.mkW failed text cap cnt fail []) P Q eq_refl Hcap) as Hsp.
  cbn [WriterApp.w_cap] in Hsp.
  destruct (wv_putN_split (WriterApp.mkW failed text cap cnt fail []) P Q)
    as (_ & _ & Ecap & _ & _ & Ecalls).
  rewrite Hsp in H1. rewrite Ecalls in H4. rewrite Ecap in H2, H3.
  unfold wbudget_pre. split; [lia|]. split; [lia|]. split; lia.
Qed.

(* ================= C4: the two swap relations compose ================= *)

Lemma wv_bswap_trans : forall ly1 S1 (W1 : world tfibsegs) mem1 md1 A0 A1 A2 b0 b1 b2 c0 c1 c2,
  AR tfibsegs B ly1 S1 W1 mem1 md1 -> A1 = ablocks B ly1 S1 ->
  (c1 <> 0 -> In (b1 - HEAD, c1 + HEAD) A1) -> (c1 = 0 -> b1 = 0) -> 0 <= c1 -> 0 <= c2 ->
  bswap A0 A1 b0 b1 c0 c1 -> bswap A1 A2 b1 b2 c1 c2 -> bswap A0 A2 b0 b2 c0 c2.
Proof.
  intros ly1 S1 W1 mem1 md1 A0 A1 A2 b0 b1 b2 c0 c1 c2 HAR EA1 _ Hb1 _ _ H1 H2.
  destruct H1 as [(Eb & Ec & EA) | [(Ec0 & C1 & C2 & EA & EC) | (A01 & A02 & C1 & C2 & EA0 & EA & EC)]].
  - subst. exact H2.
  - (* step one allocated from NULL: the new block anywhere, C1 ++ C2 = A0 *)
    destruct H2 as [(Eb2 & Ec2 & EA2) | [(Ec1 & D1 & D2 & EA2 & ED) | (Aa & Ab & D1 & D2 & EA1' & EA2 & ED)]].
    + right; left. split; [exact Ec0|]. exists C1, C2. split; [|exact EC].
      rewrite EA2, EA, Eb2, Ec2. reflexivity.
    + exfalso. apply (zzwv_zero_blk_absurd ly1 S1 W1 mem1 md1 (c1 + HEAD) HAR).
      rewrite <- EA1, EA, <- (Hb1 Ec1). apply in_or_app. right. left. reflexivity.
    + (* step two reallocated: the middle list splits at the middle buffer in one way only *)
      assert (EU : C1 ++ C2 = Aa ++ Ab).
      { apply (zzwv_ab_split_uniq ly1 S1 W1 mem1 md1 C1 C2 Aa Ab (b1 - HEAD, c1 + HEAD) HAR);
          rewrite <- EA1; [exact EA | exact EA1']. }
      right; left. split; [exact Ec0|]. exists D1, D2. split; [exact EA2|]. rewrite ED, <- EU. exact EC.
  - (* step one reallocated: C1 ++ C2 = A01 ++ A02 *)
    destruct H2 as [(Eb2 & Ec2 & EA2) | [(Ec1 & D1 & D2 & EA2 & ED) | (Aa & Ab & D1 & D2 & EA1' & EA2 & ED)]].
    + right; right. exists A01, A02, C1, C2. split; [exact EA0|]. split; [|exact EC].
      rewrite EA2, EA, Eb2, Ec2. reflexivity.
    + exfalso. apply (zzwv_zero_blk_absurd ly1 S1 W1 mem1 md1 (c1 + HEAD) HAR).
      rewrite <- EA1, EA, <- (Hb1 Ec1). apply in_or_app. right. left. reflexivity.
    + assert (EU : C1 ++ C2 = Aa ++ Ab).
      { apply (zzwv_ab_split_uniq ly1 S1 W1 mem1 md1 C1 C2 Aa Ab (b1 - HEAD, c1 + HEAD) HAR);
          rewrite <- EA1; [exact EA | exact EA1']. }
      right; right. exists A01, A02, D1, D2. split; [exact EA0|]. split; [exact EA2|].
      rewrite ED, <- EU. exact EC.
Qed.

Lemma wv_uswap_trans : forall ly1 S1 (W1 : world tfibsegs) mem1 md1 U0 U1 U2 b0 b1 b2 c0 c1,
  AR tfibsegs B ly1 S1 W1 mem1 md1 ->
  upoison_ok B ly1 S1 U1 -> fs_heads B ly1 S1 U1 -> (c1 = 0 -> b1 = 0) -> 0 <= c0 -> c0 <= c1 ->
  uswap U0 U1 b0 b1 c0 -> uswap U1 U2 b1 b2 c1 -> uswap U0 U2 b0 b2 c0.
Proof.
  intros ly1 S1 W1 mem1 md1 U0 U1 U2 b0 b1 b2 c0 c1 HAR HOK HU Hb1 Hc0 Hc01 H1 H2.
  destruct HOK as (_ & HPW).
  destruct H1 as [(EU & Eb) | [(Ua & Ub & EU0 & EU1) | (Ec0 & EU1)]].
  - (* step one left the head alone *)
    subst U1 b1.
    destruct H2 as [(EU2 & Eb2) | [(Uc & Ud & EU0' & EU2) | (Ec1 & EU2)]].
    + left. split; [exact EU2 | exact Eb2].
    + right; left. exists Uc, Ud. split; [exact EU0' | exact EU2].
    + right; right. split; [lia | exact EU2].
  - (* step one swapped the head *)
    destruct H2 as [(EU2 & Eb2) | [(Uc & Ud & EU1' & EU2) | (Ec1 & EU2)]].
    + right; left. exists Ua, Ub. split; [exact EU0|]. rewrite EU2, EU1, Eb2. reflexivity.
    + assert (EE : Uc ++ (b1 - HEAD, HEAD) :: Ud = (Ua ++ Ub) ++ [(b1 - HEAD, HEAD)]).
      { rewrite <- app_assoc, <- EU1'. exact EU1. }
      destruct (zzwv_app_last_split (Ua ++ Ub) Uc Ud _ EE) as [(-> & ->) | Hdup].
      * right; left. exists Ua, Ub. split; [exact EU0|].
        rewrite EU2, app_nil_l, app_assoc. reflexivity.
      * exfalso. apply (zzwv_u_app_dup U1 (Ua ++ Ub) (b1 - HEAD, HEAD) HPW);
          [rewrite EU1, app_assoc; reflexivity | exact Hdup | cbn [snd]; unfold HEAD; lia].
    + exfalso. apply (zzwv_zero_head_absurd ly1 S1 W1 mem1 md1 U1 HEAD HAR HU).
      rewrite EU1, <- (Hb1 Ec1). apply in_or_app. right. apply in_or_app. right. left. reflexivity.
  - (* step one allocated the first buffer *)
    destruct H2 as [(EU2 & Eb2) | [(Uc & Ud & EU1' & EU2) | (Ec1 & EU2)]].
    + right; right. split; [exact Ec0|]. rewrite EU2, EU1, Eb2. reflexivity.
    + assert (EE : Uc ++ (b1 - HEAD, HEAD) :: Ud = U0 ++ [(b1 - HEAD, HEAD)])
        by (rewrite <- EU1'; exact EU1).
      destruct (zzwv_app_last_split U0 Uc Ud _ EE) as [(-> & ->) | Hdup].
      * right; right. split; [exact Ec0|]. rewrite EU2. reflexivity.
      * exfalso. apply (zzwv_u_app_dup U1 U0 (b1 - HEAD, HEAD) HPW);
          [exact EU1 | exact Hdup | cbn [snd]; unfold HEAD; lia].
    + exfalso. apply (zzwv_zero_head_absurd ly1 S1 W1 mem1 md1 U1 HEAD HAR HU).
      rewrite EU1, <- (Hb1 Ec1). apply in_or_app. right. left. reflexivity.
Qed.

(* ================= C5: fs_heads survives a writer call ================= *)

Lemma wv_heads_swap : forall ly S U (W : world tfibsegs) mem md ly' S' U' (W' : world tfibsegs) mem' md'
    buf buf' cap cap',
  ARU tfibsegs B ly S U W mem md -> ARU tfibsegs B ly' S' U' W' mem' md' ->
  fs_heads B ly S U -> uswap U U' buf buf' cap ->
  bswap (ablocks B ly S) (ablocks B ly' S') buf buf' cap cap' ->
  (cap <> 0 -> In (buf - HEAD, cap + HEAD) (ablocks B ly S)) ->
  (cap' <> 0 -> In (buf' - HEAD, cap' + HEAD) (ablocks B ly' S')) ->
  (cap = 0 -> buf = 0) -> (cap' = 0 -> buf' = 0) -> 0 <= cap -> 0 <= cap' ->
  fs_heads B ly' S' U'.
Proof.
  intros ly S U W mem md ly' S' U' W' mem' md' buf buf' cap cap'
    HARU HARU' HU HUs HBs _ Hb' Hz Hz' _ Hc'.
  destruct HARU as (HAR & HOK & _). destruct HARU' as (HAR' & HOK' & _).
  destruct HOK as (_ & HPW). destruct HOK' as (HF' & _).
  (* the new buffer's head is the start of a live block at the call's return *)
  assert (Hnew : In (buf' - HEAD, HEAD) U' ->
                 exists m, In (buf' - HEAD, m) (ablocks B ly' S') /\ 16 <= req_size m).
  { intros Hr. destruct (Z.eqb_spec cap' 0) as [E0 | Enz].
    - exfalso. rewrite (Hz' E0) in Hr.
      rewrite Forall_forall in HF'.
      destruct (HF' _ Hr) as (_ & _ & _ & p & n & Hpn & Hple & _). cbn [fst] in Hple.
      destruct (zzwv_block_low ly' S' W' (unpoison U' mem') md' p n HAR' Hpn) as (H4 & _).
      unfold HEAD in Hple. lia.
    - exists (cap' + HEAD). split; [exact (Hb' Enz)|].
      unfold req_size, HEAD. destruct (Z.eqb_spec (cap' + 16) 0); lia. }
  apply (fs_heads_uswap B ly S ly' S' U U' buf buf' cap HU HUs).
  - (* a head that survives the call *)
    intros r Hr' Hr. destruct (HU r Hr) as (Hsnd & m & Hm & Hm16).
    destruct (zz_eq_dec (fst r, m) (buf - HEAD, cap + HEAD)) as [Eeq | Ene].
    + (* it is the writer's own buffer head *)
      injection Eeq as Ef Em.
      assert (Er : r = (buf - HEAD, HEAD)).
      { destruct r as [rp rn]. cbn [fst snd] in Ef, Hsnd. rewrite Ef, Hsnd. unfold HEAD. reflexivity. }
      assert (Hbuf0 : buf = 0 -> False).
      { intros E. apply (zzwv_zero_blk_absurd ly S W (unpoison U mem) md m HAR).
        rewrite <- E, <- Ef. exact Hm. }
      assert (Ebb : buf' = buf).
      { destruct HUs as [(_ & Eb) | [(Ua & Ub & EU0 & EU1) | (Ec0 & EU1)]].
        - exact Eb.
        - rewrite Er, EU1 in Hr'. apply in_app_or in Hr'. destruct Hr' as [Hq | Hq].
          + exfalso. apply (zzwv_u_mid_dup U Ua Ub (buf - HEAD, HEAD) HPW EU0);
              [apply in_or_app; left; exact Hq | cbn [snd]; unfold HEAD; lia].
          + apply in_app_or in Hq. destruct Hq as [Hq | [Hq | []]].
            * exfalso. apply (zzwv_u_mid_dup U Ua Ub (buf - HEAD, HEAD) HPW EU0);
                [apply in_or_app; right; exact Hq | cbn [snd]; unfold HEAD; lia].
            * injection Hq as Hq. lia.
        - exfalso. exact (Hbuf0 (Hz Ec0)). }
      destruct (Z.eqb_spec cap' 0) as [E0 | Enz].
      * exfalso. apply Hbuf0. rewrite <- Ebb. exact (Hz' E0).
      * exists (cap' + HEAD). rewrite Ef, <- Ebb. split; [exact (Hb' Enz)|].
        unfold req_size, HEAD. destruct (Z.eqb_spec (cap' + 16) 0); lia.
    + exists m. split; [|exact Hm16].
      exact (zzwv_bswap_kept _ _ _ _ _ _ _ _ HBs Hm Ene).
  - (* a head that is new *)
    intros r Hr' Hnr.
    pose proof (uswap_new_head U U' buf buf' cap r HUs Hr' Hnr) as Er.
    split; [exact Er|]. apply Hnew. rewrite <- Er. exact Hr'.
Qed.

(* ================= C6 / C7 / C8: the scalar chains ================= *)

Lemma wv_budget_kept_trans : forall S S1 S2 failed cap cnt failed1 cap1 cnt1 failed2 cap2 cnt2,
  wbudget_kept S S1 failed cap cnt failed1 cap1 cnt1 ->
  wbudget_kept S1 S2 failed1 cap1 cnt1 failed2 cap2 cnt2 ->
  wbudget_kept S S2 failed cap cnt failed2 cap2 cnt2.
Proof.
  intros S S1 S2 failed cap cnt failed1 cap1 cnt1 failed2 cap2 cnt2 (K1 & K2 & K3) (L1 & L2 & L3).
  unfold wbudget_kept. split; [exact L1|]. split; lia.
Qed.

Lemma wv_wkeep_trans : forall (W W1 W2 : world tfibsegs) mem mem1 mem2 sp ot o,
  wkeep tfibsegs W W1 mem mem1 sp ot o 32 -> wkeep tfibsegs W1 W2 mem1 mem2 sp ot o 32 ->
  wkeep tfibsegs W W2 mem mem2 sp ot o 32.
Proof.
  intros W W1 W2 mem mem1 mem2 sp ot o H1 H2 a Ha Hno.
  destruct (H1 a Ha Hno) as (E1 & I1). destruct (H2 a Ha Hno) as (E2 & I2).
  split; [rewrite E2; exact E1|].
  split; [intros Hx; apply I2, I1, Hx | intros Hx; apply I1, I2, Hx].
Qed.

(* the window's start only weakens the clause, so the LOW start is the strong one *)
Lemma wv_wkeep_mono : forall (W W' : world tfibsegs) mem mem' sp sp' ot o,
  sp <= sp' -> wkeep tfibsegs W W' mem mem' sp ot o 32 -> wkeep tfibsegs W W' mem mem' sp' ot o 32.
Proof. intros W W' mem mem' sp sp' ot o Hle H a Ha Hno. apply H; [lia | exact Hno]. Qed.

Lemma wv_peak_chain : forall peak p1 p2 live live1 cap cap1 cap2,
  live1 = live - cap + cap1 -> cap1 <= cap2 ->
  peak <= p1 -> p1 <= Z.max peak (live - cap + cap1) ->
  p1 <= p2 -> p2 <= Z.max p1 (live1 - cap1 + cap2) ->
  peak <= p2 /\ p2 <= Z.max peak (live - cap + cap2).
Proof.
  intros peak p1 p2 live live1 cap cap1 cap2 El Hc H1 H2 H3 H4. subst live1.
  pose proof (Z.max_spec peak (live - cap + cap1)) as M1.
  pose proof (Z.max_spec p1 (live - cap + cap1 - cap1 + cap2)) as M2.
  pose proof (Z.max_spec peak (live - cap + cap2)) as M3.
  split; lia.
Qed.

(* ================= C9: the footprint moves with the buffer ================= *)

Lemma wv_fp_sub_swap : forall ly S ly1 S1 (W1 : world tfibsegs) mem1 md1 buf cap buf1 cap1,
  AR tfibsegs B ly1 S1 W1 mem1 md1 ->
  bswap (ablocks B ly S) (ablocks B ly1 S1) buf buf1 cap cap1 ->
  (cap1 <> 0 -> In (buf1 - HEAD, cap1 + HEAD) (ablocks B ly1 S1)) -> 0 <= cap1 ->
  (forall a, inFP FS_PSTAT_FP a -> in_img tfibsegs a) ->
  fsw_fp_sub B ly S ly1 S1 [] (FS_PSTAT_FP ++ wbuf_fp buf cap) (FS_PSTAT_FP ++ wbuf_fp buf1 cap1).
Proof.
  intros ly S ly1 S1 W1 mem1 md1 buf cap buf1 cap1 HAR HBs Hin1 Hc1 Himg.
  unfold fsw_fp_sub. intros a Ha.
  destruct (proj1 (inFP_app FS_PSTAT_FP (wbuf_fp buf1 cap1) a) Ha) as [Hps | Hbuf].
  - right; right; left.
    split; [apply (proj2 (inFP_app FS_PSTAT_FP (wbuf_fp buf cap) a)); left; exact Hps
           | exact (Himg a Hps)].
  - unfold wbuf_fp in Hbuf. destruct (Z.eqb_spec cap1 0) as [E0 | Enz].
    + destruct Hbuf as (r & [] & _).
    + destruct Hbuf as (r & [<- | []] & Hr). cbn [fst snd] in Hr.
      assert (Hblk : In (buf1 - HEAD, cap1 + HEAD) (ablocks B ly1 S1)) by exact (Hin1 Enz).
      assert (Hrng : buf1 - HEAD <= a < buf1 - HEAD + req_size (cap1 + HEAD)).
      { unfold req_size. unfold HEAD in *. destruct (Z.eqb_spec (cap1 + 16) 0); lia. }
      destruct (in_dec zz_eq_dec (buf1 - HEAD, cap1 + HEAD) (ablocks B ly S)) as [Hold | Hnew].
      * (* the block was already live: it can only be the writer's own buffer *)
        assert (Esame : buf1 = buf /\ cap1 = cap).
        { destruct HBs as [(Eb & Ec & _) | [(Ec0 & C1 & C2 & EA & EC) | (A1 & A2 & C1 & C2 & EA & EA' & EC)]].
          - split; [exact Eb | exact Ec].
          - exfalso. apply (zzwv_ab_mid_dup ly1 S1 W1 mem1 md1 C1 C2 (buf1 - HEAD, cap1 + HEAD) HAR EA).
            rewrite EC. exact Hold.
          - destruct (zz_eq_dec (buf1 - HEAD, cap1 + HEAD) (buf - HEAD, cap + HEAD)) as [Eq | Nq].
            + injection Eq as E1 E2. split; lia.
            + exfalso. rewrite EA in Hold.
              apply (zzwv_ab_mid_dup ly1 S1 W1 mem1 md1 C1 C2 (buf1 - HEAD, cap1 + HEAD) HAR EA').
              rewrite EC. exact (WriterRet.in_mid _ _ A1 A2 Hold Nq). }
        destruct Esame as (Eb & Ec).
        left. split.
        -- apply (proj2 (inFP_app FS_PSTAT_FP (wbuf_fp buf cap) a)). right. unfold wbuf_fp.
           destruct (Z.eqb_spec cap 0) as [E0' | _]; [exfalso; apply Enz; lia|].
           exists (buf - HEAD, buf + cap). split; [left; reflexivity|].
           cbn [fst snd]. unfold HEAD in *. lia.
        -- exists (buf1 - HEAD), (cap1 + HEAD). split; [exact Hblk | exact Hrng].
      * right; left. exists (buf1 - HEAD), (cap1 + HEAD).
        split; [exact Hblk|]. split; [exact Hnew | exact Hrng].
Qed.

End C.
