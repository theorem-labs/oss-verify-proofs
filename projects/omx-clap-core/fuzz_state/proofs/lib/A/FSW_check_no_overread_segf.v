(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFl3.v:106-108
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:383-389, 448-454, 493-498, 501-509 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:625-631 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:208-214, 227-233 [Apache-2.0 OR MIT], for libreac/fuzz_identity's ASan
   build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_name_seg10.v, with its module paths and module names changed; 2634 of its 2686 lines of code are new or changed and 608 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSH_parse_value.v, with its module paths, module names, addresses and numbers changed; 1014 of its 1163 lines of code are new or changed and 2537 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_check_no_overread.v, with its module paths and module names changed; 1341 of its 1416 lines of code are new or changed and 1088 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_check_no_overread_top.v, with its addresses changed; 716 of its 798 lines of code are new or changed and 1334 lines of the source are left out. *)
(* check_no_overread 0x811c8 (fs.c), fs.asan: segment F of the CTX-free ASan walk (owner: a Theorem Labs lane).
   cno_segF : cno_segF_T B (FSW_check_no_overread_inv.v): from INV_F1, the machine at the first fuzz_free call
   (0x81420, ra 0x81424), through fuzz_free 0x81420 / 0x81428 / 0x81430 and __wrap_free 0x81438 / 0x81440 / 0x81448,
   to INV_R at 0x8144c (the hand-off to cno_tail_ret). The call steps cno_call_ffree_T / cno_call_afree_T are Section
   hypotheses. Between two calls the engine runs one instruction and the jal (fs.asan: 0x81424 mv a0, s8 / 0x8142c
   mv a0, s9 / 0x81434 ld a0, 0x18(s1) / 0x8143c mv a0, s4 / 0x81444 mv a0, s5).
   The three fuzz_free arguments are one list xs (bad text: three NULLs; success: the reader blocks q1 .. q3);
   cnof_nz xs, its non-NULL entries, are the reader blocks still live (cnof_pend). The raw blocks a, b, t and the
   reader blocks were appended inside the walk, so none of them is an entry block and no range of the entry's U is
   on them (cnof_fresh / cnof_Uout / cnof_head_notU: ARU's pairwise block disjointness and the entry's fs_heads).
   Each free removes its block from `entry ++ [...]`; the block occurs once (cnof_nodup), so the rest is the list
   without it (cnof_split), and INV_R's ablocks equation holds exactly. *)
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
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_ret
FSW_rres FSW_frame FSW_strkit FSW_rd FSH_Fn_cno FSH_Fn_alloc FSW_check_no_overread_tbl FSW_check_no_overread
FSW_check_no_overread_inv.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSH_Fn_writer ACem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* the callee-saved side condition of a register list *)
Ltac cnof_rs := repeat apply Forall_cons; try apply Forall_nil; cbv beta; cno_cs.

Lemma cnof_F2_cons {X Y : Type} {P : X -> Y -> Prop} {r : X} {rs : list X} {ys : list Y} :
  Forall2 P (r :: rs) ys -> exists y ys', ys = y :: ys' /\ P r y /\ Forall2 P rs ys'.
Proof.
intros H. destruct ys as [|y ys']; [inversion H|]. exists y, ys'.
inversion H; subst. split; [reflexivity | split; assumption].
Qed.
Lemma cnof_F2_nil {X Y : Type} {P : X -> Y -> Prop} {ys : list Y} : Forall2 P (@nil X) ys -> ys = [].
Proof. intros H. inversion H. reflexivity. Qed.

(* a list split at an element that occurs once: the two sides are determined *)
Lemma cnof_split : forall (x : Z * Z) A R l1 l2,
  ~ In x A -> ~ In x R -> A ++ x :: R = l1 ++ x :: l2 -> l1 = A /\ l2 = R.
Proof.
intros x A. induction A as [|y A IH]; intros R l1 l2 HA HR E; destruct l1 as [|z l1]; cbn [app] in E.
- inversion E. split; reflexivity.
- injection E as E1 E2. exfalso. apply HR. rewrite E2. apply in_or_app. right. left. reflexivity.
- injection E as E1 E2. exfalso. apply HA. left. exact E1.
- injection E as E1 E2. subst z.
  destruct (IH R l1 l2 (fun X => HA (or_intror X)) HR E2) as (-> & ->). split; reflexivity.
Qed.

Section F. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

(* ================= the blocks: no block occurs twice, the walk's blocks are fresh ================= *)
Lemma cnof_nodup : forall ly S (W : world tfibsegs) mem md A x R,
  AR tfibsegs B ly S W mem md -> ablocks B ly S = A ++ x :: R -> ~ In x A /\ ~ In x R.
Proof.
intros ly S W mem md A [p m] R HAR E.
assert (Hblk : In (p, m) (ablocks B ly S)) by (rewrite E; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly S W mem md p m HAR Hblk) as (_ & _ & _ & _ & _ & PW & Hmax).
assert (Hrs : 0 < req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
rewrite E in PW.
split; intros Hin; apply in_split in Hin as (C & D & ED); subst.
- assert (D0 : zdisjoint (p, req_size m) (p, req_size m)).
  { apply (YCbq.pairwise_In2 zdisjoint _ _ _ (map (fun b : Z * Z => (fst b, req_size (snd b))) C)
      (map (fun b : Z * Z => (fst b, req_size (snd b))) D) (map (fun b : Z * Z => (fst b, req_size (snd b))) R) PW).
    repeat ((rewrite map_app) || (progress cbn [map])). rewrite <- ?app_assoc. reflexivity. }
  unfold zdisjoint in D0. cbn [fst snd] in D0. lia.
- assert (D0 : zdisjoint (p, req_size m) (p, req_size m)).
  { apply (YCbq.pairwise_In2 zdisjoint _ _ _ (map (fun b : Z * Z => (fst b, req_size (snd b))) A)
      (map (fun b : Z * Z => (fst b, req_size (snd b))) C) (map (fun b : Z * Z => (fst b, req_size (snd b))) D) PW).
    repeat ((rewrite map_app) || (progress cbn [map])). rewrite <- ?app_assoc. reflexivity. }
  unfold zdisjoint in D0. cbn [fst snd] in D0. lia.
Qed.

(* a block of the tail L starts at no block of the head E *)
Lemma cnof_fresh : forall ly S (W : world tfibsegs) mem md (E L : list (Z * Z)) p n n0,
  AR tfibsegs B ly S W mem md -> ablocks B ly S = E ++ L -> In (p, n) L -> ~ In (p, n0) E.
Proof.
intros ly S W mem md E L p n n0 HAR HE HL H0.
apply in_split in HL as (C & D & EL).
assert (Hab : ablocks B ly S = (E ++ C) ++ (p, n) :: D) by (rewrite HE, EL, app_assoc; reflexivity).
destruct (cnof_nodup ly S W mem md _ _ _ HAR Hab) as (N1 & _).
assert (I1 : In (p, n0) (ablocks B ly S)) by (rewrite HE; apply in_or_app; left; exact H0).
assert (I2 : In (p, n) (ablocks B ly S)) by (rewrite Hab; apply in_or_app; right; left; reflexivity).
destruct (Z.eq_dec n0 n) as [-> | Hne].
- apply N1. apply in_or_app. left. exact H0.
- pose proof (sep_blocks tfibsegs B LAWS ly S W mem md p n0 p n HAR I1 I2
    ltac:(intros X; injection X; intros; lia)) as D0.
  destruct (al_blocks _ _ LAWS ly S W mem md p n0 HAR I1) as (_ & _ & _ & _ & _ & _ & Hm0).
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR I2) as (_ & _ & _ & _ & _ & _ & Hm1).
  assert (R0 : 0 < req_size n0) by (unfold req_size; destruct (Z.eqb_spec n0 0); lia).
  assert (R1 : 0 < req_size n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
  unfold zdisjoint in D0. cbn [fst snd] in D0. lia.
Qed.

(* no range of the entry's U is on a block appended after the entry's blocks (the entry's fs_heads put every range
   of c_U at the start of an entry block, and the block is fresh) *)
Lemma cnof_Uout : forall cx ly S (W : world tfibsegs) mem md L p m,
  cno_base B cx -> AR tfibsegs B ly S W mem md -> ablocks B ly S = ablocks B (c_ly cx) (c_S cx) ++ L ->
  In (p, m) L -> forall r, In r (c_U cx) -> fst r + snd r <= p \/ p + req_size m <= fst r.
Proof.
intros cx ly S W mem md L p m Hb HAR HE HL r Hr.
pose proof Hb as (_ & Hh0 & _).
destruct (Hh0 r Hr) as (E16 & m0 & Hm0 & M16).
pose proof (cnof_fresh ly S W mem md _ _ p m m0 HAR HE HL) as Hf.
assert (I1 : In (fst r, m0) (ablocks B ly S)) by (rewrite HE; apply in_or_app; left; exact Hm0).
assert (I2 : In (p, m) (ablocks B ly S)) by (rewrite HE; apply in_or_app; right; exact HL).
destruct (Z.eq_dec (fst r) p) as [Ep | Hne].
- exfalso. apply Hf. rewrite <- Ep. exact Hm0.
- pose proof (sep_blocks tfibsegs B LAWS ly S W mem md (fst r) m0 p m HAR I1 I2
    ltac:(intros X; injection X; intros; lia)) as D0.
  unfold zdisjoint in D0. cbn [fst snd] in D0. rewrite E16. lia.
Qed.

(* the head of an appended block is no range of the entry's U *)
Lemma cnof_head_notU : forall cx ly S (W : world tfibsegs) mem md L h n,
  cno_base B cx -> AR tfibsegs B ly S W mem md -> ablocks B ly S = ablocks B (c_ly cx) (c_S cx) ++ L ->
  In (h, n) L -> ~ In (h, HEAD) (c_U cx).
Proof.
intros cx ly S W mem md L h n Hb HAR HE HL HU.
pose proof Hb as (_ & Hh0 & _).
destruct (Hh0 _ HU) as (_ & m0 & Hm0 & _). cbn [fst] in Hm0.
exact (cnof_fresh ly S W mem md _ _ h n m0 HAR HE HL Hm0).
Qed.

(* the blocks after a free: the list without the freed block *)
Lemma cnof_rm : forall ly S (W : world tfibsegs) mem md A x R L',
  AR tfibsegs B ly S W mem md -> ablocks B ly S = A ++ x :: R ->
  (exists l1 l2, ablocks B ly S = l1 ++ x :: l2 /\ L' = l1 ++ l2) -> L' = A ++ R.
Proof.
intros ly S W mem md A x R L' HAR E (l1 & l2 & E1 & E2).
destruct (cnof_nodup ly S W mem md A x R HAR E) as (N1 & N2).
rewrite E in E1. destruct (cnof_split x A R l1 l2 N1 N2 E1) as (-> & ->). exact E2.
Qed.

Lemma cnof_blk_range : forall ly S (W : world tfibsegs) mem md p n,
  AR tfibsegs B ly S W mem md -> In (p, n) (ablocks B ly S) -> 0 <= p < 2 ^ 64 /\ p <> 0.
Proof.
intros ly S W mem md p n HAR H.
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR H) as (_ & H4096 & Hceil & _ & _ & _ & Hn).
pose proof (req_size_pos n ltac:(lia)) as (Hr1 & _). pose proof asan_consts as (C1 & _). lia.
Qed.

(* ================= the free calls' data ================= *)
Definition cnof_nz (xs : list Z) : list Z := List.filter (fun x => negb (x =? 0)) xs.
Definition cnof_qh (q : Z) : Z * Z := (q - HEAD, HEAD).
Definition cnof_qb (cx : cnocx) (q : Z) : Z * Z := (q - HEAD, FSH_Fn_writer.dec_size (c_db cx) + HEAD).
Definition cnof_rb (cx : cnocx) (p : Z) : Z * Z := (p, cno_n cx + 18).

Lemma cnof_nz_cons : forall x xs, x <> 0 -> cnof_nz (x :: xs) = x :: cnof_nz xs.
Proof.
intros x xs Hx. unfold cnof_nz. cbn [List.filter]. destruct (x =? 0) eqn:E; [apply Z.eqb_eq in E; lia | reflexivity].
Qed.

Lemma cnof_in_raw : forall cx (E L : list (Z * Z)) a b t, In (a, cno_n cx + 18) (E ++ cno_raw cx a b t ++ L).
Proof. intros. apply in_or_app. right. apply in_or_app. left. unfold cno_raw. left. reflexivity. Qed.

(* the state while fuzz_free args xs are still to come: the reader blocks among them (cnof_nz xs) are live, their
   heads in U, their bytes counted in g_live; every fuzz_free of a reader block is one event, of NULL none *)
Definition cnof_pend (cx : cnocx) (xs : list Z) (k : Z) (ly : alayout) (S : astate) (U : list (Z * Z))
  (W : world tfibsegs) (mem : word -> option byte) (a b t peak' : Z) : Prop :=
  U = c_U cx ++ map cnof_qh (cnof_nz xs) /\
  ablocks B ly S = ablocks B (c_ly cx) (c_S cx) ++ cno_raw cx a b t ++ map (cnof_qb cx) (cnof_nz xs) /\
  k = 9 - Z.of_nat (length (cnof_nz xs)) /\
  Forall (fun q => fs_rblock tfibsegs B ly S W mem q (FSH_Fn_writer.dec_size (c_db cx))) (cnof_nz xs) /\
  fs_glob tfibsegs W mem (c_live cx + Z.of_nat (length (cnof_nz xs)) * FSH_Fn_writer.dec_size (c_db cx)) peak'
    (c_cnt cx + 3) (c_fail cx).

Lemma cnof_rblocks_kept : forall cx ly S ly' S' (W W' : world tfibsegs) mem mem' qs,
  (forall p n i, In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n ->
     aview tfibsegs (w_H W') mem' (p + i) = aview tfibsegs (w_H W) mem (p + i)) ->
  (forall q, In q qs -> In (cnof_qb cx q) (ablocks B ly' S')) ->
  Forall (fun q => fs_rblock tfibsegs B ly S W mem q (FSH_Fn_writer.dec_size (c_db cx))) qs ->
  Forall (fun q => fs_rblock tfibsegs B ly' S' W' mem' q (FSH_Fn_writer.dec_size (c_db cx))) qs.
Proof.
intros cx ly S ly' S' W W' mem mem' qs HK Hin Hqs.
apply Forall_forall. intros q Hq.
destruct (proj1 (Forall_forall _ _) Hqs q Hq) as (Hb & H16 & Hn & Hv).
split; [exact (Hin q Hq)|]. split; [exact H16|]. split; [exact Hn|].
intros j Hj.
rewrite (mbyte_of_aview tfibsegs (w_H W) (w_H W') mem mem'); [exact (Hv j Hj)|].
pose proof (req_size_pos (FSH_Fn_writer.dec_size (c_db cx) + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hrq).
apply (HK (q - HEAD) (FSH_Fn_writer.dec_size (c_db cx) + HEAD) (Z.of_nat j) Hb (Hin q Hq)). unfold HEAD in *. lia.
Qed.

(* a run that keeps the ledger cells and the live blocks' bytes keeps cnof_pend *)
Lemma cnof_pend_mem : forall cx xs k ly S U (W : world tfibsegs) m m' a b t peak',
  (forall x, inFP FS_PSTAT_FP x -> aview tfibsegs (w_H W) m' x = aview tfibsegs (w_H W) m x) ->
  (forall p n i, In (p, n) (ablocks B ly S) -> 0 <= i < req_size n ->
     aview tfibsegs (w_H W) m' (p + i) = aview tfibsegs (w_H W) m (p + i)) ->
  cnof_pend cx xs k ly S U W m a b t peak' -> cnof_pend cx xs k ly S U W m' a b t peak'.
Proof.
intros cx xs k ly S U W m m' a b t peak' KL KB (EU & Eab & Ek & Hrb & Hg).
split; [exact EU|]. split; [exact Eab|]. split; [exact Ek|]. split.
- apply (cnof_rblocks_kept cx ly S ly S W W m m' _); [intros p n i H1 _ H3; exact (KB p n i H1 H3) | | exact Hrb].
  intros q Hq. rewrite Eab. apply in_or_app. right. apply in_or_app. right. apply in_map. exact Hq.
- exact (cno_glob_ledger W W m m' _ _ _ _ KL Hg).
Qed.

(* ================= the boundary machine and its registers ================= *)
Lemma cnof_frame : forall cx k ly S U (W : world tfibsegs) mem md,
  cno_J B cx k ly S W (unpoison U mem) md -> ARU tfibsegs B ly S U W mem md ->
  In (1, c_fpos cx) (frames S) /\ ly_F ly = ly_F (c_ly cx) /\ cno_F cx = frame_addr ly 1 (c_fpos cx) /\
  0 <= cno_F cx < 2 ^ 64 /\ 0 <= cno_SF cx < 2 ^ 64.
Proof.
intros cx k ly S U W mem md HJ HARU.
pose proof HJ as (_ & Hly & _ & _ & _ & Hfrs & _).
assert (Hin : In (1, c_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (EF : ly_F ly = ly_F (c_ly cx)) by (destruct Hly as (_ & _ & _ & _ & _ & X & _); exact X).
assert (EFa : cno_F cx = frame_addr ly 1 (c_fpos cx)) by (unfold cno_F, frame_addr; rewrite EF; reflexivity).
pose proof (ARU_AR tfibsegs B ly S U W mem md HARU) as HAR.
destruct (frames_bounds tfibsegs B LAWS ly S W (unpoison U mem) md 1 (c_fpos cx) HAR Hin) as (HF4096 & HFceil & _).
rewrite <- EFa in HF4096, HFceil. change (fs_frame_bytes 1) with 128 in HFceil.
pose proof asan_consts as (CA1 & CA2 & CA3 & CA4 & CA5).
pose proof (YCbq.shadow_addr_bounds (cno_F cx) ltac:(lia)) as (Hs1 & Hs2).
split; [exact Hin|]. split; [exact EF|]. split; [exact EFa|]. split; [lia|].
unfold cno_SF. lia.
Qed.

Lemma cnof_core_u : forall cx E k ly S U (W : world tfibsegs) mem md,
  cno_base B cx -> cno_core cx E -> cno_J B cx k ly S W (unpoison U mem) md -> ARU tfibsegs B ly S U W mem md ->
  bv_unsigned (ew E 8) = cno_sp0 cx /\ bv_unsigned (ew E 9) = cno_sp1 cx /\
  bv_unsigned (ew E 19) = cno_F cx /\ bv_unsigned (ew E 18) = cno_SF cx.
Proof.
intros cx E k ly S U W mem md Hb (C2 & C8 & C9 & C18 & C19 & C3 & C4) HJ HARU.
pose proof (cno_nums B cx Hb) as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
pose proof asan_consts as (CA1 & CA2 & CA3 & CA4 & CA5). pose proof cno_stk as FS.
destruct (cnof_frame cx k ly S U W mem md HJ HARU) as (_ & _ & _ & HF & HSF).
rewrite C8, C9, C19, C18. unfold w64.
split; [apply wz; lia|]. split; [apply wz; lia|]. split; apply wz; lia.
Qed.

Lemma cnof_kept : forall regs regs' xs (rr : bv 5) n w, aregs_preserved regs regs' ->
  Z.of_nat n = bv_unsigned rr -> acallee_saved (bv_unsigned rr) -> getr regs rr = w -> ew (Ereg regs' xs) n = w.
Proof. intros regs regs' xs rr n w HP Hn Hc H. rewrite (ew_Ereg_nat regs' xs n rr Hn), (fsw_pres regs regs' rr HP Hc). exact H. Qed.

Lemma cnof_core_pres : forall cx regs regs' xs,
  aregs_preserved regs regs' ->
  getr regs 2 = w64 (cno_sp1 cx) -> getr regs 8 = w64 (cno_sp0 cx) -> getr regs 9 = w64 (cno_sp1 cx) ->
  getr regs 18 = w64 (cno_SF cx) -> getr regs 19 = w64 (cno_F cx) ->
  getr regs 3 = getr (c_regs cx) 3 -> getr regs 4 = getr (c_regs cx) 4 ->
  cno_core cx (Ereg regs' xs).
Proof.
intros cx regs regs' xs HP R2 R8 R9 R18 R19 R3 R4. unfold cno_core.
split; [exact (cnof_kept regs regs' xs 2%bv 2 _ HP eq_refl ltac:(cno_cs) R2)|].
split; [exact (cnof_kept regs regs' xs 8%bv 8 _ HP eq_refl ltac:(cno_cs) R8)|].
split; [exact (cnof_kept regs regs' xs 9%bv 9 _ HP eq_refl ltac:(cno_cs) R9)|].
split; [exact (cnof_kept regs regs' xs 18%bv 18 _ HP eq_refl ltac:(cno_cs) R18)|].
split; [exact (cnof_kept regs regs' xs 19%bv 19 _ HP eq_refl ltac:(cno_cs) R19)|].
split; [exact (cnof_kept regs regs' xs 3%bv 3 _ HP eq_refl ltac:(cno_cs) R3)|].
exact (cnof_kept regs regs' xs 4%bv 4 _ HP eq_refl ltac:(cno_cs) R4).
Qed.

Lemma cnof_E_xs : forall cx regs A Bp T extra, cno_E cx (Ereg regs (cno_xs cx A Bp T extra)).
Proof.
intros cx regs A Bp T extra. unfold cno_E, cno_xs. split; [|split; [|split]].
- change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. reflexivity.
- intros j Hj. change (33 + j)%nat with (32 + S j)%nat. rewrite ew_Ereg_extra.
  do 13 (destruct j as [|j]; [reflexivity|]). lia.
- change 46%nat with (32 + 14)%nat. rewrite ew_Ereg_extra. reflexivity.
- change 47%nat with (32 + 15)%nat. rewrite ew_Ereg_extra. reflexivity.
Qed.

Lemma cnof_xs48 : forall cx regs A Bp T extra, ew (Ereg regs (cno_xs cx A Bp T extra)) 48 = w64 A.
Proof. intros. unfold cno_xs. change 48%nat with (32 + 16)%nat. rewrite ew_Ereg_extra. reflexivity. Qed.

(* the later free arguments, kept in callee-saved registers across a call *)
Lemma cnof_args_pres : forall regs regs' xs (rs : list (bv 5)) ps,
  aregs_preserved regs regs' -> Forall (fun rr => acallee_saved (bv_unsigned rr)) rs ->
  Forall2 (fun rr y => getr regs rr = w64 y) rs ps ->
  Forall2 (fun rr y => ew (Ereg regs' xs) (Z.to_nat (bv_unsigned rr)) = w64 y) rs ps.
Proof.
intros regs regs' xs rs ps HP Hrs H. revert Hrs.
induction H as [|rr y rs' ps' Hy H IH]; intros Hrs; [constructor|].
constructor; [|exact (IH (Forall_inv_tail Hrs))].
pose proof (Forall_inv Hrs) as Hc. cbv beta in Hc, Hy |- *.
pose proof (bv_unsigned_in_range _ rr) as Hrg.
rewrite (ew_Ereg_nat regs' xs (Z.to_nat (bv_unsigned rr)) rr ltac:(rewrite Z2Nat.id; [reflexivity | lia])).
rewrite (fsw_pres regs regs' rr HP Hc). exact Hy.
Qed.

(* the boundary machine at a call, read off the run's state: cno_mframe (the saved words, the flag word and the two
   slots from the state's regions, the kept registers from its register file) *)
Lemma cnof_mframe_of_st : forall cx E ss (W : world tfibsegs) ms k ly S U md A,
  cno_base B cx -> cno_E cx E -> cno_core cx E -> ew E 48 = w64 A -> 0 <= A < 2 ^ 64 ->
  st_ok tfibsegs E ss (restrict (w_H W) ms) ->
  cno_J B cx k ly S W (unpoison U (ms_mem ms)) md -> ARU tfibsegs B ly S U W (ms_mem ms) md ->
  FSupoisonU.fs_heads B ly S U ->
  nth_error (ss_mem ss) 0 = Some (fs_ret_s0_region (-104) 0 cno_sv_chunks) ->
  nth_error (ss_mem ss) 1 = Some (cno_fr_region 19 cno_flag_chunk) ->
  nth_error (ss_mem ss) 3 = Some (cno_sl_region cno_sl10) ->
  sr_get (ss_regs ss) 2%bv = SOff 2 0 -> sr_get (ss_regs ss) 8%bv = SOff 8 0 -> sr_get (ss_regs ss) 9%bv = SOff 9 0 ->
  sr_get (ss_regs ss) 18%bv = SOff 18 0 -> sr_get (ss_regs ss) 19%bv = SOff 19 0 ->
  sr_get (ss_regs ss) 3%bv = SOff 3 0 -> sr_get (ss_regs ss) 4%bv = SOff 4 0 ->
  cno_mframe B cx k ly S U W (ms_regs ms) (ms_mem ms) md A.
Proof.
intros cx E ss W ms k ly S U md A Hb HE Hc E48 HA HS HJ HARU Hh H0 H1 H3 G2 G8 G9 G18 G19 G3 G4.
destruct (cnof_core_u cx E k ly S U W (ms_mem ms) md Hb Hc HJ HARU) as (U8 & U9 & U19 & U18).
destruct (cnof_frame cx k ly S U W (ms_mem ms) md HJ HARU) as (_ & _ & _ & HF64 & _).
pose proof Hc as (C2 & C8 & C9 & C18 & C19 & C3 & C4).
pose proof HE as (_ & HE33 & HE46 & _).
pose proof (fsw_region_nth _ _ _ 0 _ HS H0) as HR0. cbn [ms_mem restrict] in HR0.
pose proof (fsw_region_nth _ _ _ 1 _ HS H1) as HR1. cbn [ms_mem restrict] in HR1.
pose proof (fsw_region_nth _ _ _ 3 _ HS H3) as HR3. cbn [ms_mem restrict] in HR3.
split; [exact HJ|]. split; [exact HARU|]. split; [exact Hh|].
split; [rewrite (cno_reg _ E ss ms 2%bv 2 HS G2); exact C2|].
split; [rewrite (cno_reg _ E ss ms 8%bv 8 HS G8); exact C8|].
split; [rewrite (cno_reg _ E ss ms 9%bv 9 HS G9); exact C9|].
split; [rewrite (cno_reg _ E ss ms 18%bv 18 HS G18); exact C18|].
split; [rewrite (cno_reg _ E ss ms 19%bv 19 HS G19); exact C19|].
split; [rewrite (cno_reg _ E ss ms 3%bv 3 HS G3); exact C3|].
split; [rewrite (cno_reg _ E ss ms 4%bv 4 HS G4); exact C4|].
split.
{ intros j Hj.
  replace (cno_sp0 cx - 8 * (Z.of_nat j + 1)) with (cno_sp0 cx + - 8 * (Z.of_nat j + 1)) by lia.
  apply (fsw_field _ _ 8 _ _ _ _ _ _ (- 8 * (Z.of_nat j + 1)) 8%N (SOff (33 + j) 0)
    (bv_unsigned (getr (c_regs cx) (nth j cno_saved_regs 0%bv))) HR0 U8).
  - unfold cno_sv_chunks. apply in_map_iff. exists j. split; [reflexivity|]. apply in_seq. lia.
  - rewrite fsw_SOff0, (HE33 j Hj). symmetry. apply Z_to_bv_bv_unsigned.
  - apply u64_range.
  - cbn. lia. }
split.
{ apply (fsw_field _ _ 19 _ _ _ _ _ _ 120 8%N (SOff 46 0) (bv_unsigned (w64 (cno_FL cx))) HR1 U19).
  - cbn. tauto.
  - rewrite fsw_SOff0, HE46. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - apply u64_range.
  - cbn. lia. }
split.
{ apply (fsw_field _ _ 9 _ _ _ _ _ _ 16 8%N (SOff 19 0) (cno_F cx) HR3 U9).
  - cbn. tauto.
  - rewrite fsw_SOff0, C19. reflexivity.
  - exact HF64.
  - cbn. lia. }
apply (fsw_field _ _ 9 _ _ _ _ _ _ 24 8%N (SOff 48 0) A HR3 U9).
- cbn. tauto.
- rewrite fsw_SOff0, E48. reflexivity.
- exact HA.
- cbn. lia.
Qed.

(* ================= the return boundaries of segment F ================= *)
(* the return of a fuzz_free call: the later free arguments in the registers rs *)
Definition cnof_RF (rs : list (bv 5)) : cno_inv := fun cx E k ly3 S3 U3 W3 ms3 md3 => exists a b t peak' xs,
  cno_core cx E /\ ew E 48 = w64 a /\ ew E 20 = w64 b /\ ew E 21 = w64 t /\
  Forall2 (fun rr y => ew E (Z.to_nat (bv_unsigned rr)) = w64 y) rs xs /\ c_peak cx <= peak' /\
  cnof_pend cx xs k ly3 S3 U3 W3 (ms_mem ms3) a b t peak' /\ FSupoisonU.fs_heads B ly3 S3 U3.
(* the return of a __wrap_free call: the raw blocks still live, in the registers rs *)
Definition cnof_RW (rs : list (bv 5)) : cno_inv := fun cx E k ly3 S3 U3 W3 ms3 md3 => exists a peak' ps,
  cno_core cx E /\ ew E 48 = w64 a /\ 0 <= a < 2 ^ 64 /\
  Forall2 (fun rr y => ew E (Z.to_nat (bv_unsigned rr)) = w64 y) rs ps /\
  U3 = c_U cx /\ ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) ++ map (cnof_rb cx) ps /\
  k = 12 - Z.of_nat (length ps) /\ c_peak cx <= peak' /\
  fs_glob tfibsegs W3 (ms_mem ms3) (c_live cx) peak' (c_cnt cx + 3) (c_fail cx) /\ FSupoisonU.fs_heads B ly3 S3 U3.

(* the premises of cno_call_afree_T for a raw block of the walk *)
Lemma cnof_afree_facts : forall cx ly S (W : world tfibsegs) mem md p L,
  cno_base B cx -> AR tfibsegs B ly S W mem md ->
  ablocks B ly S = ablocks B (c_ly cx) (c_S cx) ++ (p, cno_n cx + 18) :: L ->
  In (p, cno_n cx + 18) (ablocks B ly S) /\ p <> 0 /\ ~ In (p, cno_n cx + 18) (ablocks B (c_ly cx) (c_S cx)) /\
  (forall r, In r (c_U cx) -> fst r + snd r <= p \/ p + req_size (cno_n cx + 18) <= fst r).
Proof.
intros cx ly S W mem md p L Hb HAR E.
assert (Hin : In (p, cno_n cx + 18) (ablocks B ly S)) by (rewrite E; apply in_or_app; right; left; reflexivity).
split; [exact Hin|].
split; [exact (proj2 (cnof_blk_range ly S W mem md p _ HAR Hin))|].
split; [exact (cnof_fresh ly S W mem md _ _ p _ _ HAR E (or_introl eq_refl))|].
exact (cnof_Uout cx ly S W mem md _ p _ Hb HAR E (or_introl eq_refl)).
Qed.

(* ================= the call steps, from a boundary machine ================= *)
Hypothesis FFC : cno_call_ffree_T B.
Hypothesis AFC : cno_call_afree_T B.

(* fuzz_free (x) at the boundary machine (ra r), the resume at r, the return boundary cnof_RF rs *)
Lemma cnof_ffree_step : forall (rs : list (bv 5)) (r : Z) x xs,
  (r = 0x81424 \/ r = 0x8142c \/ r = 0x81434) ->
  Forall (fun rr => acallee_saved (bv_unsigned rr)) rs ->
  cno_from B (cno_ss r 19 18 cno_flag_chunk cno_sl10) (cnof_RF rs) ->
  forall cx k ly S U (W : world tfibsegs) regs mem md a b t peak',
  cno_base B cx -> cno_mframe B cx k ly S U W regs mem md a ->
  getr regs 1 = w64 r -> getr regs 10 = w64 x -> getr regs 20%bv = w64 b -> getr regs 21%bv = w64 t ->
  Forall2 (fun rr y => getr regs rr = w64 y) rs xs ->
  c_peak cx <= peak' -> cnof_pend cx (x :: xs) k ly S U W mem a b t peak' ->
  SRr tfibsegs W (cfg_at tfibsegs A_fuzz_free regs mem md) (cno_post B cx).
Proof.
intros rs r x xs Hr Hrs HNX cx k ly S U W regs mem md a b t peak' Hb Hm R1 R10 R20 R21 Rxs Hpk Hpd.
pose proof Hm as (HJ & HARU & Hh & R2 & R8 & R9 & R18 & R19 & R3 & R4 & _).
pose proof (ARU_AR tfibsegs B ly S U W mem md HARU) as HAR.
assert (Hr4 : 4096 <= r < 2 ^ 64 /\ r mod 2 = 0) by (destruct Hr as [-> | [-> | ->]]; (split; [lia | reflexivity])).
assert (Hsite : cno_site B cx k ly S U W regs mem md)
  by exact (cno_site_of_mframe B cx k ly S U W regs mem md a r Hm R1 (proj1 Hr4) (proj2 Hr4)).
assert (Hra : getr regs 1 = w64 0x81424 \/ getr regs 1 = w64 0x8142c \/ getr regs 1 = w64 0x81434)
  by (rewrite R1; destruct Hr as [-> | [-> | ->]]; [left | right; left | right; right]; reflexivity).
assert (Era : raZ regs = r) by (unfold raZ; rewrite R1; unfold w64; apply wz; lia).
destruct Hpd as (EU & Eab & Ek & Hrb & Hg).
assert (HA : 0 <= a < 2 ^ 64)
  by exact (proj1 (cnof_blk_range ly S W (unpoison U mem) md a (cno_n cx + 18) HAR ltac:(rewrite Eab; apply cnof_in_raw))).
assert (Hk1 : k + 1 <= EV_check_no_overread) by (rewrite Ek; unfold EV_check_no_overread; lia).
destruct (Z.eq_dec x 0) as [Hx0 | Hx0].
- (* fuzz_free (NULL) after three refused decodes: nothing freed, no event *)
  subst x. change (cnof_nz (0 :: xs)) with (cnof_nz xs) in EU, Eab, Ek, Hrb, Hg.
  apply (SRr_bind tfibsegs _ _ _ _ (FFC cx k ly S U W regs mem md 0 (FSH_Fn_writer.dec_size (c_db cx)) _ _ _ _ Hb Hsite Hra R10
    Hg (or_introl eq_refl) Hk1)).
  cbv beta. intros W' c' _ [(_ & Hret) | (Hne & _)]; [|exfalso; exact (Hne eq_refl)].
  destruct (cno_mframe_resume B cx k ly S U W regs mem md a b t [] 0 U (fun _ => False) _ W' c' Hb Hm Hsite HA Hret
    ltac:(intros ? ? X; exact X) ltac:(intros ? ? X; exact X) ltac:(intros ? ? X; exact X))
    as (ly' & S' & regs' & mem' & md' & Ec & HJ' & HARU' & Hh' & HP & HBK & HZ & HPP & HS').
  cbv beta in HPP. destruct HPP as (Eab' & Hg').
  rewrite Era in Ec, HS'. subst c'.
  apply (HNX cx (Ereg regs' (cno_xs cx a b t [])) (k + 0) ly' S' U W' (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs))
    md' Hb (cnof_E_xs cx regs' a b t []) HJ' HARU'); [|exact HS'].
  unfold cnof_RF. exists a, b, t, peak', xs. cbn [ms_mem].
  split; [exact (cnof_core_pres cx regs regs' _ HP R2 R8 R9 R18 R19 R3 R4)|].
  split; [exact (cnof_xs48 cx regs' a b t [])|].
  split; [exact (cnof_kept regs regs' _ 20%bv 20 _ HP eq_refl ltac:(cno_cs) R20)|].
  split; [exact (cnof_kept regs regs' _ 21%bv 21 _ HP eq_refl ltac:(cno_cs) R21)|].
  split; [exact (cnof_args_pres regs regs' _ rs xs HP Hrs Rxs)|].
  split; [exact Hpk|].
  split; [|exact Hh'].
  split; [exact EU|]. split; [rewrite Eab'; exact Eab|]. split; [lia|].
  split; [|exact Hg'].
  apply (cnof_rblocks_kept cx ly S ly' S' W W' mem mem' _); [| |exact Hrb].
  + intros p n i H1 H2 H3. exact (HBK p n i H1 H2 H3 (fun X => X)).
  + intros q Hq. rewrite Eab', Eab. apply in_or_app. right. apply in_or_app. right. apply in_map. exact Hq.
- (* fuzz_free (q): the reader block q is freed, its head leaves U *)
  rewrite (cnof_nz_cons x xs Hx0) in EU, Eab, Ek, Hrb, Hg.
  pose proof (Forall_inv Hrb) as Hrbx. pose proof (Forall_inv_tail Hrb) as Hrbs. cbv beta in Hrbx.
  assert (Eab2 : ablocks B ly S =
    (ablocks B (c_ly cx) (c_S cx) ++ cno_raw cx a b t) ++ cnof_qb cx x :: map (cnof_qb cx) (cnof_nz xs))
    by (rewrite Eab, <- app_assoc; reflexivity).
  destruct (cnof_nodup ly S W (unpoison U mem) md _ _ _ HAR Eab2) as (N1 & N2).
  assert (Hfr : ~ In (x - HEAD, FSH_Fn_writer.dec_size (c_db cx) + HEAD) (ablocks B (c_ly cx) (c_S cx)))
    by (intros X; apply N1; apply in_or_app; left; exact X).
  assert (HnU : ~ In (x - HEAD, HEAD) (c_U cx)).
  { apply (cnof_head_notU cx ly S W (unpoison U mem) md (cno_raw cx a b t ++ map (cnof_qb cx) (x :: cnof_nz xs)) _
      (FSH_Fn_writer.dec_size (c_db cx) + HEAD) Hb HAR Eab).
    apply in_or_app. right. left. reflexivity. }
  assert (Hnq : ~ In (x - HEAD, HEAD) (map cnof_qh (cnof_nz xs))).
  { intros X. apply in_map_iff in X as (y & Ey & Hy). apply (f_equal fst) in Ey. unfold cnof_qh in Ey. cbn [fst] in Ey.
    apply N2. replace x with y by lia. apply in_map. exact Hy. }
  assert (Hd0 : 0 <= FSH_Fn_writer.dec_size (c_db cx)).
  { unfold FSH_Fn_writer.dec_size. pose proof (Z.div_pos (Z.of_nat (length (c_db cx))) 4 ltac:(lia) ltac:(lia)). lia. }
  pose proof Hb as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hg0 & _).
  pose proof Hg0 as (_ & _ & _ & _ & (Hl0 & _) & _).
  assert (Hlen : Z.of_nat (length (x :: cnof_nz xs)) = Z.of_nat (length (cnof_nz xs)) + 1) by (cbn [length]; lia).
  assert (Hmul : 0 <= Z.of_nat (length (cnof_nz xs)) * FSH_Fn_writer.dec_size (c_db cx))
    by (apply Z.mul_nonneg_nonneg; lia).
  assert (Hlive : FSH_Fn_writer.dec_size (c_db cx) <=
    c_live cx + Z.of_nat (length (x :: cnof_nz xs)) * FSH_Fn_writer.dec_size (c_db cx))
    by (rewrite Hlen, Z.mul_add_distr_r, Z.mul_1_l; lia).
  apply (SRr_bind tfibsegs _ _ _ _ (FFC cx k ly S U W regs mem md x (FSH_Fn_writer.dec_size (c_db cx)) _ _ _ _ Hb Hsite Hra R10
    Hg (or_intror (conj Hx0 (conj (ex_intro _ (c_U cx) (ex_intro _ (map cnof_qh (cnof_nz xs)) EU))
      (conj Hrbx (conj Hlive Hfr))))) Hk1)).
  cbv beta. intros W' c' _ [(Hx' & _) | (_ & U1 & U2 & EU12 & Hret)]; [exfalso; exact (Hx0 Hx')|].
  rewrite EU in EU12.
  destruct (cnof_split (x - HEAD, HEAD) (c_U cx) (map cnof_qh (cnof_nz xs)) U1 U2 HnU Hnq EU12) as (-> & ->).
  destruct (cno_mframe_resume B cx k ly S U W regs mem md a b t [] 1 (c_U cx ++ map cnof_qh (cnof_nz xs))
    (fun _ => False) _ W' c' Hb Hm Hsite HA Hret
    ltac:(intros ? ? X; exact X) ltac:(intros ? ? X; exact X) ltac:(intros ? ? X; exact X))
    as (ly' & S' & regs' & mem' & md' & Ec & HJ' & HARU' & Hh' & HP & HBK & HZ & HPP & HS').
  cbv beta in HPP. destruct HPP as (Hrm & Hg').
  pose proof (cnof_rm ly S W (unpoison U mem) md _ _ _ _ HAR Eab2 Hrm) as Eab'.
  rewrite <- app_assoc in Eab'.
  rewrite Era in Ec, HS'. subst c'.
  apply (HNX cx (Ereg regs' (cno_xs cx a b t [])) (k + 1) ly' S' (c_U cx ++ map cnof_qh (cnof_nz xs)) W'
    (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs)) md' Hb (cnof_E_xs cx regs' a b t []) HJ' HARU'); [|exact HS'].
  unfold cnof_RF. exists a, b, t, peak', xs. cbn [ms_mem].
  split; [exact (cnof_core_pres cx regs regs' _ HP R2 R8 R9 R18 R19 R3 R4)|].
  split; [exact (cnof_xs48 cx regs' a b t [])|].
  split; [exact (cnof_kept regs regs' _ 20%bv 20 _ HP eq_refl ltac:(cno_cs) R20)|].
  split; [exact (cnof_kept regs regs' _ 21%bv 21 _ HP eq_refl ltac:(cno_cs) R21)|].
  split; [exact (cnof_args_pres regs regs' _ rs xs HP Hrs Rxs)|].
  split; [exact Hpk|].
  split; [|exact Hh'].
  split; [reflexivity|]. split; [exact Eab'|]. split; [rewrite Ek, Hlen; lia|].
  split.
  + apply (cnof_rblocks_kept cx ly S ly' S' W W' mem mem' _); [| |exact Hrbs].
    * intros p n i H1 H2 H3. exact (HBK p n i H1 H2 H3 (fun X => X)).
    * intros q Hq. rewrite Eab'. apply in_or_app. right. apply in_or_app. right. apply in_map. exact Hq.
  + replace (c_live cx + Z.of_nat (length (cnof_nz xs)) * FSH_Fn_writer.dec_size (c_db cx))
      with (c_live cx + Z.of_nat (length (x :: cnof_nz xs)) * FSH_Fn_writer.dec_size (c_db cx)
        - FSH_Fn_writer.dec_size (c_db cx)) by (rewrite Hlen, Z.mul_add_distr_r, Z.mul_1_l; lia).
    exact Hg'.
Qed.

(* __wrap_free (p) at the boundary machine (ra r, a raw block p of the walk), the resume at r, the return boundary
   cnof_RW rs *)
Lemma cnof_afree_step : forall (rs : list (bv 5)) (r : Z) p ps,
  (r = 0x8143c \/ r = 0x81444) ->
  Forall (fun rr => acallee_saved (bv_unsigned rr)) rs ->
  cno_from B (cno_ss r 19 18 cno_flag_chunk cno_sl10) (cnof_RW rs) ->
  forall cx k ly S U (W : world tfibsegs) regs mem md a peak',
  cno_base B cx -> cno_mframe B cx k ly S U W regs mem md a -> 0 <= a < 2 ^ 64 ->
  getr regs 1 = w64 r -> getr regs 10 = w64 p ->
  Forall2 (fun rr y => getr regs rr = w64 y) rs ps ->
  U = c_U cx -> ablocks B ly S = ablocks B (c_ly cx) (c_S cx) ++ map (cnof_rb cx) (p :: ps) ->
  k = 12 - Z.of_nat (length (p :: ps)) -> c_peak cx <= peak' ->
  fs_glob tfibsegs W mem (c_live cx) peak' (c_cnt cx + 3) (c_fail cx) ->
  SRr tfibsegs W (cfg_at tfibsegs PC_free regs mem md) (cno_post B cx).
Proof.
intros rs r p ps Hr Hrs HNX cx k ly S U W regs mem md a peak' Hb Hm HA R1 R10 Rps EU Eab Ek Hpk Hg.
subst U.
pose proof Hm as (HJ & HARU & Hh & R2 & R8 & R9 & R18 & R19 & R3 & R4 & _).
pose proof (ARU_AR tfibsegs B ly S (c_U cx) W mem md HARU) as HAR.
assert (Hr4 : 4096 <= r < 2 ^ 64 /\ r mod 2 = 0) by (destruct Hr as [-> | ->]; (split; [lia | reflexivity])).
assert (Hsite : cno_site B cx k ly S (c_U cx) W regs mem md)
  by exact (cno_site_of_mframe B cx k ly S (c_U cx) W regs mem md a r Hm R1 (proj1 Hr4) (proj2 Hr4)).
assert (Hra : getr regs 1 = w64 0x8143c \/ getr regs 1 = w64 0x81444 \/ getr regs 1 = w64 0x8144c)
  by (rewrite R1; destruct Hr as [-> | ->]; [left | right; left]; reflexivity).
assert (Era : raZ regs = r) by (unfold raZ; rewrite R1; unfold w64; apply wz; lia).
destruct (cnof_afree_facts cx ly S W (unpoison (c_U cx) mem) md p (map (cnof_rb cx) ps) Hb HAR Eab)
  as (Hin & Hp0 & Hfr & Hout).
assert (Hk1 : k + 1 <= EV_check_no_overread) by (rewrite Ek; cbn [length]; unfold EV_check_no_overread; lia).
apply (SRr_bind tfibsegs _ _ _ _ (AFC cx k ly S (c_U cx) W regs mem md p (cno_n cx + 18) (c_live cx) peak' (c_cnt cx + 3)
  (c_fail cx) Hb Hsite Hra R10 Hp0 Hin Hfr Hout Hg Hk1)).
cbv beta. intros W' c' _ Hret.
destruct (cno_mframe_resume B cx k ly S (c_U cx) W regs mem md a 0 0 [] 1 (c_U cx) (fun _ => False) _ W' c' Hb Hm Hsite
  HA Hret ltac:(intros ? ? X; exact X) ltac:(intros ? ? X; exact X) ltac:(intros ? ? X; exact X))
  as (ly' & S' & regs' & mem' & md' & Ec & HJ' & HARU' & Hh' & HP & HBK & HZ & HPP & HS').
cbv beta in HPP. destruct HPP as (Hrm & Hg').
pose proof (cnof_rm ly S W (unpoison (c_U cx) mem) md _ _ _ _ HAR Eab Hrm) as Eab'.
rewrite Era in Ec, HS'. subst c'.
apply (HNX cx (Ereg regs' (cno_xs cx a 0 0 [])) (k + 1) ly' S' (c_U cx) W' (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs))
  md' Hb (cnof_E_xs cx regs' a 0 0 []) HJ' HARU'); [|exact HS'].
unfold cnof_RW. exists a, peak', ps. cbn [ms_mem].
split; [exact (cnof_core_pres cx regs regs' _ HP R2 R8 R9 R18 R19 R3 R4)|].
split; [exact (cnof_xs48 cx regs' a 0 0 [])|].
split; [exact HA|].
split; [exact (cnof_args_pres regs regs' _ rs ps HP Hrs Rps)|].
split; [reflexivity|].
split; [exact Eab'|].
split; [rewrite Ek; cbn [length]; lia|].
split; [exact Hpk|].
split; [exact Hg' | exact Hh'].
Qed.

(* the last __wrap_free (t) (ra 0x8144c): the resume state is cno_ss_R (the slot 0x10 only), the boundary INV_R *)
Lemma cnof_afree_last : cno_from B cno_ss_R (INV_R B) ->
  forall cx k ly S U (W : world tfibsegs) regs mem md a p peak',
  cno_base B cx -> cno_mframe B cx k ly S U W regs mem md a ->
  getr regs 1 = w64 0x8144c -> getr regs 10 = w64 p ->
  U = c_U cx -> ablocks B ly S = ablocks B (c_ly cx) (c_S cx) ++ [(p, cno_n cx + 18)] ->
  k = 11 -> c_peak cx <= peak' ->
  fs_glob tfibsegs W mem (c_live cx) peak' (c_cnt cx + 3) (c_fail cx) ->
  SRr tfibsegs W (cfg_at tfibsegs PC_free regs mem md) (cno_post B cx).
Proof.
intros HNX cx k ly S U W regs mem md a p peak' Hb Hm R1 R10 EU Eab Ek Hpk Hg.
subst U.
pose proof Hm as (HJ & HARU & Hh & R2 & R8 & R9 & R18 & R19 & R3 & R4 & Hsv & HFL & HS16 & _).
pose proof (ARU_AR tfibsegs B ly S (c_U cx) W mem md HARU) as HAR.
destruct (cnof_frame cx k ly S (c_U cx) W mem md HJ HARU) as (_ & _ & _ & HF64 & _).
assert (Hsite : cno_site B cx k ly S (c_U cx) W regs mem md)
  by exact (cno_site_of_mframe B cx k ly S (c_U cx) W regs mem md a 0x8144c Hm R1 ltac:(lia) eq_refl).
assert (Era : raZ regs = 0x8144c) by (unfold raZ; rewrite R1; unfold w64; apply wz; lia).
destruct (cnof_afree_facts cx ly S W (unpoison (c_U cx) mem) md p [] Hb HAR Eab) as (Hin & Hp0 & Hfr & Hout).
assert (Hk1 : k + 1 <= EV_check_no_overread) by (rewrite Ek; unfold EV_check_no_overread; lia).
apply (SRr_bind tfibsegs _ _ _ _ (AFC cx k ly S (c_U cx) W regs mem md p (cno_n cx + 18) (c_live cx) peak' (c_cnt cx + 3)
  (c_fail cx) Hb Hsite (or_intror (or_intror R1)) R10 Hp0 Hin Hfr Hout Hg Hk1)).
cbv beta. intros W' c' _ Hret.
(* the resume chunks: the saved words, the flag word and the slot 0x10 (cno_mframe_resume's, without the slot 0x18) *)
assert (Hsv' : forall regs',
  Forall (YP09.chunk_ok tfibsegs (Ereg regs' (cno_xs cx a 0 0 [])) (mrestrict (w_H W) mem) (cno_sp0 cx)) cno_sv_chunks).
{ intros regs'. unfold cno_sv_chunks. cbn [seq map].
  assert (HX : forall j, (j < 13)%nat ->
    YP09.chunk_ok tfibsegs (Ereg regs' (cno_xs cx a 0 0 [])) (mrestrict (w_H W) mem) (cno_sp0 cx)
      (YP09.mkChunk (- 8 * (Z.of_nat j + 1)) (CVal 8 (SOff (33 + j) 0)))).
  { intros j Hj. apply (chunk_ok_val tfibsegs _ _ _ _ 8%N _ (bv_unsigned (getr (c_regs cx) (nth j cno_saved_regs 0%bv)))).
    - rewrite fsw_SOff0, Z_to_bv_bv_unsigned. change (33 + j)%nat with (32 + Datatypes.S j)%nat. unfold cno_xs.
      rewrite ew_Ereg_extra. do 13 (destruct j as [|j]; [reflexivity|]). lia.
    - apply u64_range.
    - cbn. lia.
    - replace (cno_sp0 cx + - 8 * (Z.of_nat j + 1)) with (cno_sp0 cx - 8 * (Z.of_nat j + 1)) by lia. exact (Hsv j Hj). }
  repeat apply Forall_cons; try apply Forall_nil;
  match goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk _ (CVal _ (SOff ?n _))) =>
    let j := eval cbv in (n - 33)%nat in exact (HX j ltac:(cbv; lia)) end. }
assert (HcsFb : Forall (fun c => 0 <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= 128 /\
  forall i, 0 <= i < YP09.c_len c -> ~ (fun _ : Z => False) (cno_F cx + YP09.c_off c + i)) cno_flag_chunk).
{ constructor; [|apply Forall_nil]. cbn. split; [lia|]. split; [lia|]. intros i _ X. exact X. }
assert (Hcsslb : Forall (fun c => 16 <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= 56 /\
  forall i, 0 <= i < YP09.c_len c -> ~ (fun _ : Z => False) (cno_sp1 cx + YP09.c_off c + i)) cno_cssl_R).
{ constructor; [|apply Forall_nil]. cbn. split; [lia|]. split; [lia|]. intros i _ X. exact X. }
assert (HcsF : forall regs', aregs_preserved regs regs' ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs' (cno_xs cx a 0 0 [])) (mrestrict (w_H W) mem) (cno_F cx)) cno_flag_chunk).
{ intros regs' _. constructor; [|apply Forall_nil].
  apply (chunk_ok_val tfibsegs _ _ _ _ 8%N _ (bv_unsigned (w64 (cno_FL cx)))); [| | cbn; lia | exact HFL].
  - rewrite fsw_SOff0, Z_to_bv_bv_unsigned. change 46%nat with (32 + 14)%nat. unfold cno_xs. rewrite ew_Ereg_extra.
    reflexivity.
  - apply u64_range. }
assert (Hcssl : forall regs', aregs_preserved regs regs' ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs' (cno_xs cx a 0 0 [])) (mrestrict (w_H W) mem) (cno_sp1 cx)) cno_cssl_R).
{ intros regs' HP. constructor; [|apply Forall_nil].
  apply (chunk_ok_val tfibsegs _ _ _ _ 8%N _ (cno_F cx)); [| exact HF64 | cbn; lia | exact HS16].
  rewrite fsw_SOff0, (ew_Ereg_nat regs' _ 19 19%bv eq_refl), (fsw_pres regs regs' 19%bv HP ltac:(cno_cs)), R19.
  reflexivity. }
destruct (cno_resume B cx k ly S (c_U cx) W regs mem md 1 (c_U cx) (fun _ => False) _ W' c' (cno_xs cx a 0 0 [])
  cno_flag_chunk cno_cssl_R Hb Hsite Hret R9 R18 R19 ltac:(intros ? ? X; exact X) ltac:(vm_compute; reflexivity)
  Hsv' HcsFb Hcsslb HcsF Hcssl)
  as (ly' & S' & regs' & mem' & md' & Ec & HJ' & HARU' & Hh' & HP & HBK & HZ & HPP & HS').
cbv beta in HPP. destruct HPP as (Hrm & Hg').
pose proof (cnof_rm ly S W (unpoison (c_U cx) mem) md _ _ _ _ HAR Eab Hrm) as Eab'. rewrite app_nil_r in Eab'.
rewrite Era in Ec, HS'. subst c'.
destruct (cnof_core_pres cx regs regs' (cno_xs cx a 0 0 []) HP R2 R8 R9 R18 R19 R3 R4)
  as (C2 & C8 & C9 & C18 & C19 & C3 & C4).
apply (HNX cx (Ereg regs' (cno_xs cx a 0 0 [])) (k + 1) ly' S' (c_U cx) W'
  (mkst regs' (Z_to_bv 64 0x8144c) mem' (seg_rom tfibsegs)) md' Hb (cnof_E_xs cx regs' a 0 0 []) HJ' HARU');
  [|exact HS'].
unfold INV_R. cbn [ms_mem].
split; [reflexivity|]. split; [exact Eab'|]. split; [rewrite Ek; reflexivity|].
split; [exact C2|]. split; [exact C8|]. split; [exact C9|]. split; [exact C18|]. split; [exact C19|].
split; [exact C3|]. split; [exact C4|].
exists peak'. split; [exact Hpk | exact Hg'].
Qed.

(* ================= the runs between the calls ================= *)
(* 0x81444 mv a0, s5; jal __wrap_free (ra 0x8144c): the free of t *)
Lemma cnof_hopW2 : cno_from B cno_ss_R (INV_R B) ->
  cno_from B (cno_ss 0x81444 19 18 cno_flag_chunk cno_sl10) (cnof_RW [21%bv]).
Proof.
intros HNX cx E k ly3 S3 U3 W3 ms3 md3 Hb HE HJ HARU HINV HS.
destruct HINV as (a & peak' & ps & Hc & E48 & HA & Hargs & EU & Eab & Ek & Hpk & Hg & Hh).
destruct (cnof_F2_cons Hargs) as (pt & ps1 & -> & E21 & Hargs1).
apply cnof_F2_nil in Hargs1. subst ps1. cbv beta in E21. subst U3.
pose proof (cno_nums B cx Hb) as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
pose proof asan_consts as (CA1 & CA2 & CA3 & CA4 & CA5). pose proof cno_stk as FS.
destruct (cnof_frame cx k ly3 S3 (c_U cx) W3 (ms_mem ms3) md3 HJ HARU) as (Hin & EF & EFa & _ & _).
destruct (cnof_core_u cx E k ly3 S3 (c_U cx) W3 (ms_mem ms3) md3 Hb Hc HJ HARU) as (U8 & U9 & U19 & U18).
fsw_aj_run_toU cno_tbl_ok HS HJ HARU PC_free.
{ eapply (cno_awr_ss B E _ _ _ _ _ ly3 _ (c_fpos cx) (cno_F cx) (cno_sp1 cx) _ _ _ U8 U19 U18 U9 EFa); lia. }
destruct (cno_run_keeps B cx E 0x81444 cno_flag_chunk cno_sl10 ly3 S3 (c_U cx) W3 (ms_mem ms) _ (ms_mem ms3) (ms_mem ms)
  Hb HARU Hin EF U8 U9 U19 U18 HF) as (KL & KB).
set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *.
lazymatch type of HS with st_ok _ _ ?ss _ => set (ssR := ss) in HS end.
assert (Hm : cno_mframe B cx k ly3 S3 (c_U cx) W3 (ms_regs ms) (ms_mem ms) md4 a)
  by (apply (cnof_mframe_of_st cx E ssR W3 ms k ly3 S3 (c_U cx) md4 a Hb HE Hc E48 HA HS HJ HARU Hh);
      vm_compute; reflexivity).
assert (R1 : getr (ms_regs ms) 1 = w64 0x8144c)
  by exact (fsw_reg_lit (w_H W3) E ssR ms 1%bv 0x8144c HS ltac:(vm_compute; reflexivity) ltac:(lia)).
assert (R10 : getr (ms_regs ms) 10 = w64 pt)
  by (rewrite (cno_reg _ E _ ms 10%bv 21 HS ltac:(vm_compute; reflexivity)); exact E21).
assert (Hg2 : fs_glob tfibsegs W3 (ms_mem ms) (c_live cx) peak' (c_cnt cx + 3) (c_fail cx))
  by exact (cno_glob_ledger W3 W3 (ms_mem ms3) (ms_mem ms) _ _ _ _
    (fun y Hy => aview_at tfibsegs (w_H W3) (ms_mem ms) (ms_mem ms3) y (KL y Hy)) Hg).
rewrite (st_ok_restrict_mkst tfibsegs (w_H W3) E ssR ms HS eq_refl).
replace (ss_pc ssR) with PC_free by (vm_compute; reflexivity).
change (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 PC_free) (ms_mem ms) (seg_rom tfibsegs)) md4)
  with (cfg_at tfibsegs PC_free (ms_regs ms) (ms_mem ms) md4).
exact (cnof_afree_last HNX cx k ly3 S3 (c_U cx) W3 (ms_regs ms) (ms_mem ms) md4 a pt peak' Hb Hm R1 R10 eq_refl Eab
  ltac:(rewrite Ek; reflexivity) Hpk Hg2).
Qed.

(* 0x8143c mv a0, s4; jal __wrap_free (ra 0x81444): the free of b *)
Lemma cnof_hopW1 : cno_from B (cno_ss 0x81444 19 18 cno_flag_chunk cno_sl10) (cnof_RW [21%bv]) ->
  cno_from B (cno_ss 0x8143c 19 18 cno_flag_chunk cno_sl10) (cnof_RW [20%bv; 21%bv]).
Proof.
intros HNX cx E k ly3 S3 U3 W3 ms3 md3 Hb HE HJ HARU HINV HS.
destruct HINV as (a & peak' & ps & Hc & E48 & HA & Hargs & EU & Eab & Ek & Hpk & Hg & Hh).
destruct (cnof_F2_cons Hargs) as (pb & ps1 & -> & E20 & Hargs1).
destruct (cnof_F2_cons Hargs1) as (pt & ps2 & -> & E21 & Hargs2).
apply cnof_F2_nil in Hargs2. subst ps2. cbv beta in E20, E21. subst U3.
pose proof (cno_nums B cx Hb) as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
pose proof asan_consts as (CA1 & CA2 & CA3 & CA4 & CA5). pose proof cno_stk as FS.
destruct (cnof_frame cx k ly3 S3 (c_U cx) W3 (ms_mem ms3) md3 HJ HARU) as (Hin & EF & EFa & _ & _).
destruct (cnof_core_u cx E k ly3 S3 (c_U cx) W3 (ms_mem ms3) md3 Hb Hc HJ HARU) as (U8 & U9 & U19 & U18).
fsw_aj_run_toU cno_tbl_ok HS HJ HARU PC_free.
{ eapply (cno_awr_ss B E _ _ _ _ _ ly3 _ (c_fpos cx) (cno_F cx) (cno_sp1 cx) _ _ _ U8 U19 U18 U9 EFa); lia. }
destruct (cno_run_keeps B cx E 0x8143c cno_flag_chunk cno_sl10 ly3 S3 (c_U cx) W3 (ms_mem ms) _ (ms_mem ms3) (ms_mem ms)
  Hb HARU Hin EF U8 U9 U19 U18 HF) as (KL & KB).
set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *.
lazymatch type of HS with st_ok _ _ ?ss _ => set (ssR := ss) in HS end.
assert (Hm : cno_mframe B cx k ly3 S3 (c_U cx) W3 (ms_regs ms) (ms_mem ms) md4 a)
  by (apply (cnof_mframe_of_st cx E ssR W3 ms k ly3 S3 (c_U cx) md4 a Hb HE Hc E48 HA HS HJ HARU Hh);
      vm_compute; reflexivity).
assert (R1 : getr (ms_regs ms) 1 = w64 0x81444)
  by exact (fsw_reg_lit (w_H W3) E ssR ms 1%bv 0x81444 HS ltac:(vm_compute; reflexivity) ltac:(lia)).
assert (R10 : getr (ms_regs ms) 10 = w64 pb)
  by (rewrite (cno_reg _ E _ ms 10%bv 20 HS ltac:(vm_compute; reflexivity)); exact E20).
assert (R21 : getr (ms_regs ms) 21%bv = w64 pt)
  by (rewrite (cno_reg _ E _ ms 21%bv 21 HS ltac:(vm_compute; reflexivity)); exact E21).
assert (Hg2 : fs_glob tfibsegs W3 (ms_mem ms) (c_live cx) peak' (c_cnt cx + 3) (c_fail cx))
  by exact (cno_glob_ledger W3 W3 (ms_mem ms3) (ms_mem ms) _ _ _ _
    (fun y Hy => aview_at tfibsegs (w_H W3) (ms_mem ms) (ms_mem ms3) y (KL y Hy)) Hg).
rewrite (st_ok_restrict_mkst tfibsegs (w_H W3) E ssR ms HS eq_refl).
replace (ss_pc ssR) with PC_free by (vm_compute; reflexivity).
change (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 PC_free) (ms_mem ms) (seg_rom tfibsegs)) md4)
  with (cfg_at tfibsegs PC_free (ms_regs ms) (ms_mem ms) md4).
exact (cnof_afree_step [21%bv] 0x81444 pb [pt] ltac:(right; reflexivity) ltac:(cnof_rs) HNX cx k ly3 S3 (c_U cx) W3
  (ms_regs ms) (ms_mem ms) md4 a peak' Hb Hm HA R1 R10 ltac:(constructor; [exact R21 | constructor]) eq_refl Eab Ek
  Hpk Hg2).
Qed.

(* 0x81434 ld a0, 0x18(s1); jal __wrap_free (ra 0x8143c): the free of a, after the three fuzz_free calls *)
Lemma cnof_hopF3 : cno_from B (cno_ss 0x8143c 19 18 cno_flag_chunk cno_sl10) (cnof_RW [20%bv; 21%bv]) ->
  cno_from B (cno_ss 0x81434 19 18 cno_flag_chunk cno_sl10) (cnof_RF []).
Proof.
intros HNX cx E k ly3 S3 U3 W3 ms3 md3 Hb HE HJ HARU HINV HS.
destruct HINV as (a & b & t & peak' & xs & Hc & E48 & E20 & E21 & Hargs & Hpk & Hpd & Hh).
apply cnof_F2_nil in Hargs. subst xs.
destruct Hpd as (EU & Eab & Ek & _ & Hg).
change (cnof_nz []) with (@nil Z) in EU, Eab, Ek, Hg. cbn [map] in EU, Eab. rewrite app_nil_r in EU, Eab.
change (Z.of_nat (length (@nil Z))) with 0 in Ek, Hg. rewrite Z.mul_0_l, Z.add_0_r in Hg. subst U3.
pose proof (cno_nums B cx Hb) as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
pose proof asan_consts as (CA1 & CA2 & CA3 & CA4 & CA5). pose proof cno_stk as FS.
pose proof (ARU_AR tfibsegs B ly3 S3 (c_U cx) W3 (ms_mem ms3) md3 HARU) as HAR3.
assert (HA : 0 <= a < 2 ^ 64)
  by exact (proj1 (cnof_blk_range ly3 S3 W3 _ md3 a (cno_n cx + 18) HAR3
    ltac:(rewrite Eab; apply in_or_app; right; unfold cno_raw; left; reflexivity))).
destruct (cnof_frame cx k ly3 S3 (c_U cx) W3 (ms_mem ms3) md3 HJ HARU) as (Hin & EF & EFa & _ & _).
destruct (cnof_core_u cx E k ly3 S3 (c_U cx) W3 (ms_mem ms3) md3 Hb Hc HJ HARU) as (U8 & U9 & U19 & U18).
fsw_aj_run_toU cno_tbl_ok HS HJ HARU PC_free.
{ eapply (cno_awr_ss B E _ _ _ _ _ ly3 _ (c_fpos cx) (cno_F cx) (cno_sp1 cx) _ _ _ U8 U19 U18 U9 EFa); lia. }
destruct (cno_run_keeps B cx E 0x81434 cno_flag_chunk cno_sl10 ly3 S3 (c_U cx) W3 (ms_mem ms) _ (ms_mem ms3) (ms_mem ms)
  Hb HARU Hin EF U8 U9 U19 U18 HF) as (KL & KB).
set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *.
lazymatch type of HS with st_ok _ _ ?ss _ => set (ssR := ss) in HS end.
assert (Hm : cno_mframe B cx k ly3 S3 (c_U cx) W3 (ms_regs ms) (ms_mem ms) md4 a)
  by (apply (cnof_mframe_of_st cx E ssR W3 ms k ly3 S3 (c_U cx) md4 a Hb HE Hc E48 HA HS HJ HARU Hh);
      vm_compute; reflexivity).
assert (R1 : getr (ms_regs ms) 1 = w64 0x8143c)
  by exact (fsw_reg_lit (w_H W3) E ssR ms 1%bv 0x8143c HS ltac:(vm_compute; reflexivity) ltac:(lia)).
assert (R10 : getr (ms_regs ms) 10 = w64 a)
  by (rewrite (cno_reg _ E _ ms 10%bv 48 HS ltac:(vm_compute; reflexivity)); exact E48).
assert (R20 : getr (ms_regs ms) 20%bv = w64 b)
  by (rewrite (cno_reg _ E _ ms 20%bv 20 HS ltac:(vm_compute; reflexivity)); exact E20).
assert (R21 : getr (ms_regs ms) 21%bv = w64 t)
  by (rewrite (cno_reg _ E _ ms 21%bv 21 HS ltac:(vm_compute; reflexivity)); exact E21).
assert (Hg2 : fs_glob tfibsegs W3 (ms_mem ms) (c_live cx) peak' (c_cnt cx + 3) (c_fail cx))
  by exact (cno_glob_ledger W3 W3 (ms_mem ms3) (ms_mem ms) _ _ _ _
    (fun y Hy => aview_at tfibsegs (w_H W3) (ms_mem ms) (ms_mem ms3) y (KL y Hy)) Hg).
rewrite (st_ok_restrict_mkst tfibsegs (w_H W3) E ssR ms HS eq_refl).
replace (ss_pc ssR) with PC_free by (vm_compute; reflexivity).
change (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 PC_free) (ms_mem ms) (seg_rom tfibsegs)) md4)
  with (cfg_at tfibsegs PC_free (ms_regs ms) (ms_mem ms) md4).
exact (cnof_afree_step [20%bv; 21%bv] 0x8143c a [b; t] ltac:(left; reflexivity) ltac:(cnof_rs) HNX cx k ly3 S3 (c_U cx)
  W3 (ms_regs ms) (ms_mem ms) md4 a peak' Hb Hm HA R1 R10
  ltac:(constructor; [exact R20 | constructor; [exact R21 | constructor]]) eq_refl Eab ltac:(rewrite Ek; reflexivity)
  Hpk Hg2).
Qed.

(* 0x8142c mv a0, s9; jal fuzz_free (ra 0x81434): the third fuzz_free *)
Lemma cnof_hopF2 : cno_from B (cno_ss 0x81434 19 18 cno_flag_chunk cno_sl10) (cnof_RF []) ->
  cno_from B (cno_ss 0x8142c 19 18 cno_flag_chunk cno_sl10) (cnof_RF [25%bv]).
Proof.
intros HNX cx E k ly3 S3 U3 W3 ms3 md3 Hb HE HJ HARU HINV HS.
destruct HINV as (a & b & t & peak' & xs & Hc & E48 & E20 & E21 & Hargs & Hpk & Hpd & Hh).
destruct (cnof_F2_cons Hargs) as (x3 & xs1 & -> & E25 & Hargs1).
apply cnof_F2_nil in Hargs1. subst xs1. cbv beta in E25.
pose proof (cno_nums B cx Hb) as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
pose proof asan_consts as (CA1 & CA2 & CA3 & CA4 & CA5). pose proof cno_stk as FS.
pose proof (ARU_AR tfibsegs B ly3 S3 U3 W3 (ms_mem ms3) md3 HARU) as HAR3.
assert (HA : 0 <= a < 2 ^ 64).
{ destruct Hpd as (_ & Eab & _).
  exact (proj1 (cnof_blk_range ly3 S3 W3 _ md3 a (cno_n cx + 18) HAR3 ltac:(rewrite Eab; apply cnof_in_raw))). }
destruct (cnof_frame cx k ly3 S3 U3 W3 (ms_mem ms3) md3 HJ HARU) as (Hin & EF & EFa & _ & _).
destruct (cnof_core_u cx E k ly3 S3 U3 W3 (ms_mem ms3) md3 Hb Hc HJ HARU) as (U8 & U9 & U19 & U18).
fsw_aj_run_toU cno_tbl_ok HS HJ HARU A_fuzz_free.
{ eapply (cno_awr_ss B E _ _ _ _ _ ly3 _ (c_fpos cx) (cno_F cx) (cno_sp1 cx) _ _ _ U8 U19 U18 U9 EFa); lia. }
destruct (cno_run_keeps B cx E 0x8142c cno_flag_chunk cno_sl10 ly3 S3 U3 W3 (ms_mem ms) _ (ms_mem ms3) (ms_mem ms)
  Hb HARU Hin EF U8 U9 U19 U18 HF) as (KL & KB).
set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *.
lazymatch type of HS with st_ok _ _ ?ss _ => set (ssR := ss) in HS end.
assert (Hm : cno_mframe B cx k ly3 S3 U3 W3 (ms_regs ms) (ms_mem ms) md4 a)
  by (apply (cnof_mframe_of_st cx E ssR W3 ms k ly3 S3 U3 md4 a Hb HE Hc E48 HA HS HJ HARU Hh);
      vm_compute; reflexivity).
assert (R1 : getr (ms_regs ms) 1 = w64 0x81434)
  by exact (fsw_reg_lit (w_H W3) E ssR ms 1%bv 0x81434 HS ltac:(vm_compute; reflexivity) ltac:(lia)).
assert (R10 : getr (ms_regs ms) 10 = w64 x3)
  by (rewrite (cno_reg _ E _ ms 10%bv 25 HS ltac:(vm_compute; reflexivity)); exact E25).
assert (R20 : getr (ms_regs ms) 20%bv = w64 b)
  by (rewrite (cno_reg _ E _ ms 20%bv 20 HS ltac:(vm_compute; reflexivity)); exact E20).
assert (R21 : getr (ms_regs ms) 21%bv = w64 t)
  by (rewrite (cno_reg _ E _ ms 21%bv 21 HS ltac:(vm_compute; reflexivity)); exact E21).
assert (Hpd2 : cnof_pend cx [x3] k ly3 S3 U3 W3 (ms_mem ms) a b t peak').
{ apply (cnof_pend_mem cx _ k ly3 S3 U3 W3 (ms_mem ms3) (ms_mem ms) a b t peak'); [| |exact Hpd].
  - intros y Hy. exact (aview_at tfibsegs (w_H W3) (ms_mem ms) (ms_mem ms3) y (KL y Hy)).
  - intros p n i Hp Hi. exact (aview_at tfibsegs (w_H W3) (ms_mem ms) (ms_mem ms3) (p + i) (KB p n i Hp Hi)). }
rewrite (st_ok_restrict_mkst tfibsegs (w_H W3) E ssR ms HS eq_refl).
replace (ss_pc ssR) with A_fuzz_free by (vm_compute; reflexivity).
change (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 A_fuzz_free) (ms_mem ms) (seg_rom tfibsegs)) md4)
  with (cfg_at tfibsegs A_fuzz_free (ms_regs ms) (ms_mem ms) md4).
exact (cnof_ffree_step [] 0x81434 x3 [] ltac:(right; right; reflexivity) ltac:(constructor) HNX cx k ly3 S3 U3 W3
  (ms_regs ms) (ms_mem ms) md4 a b t peak' Hb Hm R1 R10 R20 R21 ltac:(constructor) Hpk Hpd2).
Qed.

(* 0x81424 mv a0, s8; jal fuzz_free (ra 0x8142c): the second fuzz_free *)
Lemma cnof_hopF1 : cno_from B (cno_ss 0x8142c 19 18 cno_flag_chunk cno_sl10) (cnof_RF [25%bv]) ->
  cno_from B (cno_ss 0x81424 19 18 cno_flag_chunk cno_sl10) (cnof_RF [24%bv; 25%bv]).
Proof.
intros HNX cx E k ly3 S3 U3 W3 ms3 md3 Hb HE HJ HARU HINV HS.
destruct HINV as (a & b & t & peak' & xs & Hc & E48 & E20 & E21 & Hargs & Hpk & Hpd & Hh).
destruct (cnof_F2_cons Hargs) as (x2 & xs1 & -> & E24 & Hargs1).
destruct (cnof_F2_cons Hargs1) as (x3 & xs2 & -> & E25 & Hargs2).
apply cnof_F2_nil in Hargs2. subst xs2. cbv beta in E24, E25.
pose proof (cno_nums B cx Hb) as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
pose proof asan_consts as (CA1 & CA2 & CA3 & CA4 & CA5). pose proof cno_stk as FS.
pose proof (ARU_AR tfibsegs B ly3 S3 U3 W3 (ms_mem ms3) md3 HARU) as HAR3.
assert (HA : 0 <= a < 2 ^ 64).
{ destruct Hpd as (_ & Eab & _).
  exact (proj1 (cnof_blk_range ly3 S3 W3 _ md3 a (cno_n cx + 18) HAR3 ltac:(rewrite Eab; apply cnof_in_raw))). }
destruct (cnof_frame cx k ly3 S3 U3 W3 (ms_mem ms3) md3 HJ HARU) as (Hin & EF & EFa & _ & _).
destruct (cnof_core_u cx E k ly3 S3 U3 W3 (ms_mem ms3) md3 Hb Hc HJ HARU) as (U8 & U9 & U19 & U18).
fsw_aj_run_toU cno_tbl_ok HS HJ HARU A_fuzz_free.
{ eapply (cno_awr_ss B E _ _ _ _ _ ly3 _ (c_fpos cx) (cno_F cx) (cno_sp1 cx) _ _ _ U8 U19 U18 U9 EFa); lia. }
destruct (cno_run_keeps B cx E 0x81424 cno_flag_chunk cno_sl10 ly3 S3 U3 W3 (ms_mem ms) _ (ms_mem ms3) (ms_mem ms)
  Hb HARU Hin EF U8 U9 U19 U18 HF) as (KL & KB).
set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *.
lazymatch type of HS with st_ok _ _ ?ss _ => set (ssR := ss) in HS end.
assert (Hm : cno_mframe B cx k ly3 S3 U3 W3 (ms_regs ms) (ms_mem ms) md4 a)
  by (apply (cnof_mframe_of_st cx E ssR W3 ms k ly3 S3 U3 md4 a Hb HE Hc E48 HA HS HJ HARU Hh);
      vm_compute; reflexivity).
assert (R1 : getr (ms_regs ms) 1 = w64 0x8142c)
  by exact (fsw_reg_lit (w_H W3) E ssR ms 1%bv 0x8142c HS ltac:(vm_compute; reflexivity) ltac:(lia)).
assert (R10 : getr (ms_regs ms) 10 = w64 x2)
  by (rewrite (cno_reg _ E _ ms 10%bv 24 HS ltac:(vm_compute; reflexivity)); exact E24).
assert (R20 : getr (ms_regs ms) 20%bv = w64 b)
  by (rewrite (cno_reg _ E _ ms 20%bv 20 HS ltac:(vm_compute; reflexivity)); exact E20).
assert (R21 : getr (ms_regs ms) 21%bv = w64 t)
  by (rewrite (cno_reg _ E _ ms 21%bv 21 HS ltac:(vm_compute; reflexivity)); exact E21).
assert (R25 : getr (ms_regs ms) 25%bv = w64 x3)
  by (rewrite (cno_reg _ E _ ms 25%bv 25 HS ltac:(vm_compute; reflexivity)); exact E25).
assert (Hpd2 : cnof_pend cx [x2; x3] k ly3 S3 U3 W3 (ms_mem ms) a b t peak').
{ apply (cnof_pend_mem cx _ k ly3 S3 U3 W3 (ms_mem ms3) (ms_mem ms) a b t peak'); [| |exact Hpd].
  - intros y Hy. exact (aview_at tfibsegs (w_H W3) (ms_mem ms) (ms_mem ms3) y (KL y Hy)).
  - intros p n i Hp Hi. exact (aview_at tfibsegs (w_H W3) (ms_mem ms) (ms_mem ms3) (p + i) (KB p n i Hp Hi)). }
rewrite (st_ok_restrict_mkst tfibsegs (w_H W3) E ssR ms HS eq_refl).
replace (ss_pc ssR) with A_fuzz_free by (vm_compute; reflexivity).
change (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 A_fuzz_free) (ms_mem ms) (seg_rom tfibsegs)) md4)
  with (cfg_at tfibsegs A_fuzz_free (ms_regs ms) (ms_mem ms) md4).
exact (cnof_ffree_step [25%bv] 0x8142c x2 [x3] ltac:(right; left; reflexivity) ltac:(cnof_rs) HNX cx k ly3 S3 U3 W3
  (ms_regs ms) (ms_mem ms) md4 a b t peak' Hb Hm R1 R10 R20 R21 ltac:(constructor; [exact R25 | constructor]) Hpk Hpd2).
Qed.

(* ================= the first fuzz_free, from INV_F1 ================= *)
Lemma cnof_seg0 : cno_from B (cno_ss 0x81424 19 18 cno_flag_chunk cno_sl10) (cnof_RF [24%bv; 25%bv]) ->
  cno_at B A_fuzz_free (INV_F1 B).
Proof.
intros HNX cx k ly S U W regs mem md Hb HINV.
destruct HINV as (a & b & t & peak' & Hm & R1 & R20 & R21 & Hpk & Harms).
destruct Harms as [(Hdec & EU & Ek & Eab & R10 & _ & R24 & R25 & Hg)
  | (out & q1 & q2 & q3 & Hdec & EU & Ek & Eab & Hq1 & Hq2 & Hq3 & R10 & _ & R24 & R25 & Hr1 & Hr2 & Hr3 & Hg)].
- (* a bad text: the three fuzz_free arguments are NULL *)
  apply (cnof_ffree_step [24%bv; 25%bv] 0x81424 0 [0; 0] ltac:(left; reflexivity) ltac:(cnof_rs) HNX cx k ly S U W
    regs mem md a b t peak' Hb Hm R1 R10 R20 R21
    ltac:(constructor; [exact R24 | constructor; [exact R25 | constructor]]) Hpk).
  unfold cnof_pend. change (cnof_nz [0; 0; 0]) with (@nil Z). cbn [map length]. rewrite !app_nil_r.
  split; [exact EU|]. split; [exact Eab|]. split; [rewrite Ek; reflexivity|]. split; [constructor|].
  change (Z.of_nat 0) with 0. rewrite Z.mul_0_l, Z.add_0_r. exact Hg.
- (* the three reader blocks q1 .. q3 *)
  assert (N1 : q1 <> 0) by (unfold HEAD in *; lia).
  assert (N2 : q2 <> 0) by (unfold HEAD in *; lia).
  assert (N3 : q3 <> 0) by (unfold HEAD in *; lia).
  apply (cnof_ffree_step [24%bv; 25%bv] 0x81424 q1 [q2; q3] ltac:(left; reflexivity) ltac:(cnof_rs) HNX cx k ly S U W
    regs mem md a b t peak' Hb Hm R1 R10 R20 R21
    ltac:(constructor; [exact R24 | constructor; [exact R25 | constructor]]) Hpk).
  unfold cnof_pend. rewrite !cnof_nz_cons by assumption. change (cnof_nz []) with (@nil Z).
  split; [exact EU|]. split; [exact Eab|]. split; [rewrite Ek; reflexivity|].
  split; [constructor; [exact Hr1 | constructor; [exact Hr2 | constructor; [exact Hr3 | constructor]]]|].
  exact Hg.
Qed.

(* ================= segment F ================= *)
Lemma cno_segF : cno_segF_T B.
Proof.
intros HR. exact (cnof_seg0 (cnof_hopF1 (cnof_hopF2 (cnof_hopF3 (cnof_hopW1 (cnof_hopW2 HR)))))).
Qed.
End F.

About cno_segF.
Print Assumptions cno_segF.
