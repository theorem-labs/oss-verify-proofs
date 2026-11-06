(* The slot LLVMFuzzerTestOneInput (fuzz_link.c:764-790), plain image: locality of the memory views its cut
   predicates use (S-FR item 4). LFr.v defines `lcarry U m m'` (bytes and writability of the region U agree
   in m and m') and `mlocal U Pm` (Pm survives every lcarry U). Here:
   1. the combinators (mlocal_mono, mlocal_and, mlocal_ex, lcarry_mono, lcarry_trans, ...);
   2. one lemma per memory view, `mlocal <the bytes it reads> <the view>`;
   3. the form an allocator step uses: `lh_reg E` (the loop-head memory's region minus errno and the guard
      words), lh_mem_carry and lh_reg_keep (lh_reg lies in LFr's lkeep), and the same pair for the exit
      memory of ex_ms.
   Every address and size is link's (lib/Prog/link_mem.v, lib/Prog/link_spec.v, LDefs.v, the plain image). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Contract Img0 FrameAPI MemFile MemFileRI.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import AllocSlots AllocRoom.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import LLVMFuzzerTestOneInput_c link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LFr.
Import ListNotations.
Local Open Scope Z_scope.

(* ==========================================================================
   1. Combinators
   ========================================================================== *)

Lemma lcarry_refl : forall U m, lcarry U m m.
Proof. intros U m a _. split; [reflexivity | tauto]. Qed.

Lemma lcarry_sym : forall U m m', lcarry U m m' -> lcarry U m' m.
Proof. intros U m m' C a Ha. destruct (C a Ha) as [E W]. split; [symmetry; exact E | tauto]. Qed.

Lemma lcarry_mono : forall (U U' : Z -> Prop) m m', (forall a, U a -> U' a) -> lcarry U' m m' -> lcarry U m m'.
Proof. intros U U' m m' S C a Ha. exact (C a (S a Ha)). Qed.

Lemma lcarry_trans : forall U m1 m2 m3, lcarry U m1 m2 -> lcarry U m2 m3 -> lcarry U m1 m3.
Proof.
  intros U m1 m2 m3 C1 C2 a Ha. destruct (C1 a Ha) as [E1 W1]. destruct (C2 a Ha) as [E2 W2].
  split; [rewrite E2; exact E1 | tauto].
Qed.

Lemma lcarry_or : forall (U V : Z -> Prop) m m', lcarry U m m' -> lcarry V m m' ->
  lcarry (fun a => U a \/ V a) m m'.
Proof. intros U V m m' CU CV a [Ha|Ha]; [exact (CU a Ha) | exact (CV a Ha)]. Qed.

Lemma mlocal_mono : forall (U U' : Z -> Prop) (Pm : (word -> option byte) -> Prop),
  (forall a, U a -> U' a) -> mlocal U Pm -> mlocal U' Pm.
Proof. intros U U' Pm S L m m' C H. exact (L m m' (lcarry_mono U U' m m' S C) H). Qed.

Lemma mlocal_and : forall U (Pm Qm : (word -> option byte) -> Prop),
  mlocal U Pm -> mlocal U Qm -> mlocal U (fun m => Pm m /\ Qm m).
Proof. intros U Pm Qm LP LQ m m' C [HP HQ]. exact (conj (LP m m' C HP) (LQ m m' C HQ)). Qed.

(* the two regions of a conjunction together *)
Lemma mlocal_and_or : forall (U V : Z -> Prop) (Pm Qm : (word -> option byte) -> Prop),
  mlocal U Pm -> mlocal V Qm -> mlocal (fun a => U a \/ V a) (fun m => Pm m /\ Qm m).
Proof.
  intros U V Pm Qm LP LQ m m' C [HP HQ]. split.
  - exact (LP m m' (lcarry_mono U (fun a => U a \/ V a) m m' (fun a Ha => or_introl Ha) C) HP).
  - exact (LQ m m' (lcarry_mono V (fun a => U a \/ V a) m m' (fun a Ha => or_intror Ha) C) HQ).
Qed.

Lemma mlocal_or : forall U (Pm Qm : (word -> option byte) -> Prop),
  mlocal U Pm -> mlocal U Qm -> mlocal U (fun m => Pm m \/ Qm m).
Proof. intros U Pm Qm LP LQ m m' C [HP|HQ]; [left; exact (LP m m' C HP) | right; exact (LQ m m' C HQ)]. Qed.

(* an existential over a value the region does not depend on *)
Lemma mlocal_ex : forall {T : Type} U (Pm : T -> (word -> option byte) -> Prop),
  (forall t, mlocal U (Pm t)) -> mlocal U (fun m => exists t, Pm t m).
Proof. intros T U Pm L m m' C [t Ht]. exists t. exact (L t m m' C Ht). Qed.

Lemma mlocal_all : forall {T : Type} U (Pm : T -> (word -> option byte) -> Prop),
  (forall t, mlocal U (Pm t)) -> mlocal U (fun m => forall t, Pm t m).
Proof. intros T U Pm L m m' C H t. exact (L t m m' C (H t)). Qed.

Lemma mlocal_pure : forall U (P : Prop), mlocal U (fun _ => P).
Proof. intros U P m m' _ H. exact H. Qed.

Lemma mlocal_imp : forall U (P : Prop) (Pm : (word -> option byte) -> Prop),
  (P -> mlocal U Pm) -> mlocal U (fun m => P -> Pm m).
Proof. intros U P Pm L m m' C H HP. exact (L HP m m' C (H HP)). Qed.

Lemma mlocal_iff : forall U (Pm Qm : (word -> option byte) -> Prop),
  (forall m, Pm m <-> Qm m) -> mlocal U Pm -> mlocal U Qm.
Proof. intros U Pm Qm E L m m' C H. apply E. apply (L m m' C). apply E. exact H. Qed.

(* the form every use takes: a view, a carry over a larger region *)
Lemma ml_use : forall (U U' : Z -> Prop) (Pm : (word -> option byte) -> Prop) m m',
  mlocal U Pm -> lcarry U' m m' -> (forall a, U a -> U' a) -> Pm m -> Pm m'.
Proof. intros U U' Pm m m' L C S H. exact (L m m' (lcarry_mono U U' m m' S C) H). Qed.

(* ==========================================================================
   2. The views, each with the bytes it reads
   ========================================================================== *)

Definition lo_rng (a n x : Z) : Prop := a <= x < a + n.

Lemma ml_bytes_at : forall a bs, mlocal (lo_rng a (Z.of_nat (length bs))) (fun m => bytes_at rsegs m a bs).
Proof.
  intros a bs m m' C (H0 & H1 & H). split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (H i Hi).
  assert (Hr : lo_rng a (Z.of_nat (length bs)) (a + Z.of_nat i)) by (unfold lo_rng; lia).
  destruct (C _ Hr) as [E _]. exact E.
Qed.

Lemma ml_wr_at : forall a n, mlocal (lo_rng a n) (fun m => wr_at rsegs m a n).
Proof.
  intros a n m m' C (H0 & H1 & H). split; [exact H0|]. split; [exact H1|].
  intros i Hi. assert (Hr : lo_rng a n (a + i)) by (unfold lo_rng; lia).
  destruct (C _ Hr) as [_ W]. exact (proj1 W (H i Hi)).
Qed.

Lemma ml_rw_cells : forall A cs, mlocal (lo_rng A (Z.of_nat (cells_size cs))) (fun m => rw_cells rsegs m A cs).
Proof.
  intros A cs m m' C [[Hwf Hb] Hw]. split; [split; [exact Hwf|]|].
  - apply (ml_use _ _ _ m m' (ml_bytes_at A (cells_bytes cs)) C); [|exact Hb].
    intros x Hx. rewrite cells_bytes_length in Hx by exact Hwf. exact Hx.
  - exact (ml_wr_at A _ m m' C Hw).
Qed.

Lemma ml_u8arr : forall A bs, mlocal (lo_rng A (Z.of_nat (length bs))) (fun m => u8arr rsegs m A bs).
Proof. intros A bs m m' C [H W]. split; [exact (ml_bytes_at A bs m m' C H) | exact (ml_wr_at A _ m m' C W)]. Qed.

Lemma ml_u64_at : forall a v, mlocal (lo_rng a 8) (fun m => u64_at m a v).
Proof.
  intros a v m m' C H. unfold u64_at in *.
  apply (ml_use _ _ _ m m' (ml_bytes_at a (le8 (wz v))) C); [|exact H].
  intros x Hx. rewrite length_le8 in Hx. exact Hx.
Qed.

Lemma ml_u32_at : forall a v, mlocal (lo_rng a 4) (fun m => u32_at m a v).
Proof.
  intros a v m m' C H. unfold u32_at in *.
  apply (ml_use _ _ _ m m' (ml_bytes_at a (le4 (wz v))) C); [|exact H].
  intros x Hx. rewrite length_le4 in Hx. exact Hx.
Qed.

Lemma ml_u16_at : forall a v, mlocal (lo_rng a 2) (fun m => u16_at m a v).
Proof.
  intros a v m m' C H. unfold u16_at in *.
  apply (ml_use _ _ _ m m' (ml_bytes_at a (le2 (wz v))) C); [|exact H].
  intros x Hx. rewrite length_le2 in Hx. exact Hx.
Qed.

Lemma ml_cstr_at : forall a s, mlocal (lo_rng a (Z.of_nat (length s) + 1)) (fun m => cstr_at m a s).
Proof.
  intros a s m m' C [H Hn]. split; [|exact Hn].
  apply (ml_use _ _ _ m m' (ml_bytes_at a (s ++ [zb 0])) C); [|exact H].
  intros x Hx. rewrite length_app in Hx. cbn [length] in Hx. unfold lo_rng in *. lia.
Qed.

Lemma ml_tbuf_at : forall a cap bs, mlocal (lo_rng a (Z.max 0 cap + 1)) (fun m => tbuf_at m a cap bs).
Proof.
  intros a cap bs m m' C H. unfold tbuf_at in *.
  apply (ml_use _ _ _ m m' (ml_rw_cells _ _) C); [|exact H].
  intros x Hx. cbn [cells_size csize] in Hx. unfold lo_rng in *. lia.
Qed.

(* str_arg reads nothing when the argument is NULL *)
Definition lo_str_reg (a : Z) (o : option (list byte)) (x : Z) : Prop :=
  match o with Some s => lo_rng a (Z.of_nat (length s) + 1) x | None => False end.

Lemma ml_str_arg : forall a o, mlocal (lo_str_reg a o) (fun m => str_arg m a o).
Proof.
  intros a [s|] m m' C H; unfold str_arg in *.
  - destruct H as [Ha H]. split; [exact Ha|].
    apply (ml_use _ _ _ m m' (ml_cstr_at a s) C); [|exact H]. intros x Hx. exact Hx.
  - exact H.
Qed.

Lemma ml_buf_arg : forall a cap, mlocal (lo_rng a cap) (fun m => buf_arg m a cap).
Proof.
  intros a cap m m' C H Ha Hc. destruct (H Ha Hc) as [j Hj]. exists j.
  apply (ml_use _ _ _ m m' (ml_rw_cells _ _) C); [|exact Hj].
  intros x Hx. cbn [cells_size csize] in Hx. unfold lo_rng in *. lia.
Qed.

Lemma ml_nlk_at : forall kbs, mlocal (lo_rng A_G_NL NK_SIZE) (fun m => nlk_at m kbs).
Proof.
  intros kbs m m' C [H L]. split; [|exact L].
  apply (ml_use _ _ _ m m' (ml_u8arr _ _) C); [|exact H]. intros x Hx. rewrite L in Hx. exact Hx.
Qed.

Lemma ml_model_at : forall p bs, mlocal (lo_rng p MD_SIZE) (fun m => model_at m p bs).
Proof.
  intros p bs m m' C [H L]. split; [|exact L].
  apply (ml_use _ _ _ m m' (ml_u8arr _ _) C); [|exact H]. intros x Hx. rewrite L in Hx. exact Hx.
Qed.

Lemma ml_marks_at : forall p bs, mlocal (lo_rng p MK_SIZE) (fun m => marks_at m p bs).
Proof.
  intros p bs m m' C [H L]. split; [|exact L].
  apply (ml_use _ _ _ m m' (ml_u8arr _ _) C); [|exact H]. intros x Hx. rewrite L in Hx. exact Hx.
Qed.

Lemma ml_nlw_at : forall p bs, mlocal (lo_rng p NW_SIZE) (fun m => nlw_at m p bs).
Proof.
  intros p bs m m' C [H L]. split; [|exact L].
  apply (ml_use _ _ _ m m' (ml_u8arr _ _) C); [|exact H]. intros x Hx. rewrite L in Hx. exact Hx.
Qed.

Lemma ml_cursor_ok : forall p0 pl P N,
  mlocal (lo_rng p0 (Z.of_nat (length pl))) (fun m => cursor_ok m p0 pl P N).
Proof. intros p0 pl P N m m' C [H K]. split; [exact (ml_bytes_at p0 pl m m' C H) | exact K]. Qed.

Lemma ml_stk : forall lo hi, mlocal (lo_rng lo (hi - lo)) (fun m => stk rsegs m lo hi).
Proof.
  intros lo hi m m' C (H0 & H1 & H). split; [exact H0|]. split; [exact H1|].
  intros a Ha. destruct (H a Ha) as [W [b R]].
  assert (Hr : lo_rng lo (hi - lo) a) by (unfold lo_rng; lia).
  destruct (C _ Hr) as [E Wi]. split.
  - exact (proj1 Wi W).
  - exists b. rewrite <- R. exact E.
Qed.

(* the two guard words: the GOT slot holds &guard; the guard holds some word *)
Definition lo_guard_reg (x : Z) : Prop := lo_rng A_GOT_GUARD_S 8 x \/ lo_rng A_GUARD_S 8 x.

Lemma ml_guard_m : mlocal lo_guard_reg guard_m.
Proof.
  intros m m' C [H1 [c H2]]. split.
  - apply (ml_use _ _ _ m m' (ml_bytes_at _ _) C); [|exact H1].
    intros x Hx. left. rewrite length_le8 in Hx. exact Hx.
  - exists c. apply (ml_use _ _ _ m m' (ml_bytes_at _ _) C); [|exact H2].
    intros x Hx. right. rewrite length_le8 in Hx. exact Hx.
Qed.

(* long_alias: its 301 bytes and the 3 slack bytes after them, [0x743f8, 0x74528) *)
Lemma ml_la_ok : mlocal (lo_rng A_LONG_ALIAS (LONG_ALIAS_SIZE + 3)) la_ok.
Proof.
  intros m m' C (la & sl & H1 & H2 & L). exists la, sl. split; [|split; [|exact L]].
  - apply (ml_use _ _ _ m m' (ml_rw_cells _ _) C); [|exact H1].
    intros x Hx. cbn [cells_size csize] in Hx. unfold lo_rng, LONG_ALIAS_SIZE in *. lia.
  - apply (ml_use _ _ _ m m' (ml_bytes_at _ _) C); [|exact H2].
    intros x Hx. rewrite L in Hx. change (Z.of_nat 3) with 3 in Hx. unfold lo_rng, LONG_ALIAS_SIZE in *. lia.
Qed.

(* g_names: 64 slots of 8 bytes *)
Lemma ml_gnames_at : mlocal (lo_rng A_G_NAMES G_NAMES_SIZE) gnames_at.
Proof.
  intros m m' C H k Hk. destruct (H k Hk) as (rest & Hb & L). exists rest. split; [|exact L].
  apply (ml_use _ _ _ m m' (ml_bytes_at _ _) C); [|exact Hb].
  intros x Hx. rewrite L in Hx. change (Z.of_nat 8) with 8 in Hx. unfold lo_rng, G_NAMES_SIZE in *. lia.
Qed.

(* the six strings odd[] points at (.rodata): "", enp131s0.33, eth0, wlan0, veth-box, gone0 *)
Definition lo_odd_str (x : Z) : Prop :=
  lo_rng 0x10368 1 x \/ lo_rng 0x1039c 12 x \/ lo_rng 0x1056a 5 x \/ lo_rng 0x103bc 6 x \/
  lo_rng 0x10598 9 x \/ lo_rng 0x102a2 6 x.

Lemma lo_odd_str_nth : forall i x, (i < 6)%nat ->
  lo_rng (nth i odd_ptrs 0) (Z.of_nat (length (nth i odd_strs [])) + 1) x -> lo_odd_str x.
Proof.
  intros i x Hi Hx. unfold lo_odd_str.
  destruct i as [|[|[|[|[|[|i]]]]]].
  - left. exact Hx.
  - right; left. exact Hx.
  - right; right; left. exact Hx.
  - do 3 right; left. exact Hx.
  - do 4 right; left. exact Hx.
  - do 5 right. exact Hx.
  - lia.
Qed.

(* the odd table (.data.rel.ro, 6 pointers) and its strings *)
Definition lo_odd_reg (x : Z) : Prop := lo_rng A_ODD 48 x \/ lo_odd_str x.

Lemma ml_odd_at : mlocal lo_odd_reg odd_at.
Proof.
  intros m m' C H i Hi. destruct (H i Hi) as [Hu Hc]. split.
  - apply (ml_use _ _ _ m m' (ml_u64_at _ _) C); [|exact Hu].
    intros x Hx. left. unfold lo_rng in *. lia.
  - apply (ml_use _ _ _ m m' (ml_cstr_at _ _) C); [|exact Hc].
    intros x Hx. right. exact (lo_odd_str_nth i x Hi Hx).
Qed.

(* the texts table (.data.rel.ro, 11 pointers; texts_at reads the table only) *)
Lemma ml_texts_at : mlocal (lo_rng A_TEXTS 88) texts_at.
Proof.
  intros m m' C H i Hi. apply (ml_use _ _ _ m m' (ml_u64_at _ _) C); [|exact (H i Hi)].
  intros x Hx. unfold lo_rng in *. lia.
Qed.

(* g_nl.if_name[0..63] *)
Lemma ml_ifptrs_at : mlocal (lo_rng (A_G_NL + NK_IF_NAME) 512) ifptrs_at.
Proof.
  intros m m' C H i Hi. apply (ml_use _ _ _ m m' (ml_u64_at _ _) C); [|exact (H i Hi)].
  intros x Hx. unfold lo_rng in *. lia.
Qed.

(* the four policy strings (.rodata) *)
Definition lo_pol_reg (x : Z) : Prop :=
  lo_rng A_PREFIX 9 x \/ lo_rng A_SERVED 15 x \/ lo_rng A_VLAN 5 x \/ lo_rng A_EMPTY 1 x.

Lemma ml_policy_ro : mlocal lo_pol_reg policy_ro.
Proof.
  intros m m' C (P1 & P2 & P3 & P4). split; [|split; [|split]].
  - apply (ml_use _ _ _ m m' (ml_cstr_at _ _) C); [|exact P1]. intros x Hx. left. exact Hx.
  - apply (ml_use _ _ _ m m' (ml_cstr_at _ _) C); [|exact P2]. intros x Hx. right; left. exact Hx.
  - apply (ml_use _ _ _ m m' (ml_cstr_at _ _) C); [|exact P3]. intros x Hx. right; right; left. exact Hx.
  - apply (ml_use _ _ _ m m' (ml_cstr_at _ _) C); [|exact P4]. intros x Hx. right; right; right. exact Hx.
Qed.

(* ---- iftab_at with ifptrs_at: g_nl.if_name[i] holds link_ptrs[i], which points into g_names or at one
   of the odd strings; so the names iftab_at reads lie there ---- *)

Definition lo_in_b (lo n p k : Z) : bool := (lo <=? p) && (p + k <=? lo + n).

Lemma lo_in_b_ok : forall lo n p k, lo_in_b lo n p k = true -> forall x, lo_rng p k x -> lo_rng lo n x.
Proof.
  intros lo n p k H x Hx. unfold lo_in_b in H. apply andb_true_iff in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. unfold lo_rng in *. lia.
Qed.

Definition lo_name_b (p k : Z) : bool :=
  lo_in_b A_G_NAMES G_NAMES_SIZE p k || lo_in_b 0x10368 1 p k || lo_in_b 0x1039c 12 p k ||
  lo_in_b 0x1056a 5 p k || lo_in_b 0x103bc 6 p k || lo_in_b 0x10598 9 p k || lo_in_b 0x102a2 6 p k.

Lemma lo_name_b_ok : forall p k, lo_name_b p k = true ->
  forall x, lo_rng p k x -> lo_rng A_G_NAMES G_NAMES_SIZE x \/ lo_odd_str x.
Proof.
  intros p k H x Hx. unfold lo_name_b in H.
  repeat match goal with Hh : (_ || _)%bool = true |- _ => apply orb_prop in Hh; destruct Hh as [Hh|Hh] end;
    pose proof (lo_in_b_ok _ _ _ _ H x Hx) as R; unfold lo_odd_str, lo_rng in *; lia.
Qed.

Fixpoint lo_tab_ok (tab : list (list byte * Z)) (ps : list Z) : bool :=
  match tab, ps with
  | [], _ => true
  | (nm, _) :: tab', p :: ps' => lo_name_b p (Z.of_nat (length nm) + 1) && lo_tab_ok tab' ps'
  | _ :: _, [] => false
  end.

Lemma lo_tab_ok_nth : forall tab ps i nm ix, lo_tab_ok tab ps = true -> nth_error tab i = Some (nm, ix) ->
  lo_name_b (nth i ps 0) (Z.of_nat (length nm) + 1) = true.
Proof.
  induction tab as [|[nm0 ix0] tab IH]; intros ps i nm ix H E.
  - destruct i; cbn in E; discriminate.
  - destruct ps as [|p ps]; [cbn in H; discriminate|].
    cbn [lo_tab_ok] in H. apply andb_true_iff in H as [H1 H2].
    destruct i as [|i].
    + cbn in E. injection E as E1 E2. subst. exact H1.
    + cbn in E. exact (IH ps i nm ix H2 E).
Qed.

Lemma lo_link_tab_ok : lo_tab_ok link_tab link_ptrs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma lo_link_len : length link_tab = 64%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma lo_list_ext : forall (l l' : list byte), length l = length l' ->
  (forall i, (i < length l)%nat -> nth_error l i = nth_error l' i) -> l = l'.
Proof.
  induction l as [|b l IH]; intros [|b' l'] HL H.
  - reflexivity.
  - cbn in HL. discriminate.
  - cbn in HL. discriminate.
  - cbn in HL. f_equal.
    + specialize (H 0%nat ltac:(cbn; lia)). cbn in H. injection H as Hb. exact Hb.
    + apply IH; [lia|]. intros i Hi. exact (H (S i) ltac:(cbn; lia)).
Qed.

(* the 8 bytes at a fix a value below 2^64 *)
Lemma lo_u64_inj : forall m a p q, u64_at m a p -> u64_at m a q -> 0 <= p < 2 ^ 64 -> 0 <= q < 2 ^ 64 -> p = q.
Proof.
  intros m a p q (_ & _ & Hp) (_ & _ & Hq) Rp Rq.
  assert (E : le8 (wz p) = le8 (wz q)).
  { apply lo_list_ext; [rewrite !length_le8; reflexivity|].
    intros i Hi. rewrite <- (Hp i Hi). apply Hq. rewrite length_le8. rewrite length_le8 in Hi. exact Hi. }
  assert (W : wz p = wz q).
  { pose proof (f_equal le_bytes_to_word E) as E2. rewrite !le_bytes_to_word_le8 in E2. exact E2. }
  pose proof (f_equal bv_unsigned W) as W2. unfold wz in W2.
  rewrite (MState.unsigned_lit p Rp), (MState.unsigned_lit q Rq) in W2. exact W2.
Qed.

(* g_nl.if_name[], g_nl.if_index[0..63], g_names, the odd strings *)
Definition lo_iftab_reg (x : Z) : Prop :=
  lo_rng (A_G_NL + NK_IF_NAME) 512 x \/ lo_rng (A_G_NL + NK_IF_INDEX) 256 x \/
  lo_rng A_G_NAMES G_NAMES_SIZE x \/ lo_odd_str x.

Lemma ml_iftab : forall kbs, mlocal lo_iftab_reg (fun m => iftab_at m kbs link_tab /\ ifptrs_at m).
Proof.
  intros kbs m m' C [(Hn & Hl & H) Hp].
  assert (Hp' : ifptrs_at m').
  { apply (ml_use _ _ _ m m' ml_ifptrs_at C); [|exact Hp]. intros x Hx. left. exact Hx. }
  split; [|exact Hp']. split; [exact Hn|]. split; [exact Hl|].
  intros i nm ix E. destruct (H i nm ix E) as (Hix & p & Hu & Hp0 & Hc & Hidx). split; [exact Hix|].
  assert (Hi : (i < 64)%nat).
  { rewrite <- lo_link_len. apply nth_error_Some. rewrite E. discriminate. }
  pose proof (lo_tab_ok_nth _ _ _ _ _ lo_link_tab_ok E) as Hb.
  pose proof (eq_refl : 2 ^ 64 = 18446744073709551616) as P64.
  assert (Eq : p = nth i link_ptrs 0).
  { apply (lo_u64_inj m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i)); [exact Hu | exact (Hp i Hi) | |].
    - destruct Hc as [(H0 & H1 & _) _]. rewrite length_app in H1. cbn [length] in H1. lia.
    - assert (Hq : lo_rng (nth i link_ptrs 0) (Z.of_nat (length nm) + 1) (nth i link_ptrs 0))
        by (unfold lo_rng; lia).
      destruct (lo_name_b_ok _ _ Hb _ Hq) as [R|R];
        cbv [lo_odd_str lo_rng A_G_NAMES G_NAMES_SIZE] in R; lia. }
  subst p. exists (nth i link_ptrs 0). split; [|split; [exact Hp0|split]].
  - apply (ml_use _ _ _ m m' (ml_u64_at _ _) C); [|exact Hu].
    intros x Hx. left. unfold lo_rng in *. lia.
  - apply (ml_use _ _ _ m m' (ml_cstr_at _ _) C); [|exact Hc]. intros x Hx.
    destruct (lo_name_b_ok _ _ Hb x Hx) as [R|R]; [right; right; left; exact R | right; right; right; exact R].
  - apply (ml_use _ _ _ m m' (ml_u32_at _ _) C); [|exact Hidx].
    intros x Hx. right; left. unfold lo_rng in *. lia.
Qed.

(* ==========================================================================
   3. The loop-head memory lh_mem, and what an allocator step needs
   ========================================================================== *)

(* lh_mem's region minus errno and the guard words: the frame [S - 480, S) (and the saved bytes as lh_mem
   reads them), g_nl, g_names, long_alias with its 3 slack bytes, the odd and texts tables, the odd and
   policy strings, the md block, the mk block, the payload *)
Definition lh_reg (E : lenv) (x : Z) : Prop :=
  lo_rng (e_S E - SLOT_FRAME) SLOT_FRAME x \/
  lo_rng (e_S E - 104) (Z.of_nat (length (e_saved E))) x \/
  lo_rng A_G_NL NK_SIZE x \/
  lo_rng A_G_NAMES G_NAMES_SIZE x \/
  lo_rng A_LONG_ALIAS (LONG_ALIAS_SIZE + 3) x \/
  lo_rng A_ODD 48 x \/
  lo_rng A_TEXTS 88 x \/
  lo_odd_str x \/
  lo_pol_reg x \/
  lo_rng (e_md E) MD_SIZE x \/
  lo_rng (e_mk E) MK_SIZE x \/
  lo_rng (e_p0 E) (Z.of_nat (length (e_pl E))) x.

(* the whole region lh_mem reads *)
Definition lh_mem_reg (E : lenv) (x : Z) : Prop := lh_reg E x \/ lo_rng A_ERRNO 4 x \/ lo_guard_reg x.

Lemma lh_reg_frame : forall E x, lo_rng (e_S E - SLOT_FRAME) SLOT_FRAME x -> lh_reg E x.
Proof. intros E x H. left. exact H. Qed.
Lemma lh_reg_saved : forall E x, lo_rng (e_S E - 104) (Z.of_nat (length (e_saved E))) x -> lh_reg E x.
Proof. intros E x H. right; left. exact H. Qed.
Lemma lh_reg_gnl : forall E x, lo_rng A_G_NL NK_SIZE x -> lh_reg E x.
Proof. intros E x H. do 2 right; left. exact H. Qed.
Lemma lh_reg_gnames : forall E x, lo_rng A_G_NAMES G_NAMES_SIZE x -> lh_reg E x.
Proof. intros E x H. do 3 right; left. exact H. Qed.
Lemma lh_reg_la : forall E x, lo_rng A_LONG_ALIAS (LONG_ALIAS_SIZE + 3) x -> lh_reg E x.
Proof. intros E x H. do 4 right; left. exact H. Qed.
Lemma lh_reg_oddtab : forall E x, lo_rng A_ODD 48 x -> lh_reg E x.
Proof. intros E x H. do 5 right; left. exact H. Qed.
Lemma lh_reg_texts : forall E x, lo_rng A_TEXTS 88 x -> lh_reg E x.
Proof. intros E x H. do 6 right; left. exact H. Qed.
Lemma lh_reg_oddstr : forall E x, lo_odd_str x -> lh_reg E x.
Proof. intros E x H. do 7 right; left. exact H. Qed.
Lemma lh_reg_pol : forall E x, lo_pol_reg x -> lh_reg E x.
Proof. intros E x H. do 8 right; left. exact H. Qed.
Lemma lh_reg_md : forall E x, lo_rng (e_md E) MD_SIZE x -> lh_reg E x.
Proof. intros E x H. do 9 right; left. exact H. Qed.
Lemma lh_reg_mk : forall E x, lo_rng (e_mk E) MK_SIZE x -> lh_reg E x.
Proof. intros E x H. do 10 right; left. exact H. Qed.
Lemma lh_reg_pl : forall E x, lo_rng (e_p0 E) (Z.of_nat (length (e_pl E))) x -> lh_reg E x.
Proof. intros E x H. do 11 right. exact H. Qed.

Lemma lo_iftab_lh : forall E x, lo_iftab_reg x -> lh_reg E x.
Proof.
  intros E x [H|[H|[H|H]]].
  - apply lh_reg_gnl. unfold lo_rng, NK_IF_NAME, NK_SIZE in *. lia.
  - apply lh_reg_gnl. unfold lo_rng, NK_IF_INDEX, NK_SIZE in *. lia.
  - apply lh_reg_gnames. exact H.
  - apply lh_reg_oddstr. exact H.
Qed.

Lemma lo_lh_cells_size : forall md mk P N j0 j1 j2, Z.of_nat (cells_size (lh_cells md mk P N j0 j1 j2)) = 376.
Proof. reflexivity. Qed.

Lemma lh_mem_carry : forall E i P N kbs mbs gbs m m',
  lh_mem E i P N kbs mbs gbs m -> lcarry (lh_reg E) m m' -> wr_at rsegs m' A_ERRNO 4 -> guard_m m' ->
  lh_mem E i P N kbs mbs gbs m'.
Proof.
  intros E i P N kbs mbs gbs m m' H C Hw Hg.
  destruct H as ((j0 & j1 & j2 & nc & Fr) & Sv & Nk & Nw & It & No & Nm & Noc & Nop & Gn & Od & Po & La & Tx & Ip
    & Md & Mw & Mk & Kw & Ma & Cu & _ & _).
  assert (Fr' : exists j0 j1 j2 nc, rw_cells rsegs m' (e_S E - SLOT_FRAME) (lh_cells (e_md E) (e_mk E) P nc j0 j1 j2)).
  { exists j0, j1, j2, nc. apply (ml_use _ _ _ m m' (ml_rw_cells _ _) C); [|exact Fr].
    intros x Hx. apply lh_reg_frame. rewrite lo_lh_cells_size in Hx. unfold lo_rng, SLOT_FRAME in *. lia. }
  assert (Sv' : bytes_at rsegs m' (e_S E - 104) (e_saved E)).
  { apply (ml_use _ _ _ m m' (ml_bytes_at _ _) C); [|exact Sv]. intros x Hx. apply lh_reg_saved. exact Hx. }
  assert (Nk' : nlk_at m' kbs).
  { apply (ml_use _ _ _ m m' (ml_nlk_at kbs) C); [|exact Nk]. intros x Hx. apply lh_reg_gnl. exact Hx. }
  assert (ItIp : iftab_at m' kbs link_tab /\ ifptrs_at m').
  { apply (ml_use _ _ _ m m' (ml_iftab kbs) C); [|exact (conj It Ip)]. exact (lo_iftab_lh E). }
  destruct ItIp as [It' Ip'].
  assert (Gn' : gnames_at m').
  { apply (ml_use _ _ _ m m' ml_gnames_at C); [|exact Gn]. intros x Hx. apply lh_reg_gnames. exact Hx. }
  assert (Od' : odd_at m').
  { apply (ml_use _ _ _ m m' ml_odd_at C); [|exact Od].
    intros x [Hx|Hx]; [apply lh_reg_oddtab | apply lh_reg_oddstr]; exact Hx. }
  assert (Po' : policy_ro m').
  { apply (ml_use _ _ _ m m' ml_policy_ro C); [|exact Po]. intros x Hx. apply lh_reg_pol. exact Hx. }
  assert (La' : la_ok m').
  { apply (ml_use _ _ _ m m' ml_la_ok C); [|exact La]. intros x Hx. apply lh_reg_la. exact Hx. }
  assert (Tx' : texts_at m').
  { apply (ml_use _ _ _ m m' ml_texts_at C); [|exact Tx]. intros x Hx. apply lh_reg_texts. exact Hx. }
  assert (Md' : model_at m' (e_md E) mbs).
  { apply (ml_use _ _ _ m m' (ml_model_at _ _) C); [|exact Md]. intros x Hx. apply lh_reg_md. exact Hx. }
  assert (Mk' : marks_at m' (e_mk E) gbs).
  { apply (ml_use _ _ _ m m' (ml_marks_at _ _) C); [|exact Mk]. intros x Hx. apply lh_reg_mk. exact Hx. }
  assert (Cu' : cursor_ok m' (e_p0 E) (e_pl E) P N).
  { apply (ml_use _ _ _ m m' (ml_cursor_ok _ _ _ _) C); [|exact Cu]. intros x Hx. apply lh_reg_pl. exact Hx. }
  exact (conj Fr' (conj Sv' (conj Nk' (conj Nw (conj It' (conj No (conj Nm (conj Noc (conj Nop (conj Gn'
    (conj Od' (conj Po' (conj La' (conj Tx' (conj Ip' (conj Md' (conj Mw (conj Mk' (conj Kw (conj Ma
    (conj Cu' (conj Hw Hg)))))))))))))))))))))).
Qed.

Lemma ml_lh_mem : forall E i P N kbs mbs gbs, mlocal (lh_mem_reg E) (lh_mem E i P N kbs mbs gbs).
Proof.
  intros E i P N kbs mbs gbs m m' C H.
  pose proof H as H0.
  destruct H0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Er & Gu).
  apply (lh_mem_carry E i P N kbs mbs gbs m m' H).
  - apply (lcarry_mono (lh_reg E) (lh_mem_reg E) m m'); [|exact C]. intros x Hx. left. exact Hx.
  - apply (ml_use _ _ _ m m' (ml_wr_at _ _) C); [|exact Er]. intros x Hx. right; left. exact Hx.
  - apply (ml_use _ _ _ m m' ml_guard_m C); [|exact Gu]. intros x Hx. right; right. exact Hx.
Qed.

(* ---- the exit memory (ex_ms at L_EXIT): the frame cells, the saved bytes, errno, the guard words ---- *)

Definition ex_mem (E : lenv) (m : word -> option byte) : Prop :=
  (exists j, rw_cells rsegs m (e_S E - SLOT_FRAME) [CB 376 j]) /\
  bytes_at rsegs m (e_S E - 104) (e_saved E) /\
  wr_at rsegs m A_ERRNO 4 /\ guard_m m.

Definition ex_reg (E : lenv) (x : Z) : Prop :=
  lo_rng (e_S E - SLOT_FRAME) SLOT_FRAME x \/ lo_rng (e_S E - 104) (Z.of_nat (length (e_saved E))) x.

Lemma ex_ms_mem : forall E gp ms, ex_ms E gp ms -> ex_mem E (ms_mem ms).
Proof.
  intros E gp ms (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s1 & s2 & s3 & s4 & s5 & s6 & s8 & s9
    & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & m & j & -> & _ & Hc & Hs & Hw & Hg & _).
  exact (conj (ex_intro _ j Hc) (conj Hs (conj Hw Hg))).
Qed.

Lemma lo_cb376 : forall j, Z.of_nat (cells_size [CB 376 j]) = 376.
Proof. reflexivity. Qed.

Lemma ex_mem_carry : forall E m m',
  ex_mem E m -> lcarry (ex_reg E) m m' -> wr_at rsegs m' A_ERRNO 4 -> guard_m m' -> ex_mem E m'.
Proof.
  intros E m m' ((j & Fr) & Sv & _ & _) C Hw Hg. split; [|split; [|split; [exact Hw | exact Hg]]].
  - exists j. apply (ml_use _ _ _ m m' (ml_rw_cells _ _) C); [|exact Fr].
    intros x Hx. left. rewrite lo_cb376 in Hx. unfold lo_rng, SLOT_FRAME in *. lia.
  - apply (ml_use _ _ _ m m' (ml_bytes_at _ _) C); [|exact Sv]. intros x Hx. right. exact Hx.
Qed.

Lemma ml_ex_mem : forall E, mlocal (fun x => ex_reg E x \/ lo_rng A_ERRNO 4 x \/ lo_guard_reg x) (ex_mem E).
Proof.
  intros E m m' C H. pose proof H as (_ & _ & Er & Gu).
  apply (ex_mem_carry E m m' H).
  - apply (lcarry_mono (ex_reg E) (fun x => ex_reg E x \/ lo_rng A_ERRNO 4 x \/ lo_guard_reg x) m m');
      [|exact C].
    intros x Hx. left. exact Hx.
  - apply (ml_use _ _ _ m m' (ml_wr_at _ _) C); [|exact Er]. intros x Hx. right; left. exact Hx.
  - apply (ml_use _ _ _ m m' ml_guard_m C); [|exact Gu]. intros x Hx. right; right. exact Hx.
Qed.

(* ---- the regions lie in what an allocator call keeps (LFr lkeep) ---- *)

(* one reservation of the image covers [lo, hi) (a closed check per range) *)
Definition lo_res_chk (lo hi : Z) : bool :=
  existsb (fun r => (bv_unsigned (fst r) <=? lo) && (hi <=? bv_unsigned (fst r) + bv_unsigned (snd r)))
    (segments_reserved rsegs).

Lemma lo_res_img : forall B lo hi x, ms_segs B = rsegs -> lo_res_chk lo hi = true -> lo <= x < hi -> in_img B x.
Proof.
  intros B lo hi x HS Hc Hx. unfold lo_res_chk in Hc. apply existsb_exists in Hc as (r & Hr & Hb).
  cbv beta in Hb. apply andb_true_iff in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  split; [rewrite HS; exact lfr_rsegs_nonnil|].
  exists r. split; [rewrite HS; exact Hr | lia].
Qed.

(* the strings (.rodata), the two pointer tables (.data.rel.ro), g_nl .. long_alias + 3 (.bss) *)
Lemma lo_chk_ro : lo_res_chk 0x102a2 0x105a1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma lo_chk_relro : lo_res_chk 0x207c0 0x20848 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma lo_chk_bss : lo_res_chk 0x31b80 0x74528 = true.
Proof. vm_compute. reflexivity. Qed.

Section Keep.
Context {rc : YM05.RunCeil}.

(* at LFF's values none of these bytes is static_owned (lock 0x95908, libc 0x95898, guard 0x95878, GOT
   guard 0x208d8, debruijn 0x10778 from -108, size classes 0x10798, counts 0x107f8 / 0x10813), the ctx
   (0x95910, 928 bytes) or errno (0x75564) *)
Lemma lo_img_keep : forall (B : malloc_syms) (API : AllocAPI B) SH SK x, @LFF rc B API SH SK ->
  (0x102a2 <= x < 0x105a1 \/ 0x207c0 <= x < 0x20848 \/ 0x31b80 <= x < 0x74528) -> lf_img B x.
Proof.
  intros B API SH SK x FF Hx.
  destruct FF as (SEG & _ & _ & _ & _ & _ & GUA & GOT & CTX & LCK & LIBC & SCL & SMC & MDC & DBR & TP & EOFF & _
    & VML & DBL & _).
  assert (VL1 : vml_lo B = 0) by (unfold vml_lo; rewrite VML; reflexivity).
  assert (VL2 : vml_len B = 0) by (unfold vml_len; rewrite VML; reflexivity).
  unfold lf_img, static_owned, errno_addr.
  rewrite GUA, GOT, CTX, LCK, LIBC, SCL, SMC, MDC, DBR, TP, EOFF, VL1, VL2, DBL. unfold CTX_SIZE.
  split.
  - destruct Hx as [Hx|[Hx|Hx]].
    + exact (lo_res_img B _ _ x SEG lo_chk_ro Hx).
    + exact (lo_res_img B _ _ x SEG lo_chk_relro Hx).
    + exact (lo_res_img B _ _ x SEG lo_chk_bss Hx).
  - split; [|split]; intros HH; lia.
Qed.

Lemma lh_reg_keep : forall (B : malloc_syms) (API : AllocAPI B) SH SK g hb E x,
  @LFF rc B API SH SK -> e_S E = lg_S g -> In (e_md E, MD_SIZE) hb -> In (e_mk E, MK_SIZE) hb ->
  (forall y, e_p0 E <= y < e_p0 E + Z.of_nat (length (e_pl E)) -> in_blk0 g y) ->
  length (e_saved E) = 104%nat ->
  lh_reg E x -> lkeep B g hb x.
Proof.
  intros B API SH SK g hb E x FF HS Hmd Hmk Hpl Hsv Hx.
  assert (IMG : forall y, (0x102a2 <= y < 0x105a1 \/ 0x207c0 <= y < 0x20848 \/ 0x31b80 <= y < 0x74528) ->
    lkeep B g hb y).
  { intros y Hy. right; left. exact (lo_img_keep B API SH SK y FF Hy). }
  destruct Hx as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]].
  - left. rewrite <- HS. unfold lo_rng, SLOT_FRAME in *. lia.
  - left. rewrite <- HS. rewrite Hsv in H. change (Z.of_nat 104) with 104 in H. unfold lo_rng, SLOT_FRAME in *. lia.
  - apply IMG. unfold lo_rng, A_G_NL, NK_SIZE in H. lia.
  - apply IMG. unfold lo_rng, A_G_NAMES, G_NAMES_SIZE in H. lia.
  - apply IMG. unfold lo_rng, A_LONG_ALIAS, LONG_ALIAS_SIZE in H. lia.
  - apply IMG. unfold lo_rng, A_ODD in H. lia.
  - apply IMG. unfold lo_rng, A_TEXTS in H. lia.
  - apply IMG. unfold lo_odd_str, lo_rng in H. lia.
  - apply IMG. unfold lo_pol_reg, lo_rng, A_PREFIX, A_SERVED, A_VLAN, A_EMPTY in H. lia.
  - right; right; left. exists (e_md E), MD_SIZE. split; [exact Hmd | exact H].
  - right; right; left. exists (e_mk E), MK_SIZE. split; [exact Hmk | exact H].
  - right; right; right. apply Hpl. exact H.
Qed.

(* the same with the placement facts lenv_ok gives *)
Lemma lh_reg_keep_ok : forall (B : malloc_syms) (API : AllocAPI B) SH SK g hb E x,
  @LFF rc B API SH SK -> lenv_ok E -> e_S E = lg_S g -> In (e_md E, MD_SIZE) hb -> In (e_mk E, MK_SIZE) hb ->
  (forall y, e_p0 E <= y < e_p0 E + Z.of_nat (length (e_pl E)) -> in_blk0 g y) ->
  lh_reg E x -> lkeep B g hb x.
Proof.
  intros B API SH SK g hb E x FF HE HS Hmd Hmk Hpl Hx.
  destruct HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsv).
  exact (lh_reg_keep B API SH SK g hb E x FF HS Hmd Hmk Hpl Hsv Hx).
Qed.

End Keep.

Lemma ex_reg_keep : forall (B : malloc_syms) g hb E x,
  e_S E = lg_S g -> length (e_saved E) = 104%nat -> ex_reg E x -> lkeep B g hb x.
Proof.
  intros B g hb E x HS Hsv [H|H]; left; rewrite <- HS.
  - unfold lo_rng, SLOT_FRAME in *. lia.
  - rewrite Hsv in H. change (Z.of_nat 104) with 104 in H. unfold lo_rng, SLOT_FRAME in *. lia.
Qed.
