(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics Fs State Monad Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import
  W64 W64Proofs Val IMap Mem Instr State Step Plan Notation ValProofs StepSoundBase StepSound PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib Defs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import MemProofs StepSoundMem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import Nodes CertSound OblsLib Ops SysSpec CtrSys StdioWrite DrvShape DrvRoot.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP StepB StepS PlanS FXN CertS OL Ops CtrS SW DrvShape DrvRoot.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module DrvLib.

Definition LE8 (z : Z) : list byte := Z_to_le_bytes 8 z.
Definition cstr (s : list byte) : list byte := s ++ [Z_to_bv 8 0].

Record drun := DRun {
  r_heap : opcomp;
  r_ext : int -> opcomp;
  r_a0 : list byte;
  r_p1 : list byte;
  r_file : list byte;
  r_fs : Fs;
  r_RS : Z;
  r_RSr : 0 <= r_RS /\ r_RS + 65536 <= two64;
  r_MP : Model -> Prop;
  r_PB : (int -> list byte) -> Prop;
  r_MP_fs : forall m, r_MP m -> m_fs m = r_fs;
  r_MP_fds : forall fds m, r_MP m -> r_MP (with_fds fds m);
  r_MPA : mp_stable r_MP;
  r_heap_fds : forall args m model fds, oc_holds r_heap args m model -> oc_holds r_heap args m (with_fds fds model);
  r_heap_fp_stage : forall args a, r_RS <= a < r_RS + 65536 -> ~ Exists (fun iv => fst iv <= a < snd iv) (oc_fp r_heap args);
  r_ext_fds : forall id args m model fds, oc_holds (r_ext id) args m model -> oc_holds (r_ext id) args m (with_fds fds model);
  r_ext_fp_stage : forall id args a, r_RS <= a < r_RS + 65536 -> ~ Exists (fun iv => fst iv <= a < snd iv) (oc_fp (r_ext id) args);
  r_PB_a0 : forall b, r_PB b -> b 1%uint63 = cstr r_a0 /\ b 9%uint63 = LE8 (Z.of_nat (length r_a0) + 1);
  r_PB_p1 : forall b, r_PB b -> b 3%uint63 = cstr r_p1 /\ b 10%uint63 = LE8 (Z.of_nat (length r_p1) + 1);
  r_a0_len : Z.of_nat (length r_a0) <= 131071;
  r_p1_len : Z.of_nat (length r_p1) <= 131071;
  r_p1_nz : ~ In (Z_to_bv 8 0) r_p1;

  r_tm : tab_model r_heap (FD3 r_p1 r_file) (RSTAGE r_file r_RS r_RSr) FD3DIR FDINIT r_ext;
  r_tm_fds : forall mo fds, op_minv (CtrSys.OPS r_heap r_ext r_p1 r_file r_RS r_RSr r_tm) mo ->
                            op_minv (CtrSys.OPS r_heap r_ext r_p1 r_file r_RS r_RSr r_tm) (with_fds fds mo);
  r_tm_cov1 : forall id args a, op_cov1 (CtrSys.OPS r_heap r_ext r_p1 r_file r_RS r_RSr r_tm) id args a -> id = 1%uint63

}.

Definition file_pb (R : drun) : Prop :=
  forall b, r_PB R b -> b 4%uint63 = r_file R /\ b 11%uint63 = LE8 (fsize (r_file R)) /\ b 5%uint63 = payload (r_file R)
              /\ b 14%uint63 = LE8 (6 + cfg_len (r_file R)) /\ b 13%uint63 = LE8 (Z.max 0 (fsize (r_file R) - 6 - cfg_len (r_file R))).

Definition OPS (R : drun) : optable := CtrSys.OPS (r_heap R) (r_ext R) (r_p1 R) (r_file R) (r_RS R) (r_RSr R) (r_tm R).
Definition DR (R : drun) (s : shp) : TSet := D (r_fs R) (r_a0 R) (r_p1 R) s.

Section Run.
Variable segs : list Segment.
Variable R : drun.
Let MP := r_MP R.
Let PB := r_PB R.

Definition NODE (T : sstate) (K : TSet) : Prop :=
  forall E ms m, PB (eb E) -> MP m -> st_ok segs (OPS R) E T ms m -> realizes segs (mkCfg ms m) K.

Definition ENODE (T : sstate) (K : TSet) : Prop :=
  forall E ms m, PB (eb E) -> MP m -> st_ok segs (OPS R) E T ms m -> ecall_at segs (s_pc T) -> realizes segs (mkCfg ms m) K.

Lemma node_teq : forall T K K', NODE T K' -> t_eq K' K -> NODE T K.
Proof. intros T K K' HN Heq E ms m HPB HMP HS. apply (rz_conseq segs _ K' K (HN E ms m HPB HMP HS) Heq). Qed.

Lemma enode_teq : forall T K K', ENODE T K' -> t_eq K' K -> ENODE T K.
Proof. intros T K K' HN Heq E ms m HPB HMP HS Hat. apply (rz_conseq segs _ K' K (HN E ms m HPB HMP HS Hat) Heq). Qed.

Lemma node_eqv : forall T a b, shp_eqv a b = true -> NODE T (DR R a) -> NODE T (DR R b).
Proof. intros T a b Hab HN. apply (node_teq T _ _ HN). apply shp_eqv_sound. exact Hab. Qed.

Lemma node_facts : forall T K K', NODE T K' ->
  (forall E, PB (eb E) -> ev E 0%uint63 = Z_to_bv 64 0 -> facts_hold E (s_facts T) -> t_eq K' K) -> NODE T K.
Proof.
  intros T K K' HN HF E ms m HPB HMP HS.
  apply (rz_conseq segs _ K' K (HN E ms m HPB HMP HS)).
  apply (HF E HPB (so_zero _ _ _ _ _ _ HS) (so_facts _ _ _ _ _ _ HS)).
Qed.

Lemma Forall_imap_of : forall A (P : int * A -> Prop) (l : list (int * A)) k v,
  Forall P l -> IMap.find k (imap_of l) = Some v -> P (k, v).
Proof. intros A P l k v HF Hf. apply imap_of_find_in in Hf. exact (proj1 (Forall_forall _ _) HF _ Hf). Qed.

Theorem node_cert : forall (C : ctx) (p : plan) (T : sstate) (obls : list obligation) (K : TSet)
                           (cutl : list (int * template)) (ecl : list (int * sstate)),
  ctx_wfb C = true -> itab_ok segs (c_itab C) -> contracts_ok segs (OPS R) C MP PB ->
  check segs C p T = Some obls -> obls_hold PB obls -> c_mroot C = VL wzero ->
  c_cuts C = imap_of cutl -> Forall (fun kv => NODE (t_st (snd kv)) K) cutl ->
  c_ecalls C = imap_of ecl -> Forall (fun kv => ENODE (snd kv) K) ecl ->
  NODE T K.
Proof.
  intros C p T obls K cutl ecl HWF HIT HCO HCHK HOB HM Hc HNc He HNe E ms m HPB HMP HS.
  eapply (check_sound segs (OPS R) C MP PB p T obls HWF HIT HCO (r_MPA R) HCHK HOB); [rewrite HM; reflexivity | exact HS | exact HPB | exact HMP |].
  split.
  - intros tid T' Hf E' ms' m' Heb HMP' HS' _. rewrite Hc in Hf.
    exact (Forall_imap_of _ _ cutl tid T' HNc Hf E' ms' m' ltac:(rewrite Heb; exact HPB) HMP' HS').
  - intros eid T' Hf E' ms' m' Heb HMP' HS' Hat. rewrite He in Hf.
    exact (Forall_imap_of _ _ ecl eid T' HNe Hf E' ms' m' ltac:(rewrite Heb; exact HPB) HMP' HS' Hat).
Qed.

Theorem node_loop : forall (C : ctx) (p : plan) (obls : list obligation) (h : int) (HEAD : template) (K : TSet)
                           (cutl : list (int * template)) (ecl : list (int * sstate)),
  ctx_wfb C = true -> itab_ok segs (c_itab C) -> contracts_ok segs (OPS R) C MP PB ->
  IMap.find h (c_cuts C) = Some HEAD -> c_mroot C = t_measure HEAD ->
  check segs C p (t_st HEAD) = Some obls -> obls_hold PB obls ->
  vars_below (s_next (t_st HEAD)) (t_measure HEAD) = true -> uses_plain_cut p h = false ->
  c_cuts C = imap_of cutl -> Forall (fun kv => PrimInt63.eqb (fst kv) h = true \/ NODE (t_st (snd kv)) K) cutl ->
  c_ecalls C = imap_of ecl -> Forall (fun kv => ENODE (snd kv) K) ecl ->
  NODE (t_st HEAD) K.
Proof.
  intros C p obls h HEAD K cutl ecl HWF HIT HCO Hh HM HCHK HOB HMV Hplain Hc HNc He HNe E ms m HPB HMP HS.
  refine (loop_sound segs (OPS R) C p obls h HEAD MP PB K E (r_MPA R) HWF HIT HCO Hh HM HCHK HOB HMV Hplain HPB _ _ E ms m eq_refl HMP HS).
  - intros tid T' Hf Hne E' ms' m' Heb HMP' HS'. rewrite Hc in Hf.
    destruct (Forall_imap_of _ _ cutl tid T' HNc Hf) as [Hx | HN]; [cbn [fst] in Hx; rewrite Hx in Hne; discriminate Hne|].
    exact (HN E' ms' m' ltac:(rewrite Heb; exact HPB) HMP' HS').
  - intros eid T' Hf E' ms' m' Heb HMP' HS' Hat. rewrite He in Hf.
    exact (Forall_imap_of _ _ ecl eid T' HNe Hf E' ms' m' ltac:(rewrite Heb; exact HPB) HMP' HS' Hat).
Qed.

Definition ctab_ok (tab : IMap.t contract) : Prop :=
  forall cid ct, IMap.find cid tab = Some ct -> contract_sound segs (OPS R) MP PB ct.

Lemma contracts_ok_of : forall C, ctab_ok (c_contracts C) -> contracts_ok segs (OPS R) C MP PB.
Proof. intros C H cid ct Hf. exact (H cid ct Hf). Qed.

Lemma ctab_ok_of_list : forall (l : list (int * contract)),
  Forall (fun kv => contract_sound segs (OPS R) MP PB (snd kv)) l -> ctab_ok (imap_of l).
Proof. intros l HF cid ct Hf. exact (Forall_imap_of _ _ l cid ct HF Hf). Qed.

Lemma node_exit : forall T c z, exit_code T = Some c -> w2Z c = z -> ENODE T (DR R (SX z)).
Proof.
  intros T c z Hc Hz E ms m HPB HMP HS Hat. cbn [DR D]. unfold X.
  rewrite <- (r_MP_fs R m HMP), <- Hz. exact (fx_node_exit segs (OPS R) T c Hc E ms m HS Hat).
Qed.

Definition ecall_atb (pc : int) : bool :=
  match fetch_word segs (Z_to_bv 64 (to_Z pc)) with Some w => is_ecall w | None => false end.
Lemma ecall_atb_sound : forall pc, ecall_atb pc = true -> ecall_at segs pc.
Proof.
  intros pc H. unfold ecall_atb in H. destruct (fetch_word segs (Z_to_bv 64 (to_Z pc))) as [w|] eqn:Hw; [|discriminate H].
  exists w. split; [exact Hw | exact H].
Qed.

Definition fdok (st : sstate) : bool := existsb is_fd_op (s_ops st).

Lemma FDS0_lookup : forall fds fd, fd = 1 \/ fd = 2 ->
  (forall e, In e fds -> fst e = fd3) ->
  fd_lookup (fds ++ FDS0) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)).
Proof.
  intros fds fd Hfd Hfds. induction fds as [|[k e] fds IH]; cbn [app fd_lookup].
  - unfold FDS0. cbn [fd_lookup fst snd]. destruct Hfd as [-> | ->]; reflexivity.
  - pose proof (Hfds (k, e) (or_introl eq_refl)) as Hk. cbn [fst] in Hk. subst k.
    replace (bv_eqb fd3 (Z_to_bv 64 fd)) with false.
    + apply IH. intros e' He'. apply Hfds. right. exact He'.
    + symmetry. unfold bv_eqb, fd3. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. apply Z.eqb_neq. destruct Hfd as [-> | ->]; cbn; lia.
Qed.

Lemma fdok_sound : forall E st ms model, st_ok segs (OPS R) E st ms model -> fdok st = true ->
  forall fd, fd = 1 \/ fd = 2 -> fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)).
Proof.
  intros E st ms model HS Hok fd Hfd. unfold fdok in Hok. apply existsb_exists in Hok. destruct Hok as (o & Hin & Ho).
  pose proof (CtrSys.ops_hold_In (OPS R) E _ _ _ o (so_ops _ _ _ _ _ _ HS) Hin) as Hh.
  unfold OPS, CtrSys.OPS in Hh. rewrite mk_holds in Hh. destruct o as [id args]. cbn [op_id op_args] in Hh, Ho.
  unfold is_fd_op in Ho. cbn [op_id] in Ho.
  apply orb_prop in Ho. destruct Ho as [Ho | Ho]; [apply orb_prop in Ho; destruct Ho as [Ho | Ho]|];
    apply Uint63.eqb_correct in Ho; subst id.
  - rewrite comp_5 in Hh. cbn [FDINIT oc_pure oc_holds fdinit_holds] in Hh. destruct (map (den E) args); [|contradiction].
    rewrite Hh. apply (FDS0_lookup []); [exact Hfd | intros e []].
  - rewrite comp_2 in Hh. cbn [FD3 oc_pure oc_holds fd3_holds] in Hh. destruct (map (den E) args) as [|off [|? ?]]; try contradiction.
    destruct Hh as [Hh _]. rewrite Hh. apply (FDS0_lookup [(fd3, FdFile (r_p1 R) off)]); [exact Hfd | intros e [<-|[]]; reflexivity].
  - rewrite comp_4 in Hh. cbn [FD3DIR oc_pure oc_holds fd3dir_holds] in Hh. destruct (map (den E) args); [|contradiction].
    rewrite Hh. apply (FDS0_lookup [(fd3, FdDir)]); [exact Hfd | intros e [<-|[]]; reflexivity].
Qed.

Section SW.
Variables (it : itab) (L : layout).
Hypothesis HIT : itab_ok segs it.

Theorem node_sw : forall (T P : sstate) (C : swcert) (fd : Z) (bs : list byte) (K : TSet),
  sw_verify segs it L fdok T P C = true ->
  run segs it [] T = SStop KEcall (c_T1 C) ->
  Forall (explore_eqs segs it (c_ra C)) (c_tpls C) ->
  c_fd C = fd ->
  (forall E, PB (eb E) -> ev E 0%uint63 = Z_to_bv 64 0 -> facts_hold E (s_facts T) -> sw_bytes C E = bs) ->
  K [] -> NODE P K ->
  NODE T (W fd bs K).
Proof.
  intros T P C fd bs K HV Hrun HX Hfd Hbs HK HP E ms m HPB HMP HS.
  rewrite <- (Hbs E HPB (so_zero _ _ _ _ _ _ HS) (so_facts _ _ _ _ _ _ HS)), <- Hfd.
  apply (stdio_write_sound segs (OPS R) it L fdok HIT fdok_sound MP (r_MPA R) T P C E ms m K HV Hrun HX HS HMP HK).
  intros E' ms' mo' Heb HMP' HS'. apply (HP E' ms' mo'); [rewrite Heb; exact HPB | exact HMP' | exact HS'].
Qed.
End SW.

Definition LENX (jl : int) : sv := VAlu ALU_SUB (VBlob false jl (VL wzero) 8%uint63) (VL (wlit 1%uint63)).
Record strent := SE { se_j : int; se_jl : int; se_c : chunk }.
Definition STRS : list strent := [SE 1%uint63 9%uint63 CA0; SE 3%uint63 10%uint63 CP1].
Definition str_of_blob (j : int) : option strent := find (fun e => PrimInt63.eqb (se_j e) j) STRS.

Inductive bitem := IZ (z : Z) | IB (j : int) (i : Z) | IS (c : chunk).

Definition item_of_sv (v : sv) : option bitem :=
  match v with
  | VL w => Some (IZ (w2Z w mod 256))
  | VBlob false j (VL i) n => if PrimInt63.eqb n 1%uint63 then Some (IB j (w2Z i)) else None
  | VExt false lo n (VBlob false j (VL i) n1) =>
      if PrimInt63.eqb lo 0%uint63 && PrimInt63.eqb n 1%uint63 && PrimInt63.eqb n1 1%uint63 then Some (IB j (w2Z i)) else None
  | _ => None
  end.

Definition items_of_desc (d : bdesc) : option (list bitem) :=
  match d with
  | BLit vs => omap item_of_sv vs
  | BBlob j off len =>
      match lit_Z len with
      | Some n => if 0 <=? off then Some (map (fun i => IB j (off + Z.of_nat i)) (seq 0 (Z.to_nat n))) else None
      | None =>
          match str_of_blob j with
          | Some e => if Z.eqb off 0 && sv_eqb len (LENX (se_jl e)) then Some [IS (se_c e)] else None
          | None => None
          end
      end
  end.

Fixpoint items_of_wes (wes : list went) : option (list bitem) :=
  match wes with
  | [] => Some []
  | w :: wes' => match items_of_desc (we_bytes w), items_of_wes wes' with
                 | Some a, Some b => Some (a ++ b)
                 | _, _ => None
                 end
  end.

Definition is_len_fact (jl : int) (n : Z) (f : fact) : bool :=
  match f with
  | FEq a (VL w) => sv_eqb a (LENX jl) && Z.eqb (w2Z w) n
  | _ => false
  end.
Definition has_len_fact (fs : list fact) (jl : int) (n : Z) : bool := existsb (is_len_fact jl n) fs.

Fixpoint blob_run (j : int) (i : Z) (its : list bitem) : nat * list bitem :=
  match its with
  | IB j' i' :: r => if PrimInt63.eqb j' j && Z.eqb i' i
                     then let (n, r') := blob_run j (i + 1) r in (S n, r')
                     else (O, its)
  | _ => (O, its)
  end.

Fixpoint chunks_of (fs : list fact) (fuel : nat) (its : list bitem) : option (list chunk) :=
  match fuel with
  | O => match its with [] => Some [] | _ => None end
  | S fuel' =>
      match its with
      | [] => Some []
      | IZ z :: r => option_map (cons (CLit [z])) (chunks_of fs fuel' r)
      | IS c :: r => option_map (cons c) (chunks_of fs fuel' r)
      | IB j i :: r =>
          if Z.eqb i 0 then
            let (n, r') := blob_run j 1 r in
            match str_of_blob j with
            | Some e => if has_len_fact fs (se_jl e) (Z.of_nat (S n))
                        then option_map (cons (se_c e)) (chunks_of fs fuel' r')
                        else None
            | None => None
            end
          else None
      end
  end.

Definition bytes_chk (fs : list fact) (wes : list went) : option (list chunk) :=
  match items_of_wes wes with
  | Some its => option_map cnorm (chunks_of fs (length its) its)
  | None => None
  end.

Definition strip_empty (fs : list fact) (cs : list chunk) : list chunk :=
  List.filter (fun c => match c with
                   | CA0 => negb (has_len_fact fs 9%uint63 0%Z)
                   | CP1 => negb (has_len_fact fs 10%uint63 0%Z)
                   | CLit _ => true
                   end) cs.
Fixpoint stripf (fs : list fact) (s : shp) : shp :=
  match s with
  | SWr fd cs k => SWr fd (strip_empty fs cs) (stripf fs k)
  | SX c => SX c
  | SALT a b => SALT (stripf fs a) (stripf fs b)
  end.
Definition shp_eqv_f (fs : list fact) (a b : shp) : bool := shp_eqv (stripf fs a) (stripf fs b).

Let a0 := r_a0 R.
Let p1 := r_p1 R.

Definition den_item (E : env) (it : bitem) : list byte :=
  match it with
  | IZ z => [Z_to_bv 8 z]
  | IB j i => [nth (Z.to_nat i) (eb E j) (Z_to_bv 8 0)]
  | IS c => den_chunk a0 p1 c
  end.
Definition den_items (E : env) (its : list bitem) : list byte := flat_map (den_item E) its.

Lemma den_items_app : forall E a b, den_items E (a ++ b) = den_items E a ++ den_items E b.
Proof. intros. unfold den_items. apply flat_map_app. Qed.

Lemma lowbyte_of_unsigned : forall (w : word) z, bv_unsigned w mod 256 = z mod 256 -> lowbyte w = Z_to_bv 8 z.
Proof.
  intros w z H. unfold lowbyte. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. exact H.
Qed.

Lemma byte_small : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range _ b) as H. unfold bv_modulus in H. exact H. Qed.

Lemma lowbyte_eq : forall (w : word) (b : byte), bv_unsigned w mod 256 = bv_unsigned b -> lowbyte w = b.
Proof.
  intros w b H. unfold lowbyte. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. exact H.
Qed.

Lemma w2Z_range : forall w, 0 <= w2Z w < two64.
Proof. intros w. rewrite <- wbv_unsigned. pose proof (u64_range (wbv w)) as H. unfold two64. exact H. Qed.

Lemma den_blob1 : forall E j (w : w64),
  bv_unsigned (den E (VBlob false j (VL w) 1%uint63)) = bv_unsigned (nth (Z.to_nat (w2Z w)) (eb E j) (Z_to_bv 8 0)).
Proof.
  intros E j w. cbn [den]. rewrite wbv_unsigned. change (to_Z 1%uint63) with 1.
  unfold bytes_val, blob_bytes. change (Z.to_nat 1) with 1%nat.
  destruct (skipn (Z.to_nat (w2Z w)) (eb E j)) as [|b rest] eqn:Hs.
  - cbn [firstn bytes_le_to_Z]. rewrite nth_overflow.
    + rewrite Z_to_bv64_unsigned; [reflexivity|]. unfold ext_Z. cbn. lia.
    + apply (f_equal (@length byte)) in Hs. rewrite length_skipn in Hs. cbn in Hs. lia.
  - assert (Hb : nth (Z.to_nat (w2Z w)) (eb E j) (Z_to_bv 8 0) = b).
    { rewrite <- (Nat.add_0_r (Z.to_nat (w2Z w))), <- nth_skipn, Hs. reflexivity. }
    rewrite Hb. cbn [firstn bytes_le_to_Z]. rewrite Z.shiftl_0_l, Z.lor_0_r.
    pose proof (byte_small b). rewrite Z_to_bv64_unsigned; unfold ext_Z.
    + change (2 ^ (8 * 0)) with 1. change (2 ^ (8 * 1)) with 256. rewrite Z.div_1_r. apply Z.mod_small. lia.
    + change (2 ^ (8 * 0)) with 1. change (2 ^ (8 * 1)) with 256. rewrite Z.div_1_r, Z.mod_small by lia. lia.
Qed.

Lemma den_ext01 : forall E a, bv_unsigned (den E (VExt false 0%uint63 1%uint63 a)) = bv_unsigned (den E a) mod 256.
Proof.
  intros E a. cbn [den]. unfold ext_word. change (to_Z 0%uint63) with 0. change (to_Z 1%uint63) with 1.
  unfold ext_Z. change (2 ^ (8 * 0)) with 1. change (2 ^ (8 * 1)) with 256. rewrite Z.div_1_r.
  pose proof (Z.mod_pos_bound (bv_unsigned (den E a)) 256 ltac:(lia)).
  rewrite Z_to_bv64_unsigned; lia.
Qed.

Lemma item_of_sv_sound : forall E v it, item_of_sv v = Some it -> [lowbyte (den E v)] = den_item E it.
Proof.
  intros E v it H.
  assert (CB : forall (x : word) j w, bv_unsigned x mod 256 = bv_unsigned (den E (VBlob false j (VL w) 1%uint63)) mod 256 ->
                                     [lowbyte x] = den_item E (IB j (w2Z w))).
  { intros x j w Hx. cbn [den_item]. f_equal. apply lowbyte_eq. rewrite Hx, den_blob1.
    pose proof (byte_small (nth (Z.to_nat (w2Z w)) (eb E j) (Z_to_bv 8 0))). apply Z.mod_small. lia. }
  destruct v; cbn [item_of_sv] in H; try discriminate H.
  - injection H as <-. cbn [den_item]. f_equal. apply lowbyte_of_unsigned. cbn [den]. rewrite wbv_unsigned, Z.mod_mod by lia. reflexivity.
  -
    destruct sx; [discriminate H|]. destruct v; try discriminate H. destruct sx; [discriminate H|]. destruct v; try discriminate H.
    destruct (PrimInt63.eqb lo 0 && PrimInt63.eqb n 1 && PrimInt63.eqb n0 1)%bool eqn:Hc; [|discriminate H]. injection H as <-.
    apply andb_prop in Hc as [Hc H1]. apply andb_prop in Hc as [H0 Hn].
    apply Uint63.eqb_correct in H0. apply Uint63.eqb_correct in Hn. apply Uint63.eqb_correct in H1. subst lo n n0.
    apply CB. rewrite den_ext01. apply Z.mod_mod. lia.
  -
    destruct sx; [discriminate H|]. destruct v; try discriminate H.
    destruct (PrimInt63.eqb n 1) eqn:Hn; [|discriminate H]. injection H as <-. apply Uint63.eqb_correct in Hn. subst n.
    apply CB. reflexivity.
Qed.

Definition str_ok (E : env) (e : strent) : Prop :=
  let s := den_chunk a0 p1 (se_c e) in
  eb E (se_j e) = cstr s /\ eb E (se_jl e) = LE8 (Z.of_nat (length s) + 1) /\ Z.of_nat (length s) <= 131071.

Lemma str_of_blob_ok : forall E j e, PB (eb E) -> str_of_blob j = Some e -> se_j e = j /\ str_ok E e.
Proof.
  intros E j e HPB H. unfold str_of_blob, STRS in H. cbn [find se_j] in H.
  destruct (PrimInt63.eqb 1 j) eqn:E1.
  - injection H as <-. apply Uint63.eqb_correct in E1. split; [exact E1|].
    destruct (r_PB_a0 R _ HPB) as [H1 H9]. unfold str_ok. cbn [se_j se_jl se_c den_chunk]. repeat split; try assumption. apply r_a0_len.
  - destruct (PrimInt63.eqb 3 j) eqn:E3; [|discriminate H].
    injection H as <-. apply Uint63.eqb_correct in E3. split; [exact E3|].
    destruct (r_PB_p1 R _ HPB) as [H3 H10]. unfold str_ok. cbn [se_j se_jl se_c den_chunk]. repeat split; try assumption. apply r_p1_len.
Qed.

Lemma den_LENX : forall E e, str_ok E e -> bv_unsigned (den E (LENX (se_jl e))) = Z.of_nat (length (den_chunk a0 p1 (se_c e))).
Proof.
  intros E e (Hj & Hjl & Hlen). unfold LENX. rewrite OL.den_sub.
  change (VL wzero) with (VL (wp 0%uint63)). rewrite (den_param8_u E (se_jl e) _ Hjl) by lia.
  cbn [den]. rewrite wbv_unsigned, wlit_ok. change (to_Z 1%uint63) with 1. rewrite Z.mod_small by lia. lia.
Qed.

Lemma map_nth_seq_prefix : forall (s t : list byte) k n, (k + n <= length s)%nat ->
  map (fun i => nth (k + i) (s ++ t) (Z_to_bv 8 0)) (seq 0 n) = firstn n (skipn k s).
Proof.
  intros s t k n. revert k. induction n as [|n IH]; intros k Hk.
  - cbn [seq map]. rewrite firstn_O. reflexivity.
  - cbn [seq map]. rewrite <- seq_shift, map_map.
    destruct (skipn k s) as [|b r] eqn:Hs.
    { exfalso. apply (f_equal (@length byte)) in Hs. rewrite length_skipn in Hs. cbn in Hs. lia. }
    cbn [firstn]. f_equal.
    + rewrite Nat.add_0_r, app_nth1 by lia. rewrite <- (Nat.add_0_r k), <- nth_skipn, Hs. reflexivity.
    + replace r with (skipn (S k) s).
      * rewrite <- (IH (S k)) by lia. apply map_ext. intros i. f_equal. lia.
      * replace (S k) with (1 + k)%nat by lia. rewrite <- skipn_skipn, Hs. reflexivity.
Qed.

Lemma map_nth_seq_whole : forall (s : list byte),
  map (fun i => nth i (cstr s) (Z_to_bv 8 0)) (seq 0 (length s)) = s.
Proof.
  intros s. unfold cstr. pose proof (map_nth_seq_prefix s [Z_to_bv 8 0] 0 (length s) ltac:(lia)) as H.
  cbn [Nat.add] in H. rewrite skipn_O, firstn_all in H. exact H.
Qed.

Lemma den_items_map_IB : forall E j (f : nat -> Z) n,
  den_items E (map (fun i => IB j (f i)) (seq 0 n)) = map (fun i => nth (Z.to_nat (f i)) (eb E j) (Z_to_bv 8 0)) (seq 0 n).
Proof. intros E j f n. unfold den_items. rewrite flat_map_concat_map, map_map. cbn [den_item]. induction (seq 0 n) as [|x l IH]; [reflexivity|]. cbn [map concat app]. rewrite IH. reflexivity. Qed.

Lemma items_of_desc_sound : forall E d its, PB (eb E) -> items_of_desc d = Some its -> desc_bytes E d = den_items E its.
Proof.
  intros E d its HPB H. destruct d as [vs | j off len]; cbn [items_of_desc] in H.
  - revert its H. induction vs as [|v vs IH]; intros its H; cbn [omap] in H.
    + injection H as <-. reflexivity.
    + destruct (item_of_sv v) as [it|] eqn:Hv; [|discriminate H]. destruct (omap item_of_sv vs) as [r|] eqn:Hr; [|discriminate H].
      injection H as <-. cbn [desc_bytes map]. change (den_items E (it :: r)) with (den_item E it ++ den_items E r).
      rewrite <- (item_of_sv_sound E v it Hv), <- (IH r eq_refl). reflexivity.
  - destruct (lit_Z len) as [n|] eqn:Hn.
    + destruct (0 <=? off) eqn:Hoff; [|discriminate H]. injection H as <-. apply Z.leb_le in Hoff.
      destruct (lit_Z_sound E len n Hn) as [HL Hnr].
      cbn [desc_bytes]. rewrite HL, den_items_map_IB. apply map_ext. intros i. f_equal. lia.
    + destruct (str_of_blob j) as [e|] eqn:He; [|discriminate H].
      destruct (Z.eqb off 0 && sv_eqb len (LENX (se_jl e)))%bool eqn:Hc; [|discriminate H]. injection H as <-.
      apply andb_prop in Hc as [Ho Hl]. apply Z.eqb_eq in Ho. apply sv_eqb_eq in Hl. subst off len.
      destruct (str_of_blob_ok E j e HPB He) as [Hj Hok]. pose proof Hok as (Hb & _ & _).
      cbn [desc_bytes]. rewrite (den_LENX E e Hok), Nat2Z.id. rewrite <- Hj, Hb.
      unfold den_items. cbn [flat_map den_item]. rewrite app_nil_r. cbn [Z.to_nat Nat.add]. apply map_nth_seq_whole.
Qed.

Lemma items_of_wes_sound : forall E wes its, PB (eb E) -> items_of_wes wes = Some its ->
  concat (map (ent_bytes E) wes) = den_items E its.
Proof.
  intros E wes. induction wes as [|w wes IH]; intros its HPB H; cbn [items_of_wes] in H.
  - injection H as <-. reflexivity.
  - destruct (items_of_desc (we_bytes w)) as [a|] eqn:Ha; [|discriminate H]. destruct (items_of_wes wes) as [b|] eqn:Hb; [|discriminate H].
    injection H as <-. cbn [map concat]. unfold ent_bytes at 1. rewrite (items_of_desc_sound E _ a HPB Ha), (IH b HPB eq_refl), den_items_app. reflexivity.
Qed.

Lemma blob_run_spec : forall j its i n r', blob_run j i its = (n, r') ->
  its = map (fun k => IB j (i + Z.of_nat k)) (seq 0 n) ++ r' /\ (length r' <= length its)%nat.
Proof.
  intros j its. induction its as [|it its IH]; intros i n r' H; cbn [blob_run] in H.
  - injection H as <- <-. split; [reflexivity | cbn; lia].
  - destruct it as [z | j' i' | c]; try (injection H as <- <-; split; [reflexivity | cbn; lia]).
    destruct (PrimInt63.eqb j' j && Z.eqb i' i)%bool eqn:Hc.
    + apply andb_prop in Hc as [Hj Hi]. apply Uint63.eqb_correct in Hj. apply Z.eqb_eq in Hi. subst j' i'.
      destruct (blob_run j (i + 1) its) as [n1 r1] eqn:Hrun. injection H as <- <-.
      destruct (IH (i + 1) n1 r1 Hrun) as [Hits Hlen]. split; [|cbn; lia].
      cbn [seq map app]. rewrite <- seq_shift, map_map, Z.add_0_r. f_equal. rewrite Hits at 1. f_equal. apply map_ext. intros k. f_equal. lia.
    + injection H as <- <-. split; [reflexivity | cbn; lia].
Qed.

Lemma has_len_fact_sound : forall E fs e n, facts_hold E fs -> str_ok E e -> has_len_fact fs (se_jl e) n = true ->
  Z.of_nat (length (den_chunk a0 p1 (se_c e))) = n.
Proof.
  intros E fs e n Hfs Hok H. unfold has_len_fact in H. apply existsb_exists in H. destruct H as (f & Hin & Hf).
  pose proof (proj1 (Forall_forall _ _) Hfs f Hin) as HF.
  destruct f; cbn [is_len_fact] in Hf; try discriminate Hf. destruct b; try discriminate Hf.
  apply andb_prop in Hf as [Ha Hw]. apply sv_eqb_eq in Ha. apply Z.eqb_eq in Hw. subst a n.
  cbn [fact_holds] in HF. apply (f_equal bv_unsigned) in HF. rewrite (den_LENX E e Hok) in HF. cbn [den] in HF. rewrite wbv_unsigned in HF. exact HF.
Qed.

Lemma chunks_of_sound : forall E fs fuel its cs, PB (eb E) -> facts_hold E fs -> chunks_of fs fuel its = Some cs ->
  den_items E its = den_chunks a0 p1 cs.
Proof.
  intros E fs fuel. induction fuel as [|fuel IH]; intros its cs HPB Hfs H; cbn [chunks_of] in H.
  - destruct its; [|discriminate H]. injection H as <-. reflexivity.
  - destruct its as [|it r]; [injection H as <-; reflexivity|].
    destruct it as [z | j i | c].
    + destruct (chunks_of fs fuel r) as [cs'|] eqn:Hr; [|discriminate H]. injection H as <-.
      change (den_items E (IZ z :: r)) with (den_item E (IZ z) ++ den_items E r). rewrite (IH r cs' HPB Hfs Hr). reflexivity.
    + destruct (Z.eqb i 0) eqn:Hi; [|discriminate H]. apply Z.eqb_eq in Hi. subst i.
      destruct (blob_run j 1 r) as [n r'] eqn:Hrun.
      destruct (str_of_blob j) as [e|] eqn:He; [|discriminate H].
      destruct (has_len_fact fs (se_jl e) (Z.of_nat (S n))) eqn:Hlen; [|discriminate H].
      destruct (chunks_of fs fuel r') as [cs'|] eqn:Hr'; [|discriminate H]. injection H as <-.
      destruct (blob_run_spec j r 1 n r' Hrun) as [Hr _].
      destruct (str_of_blob_ok E j e HPB He) as [Hj Hok]. pose proof Hok as (Hb & _ & _).
      pose proof (has_len_fact_sound E fs e _ Hfs Hok Hlen) as HL.
      change (den_items E (IB j 0 :: r)) with (den_item E (IB j 0) ++ den_items E r).
      rewrite Hr, den_items_app, (IH r' cs' HPB Hfs Hr'). cbn [den_chunks]. rewrite app_assoc. f_equal.

      rewrite den_items_map_IB. cbn [den_item]. rewrite <- Hj, Hb.
      set (s0 := den_chunk a0 p1 (se_c e)) in *. apply Nat2Z.inj in HL.
      transitivity (map (fun i => nth i (cstr s0) (Z_to_bv 8 0)) (seq 0 (length s0))); [| apply map_nth_seq_whole]. rewrite HL.
      cbn [seq map]. f_equal. rewrite <- seq_shift, map_map. apply map_ext. intros k. f_equal. lia.
    + destruct (chunks_of fs fuel r) as [cs'|] eqn:Hr; [|discriminate H]. injection H as <-.
      change (den_items E (IS c :: r)) with (den_item E (IS c) ++ den_items E r). rewrite (IH r cs' HPB Hfs Hr). reflexivity.
Qed.

Theorem bytes_chk_sound : forall fs wes cs E,
  bytes_chk fs wes = Some cs -> PB (eb E) -> facts_hold E fs ->
  concat (map (ent_bytes E) wes) = den_chunks a0 p1 cs.
Proof.
  intros fs wes cs E H HPB Hfs. unfold bytes_chk in H.
  destruct (items_of_wes wes) as [its|] eqn:Hits; [|discriminate H].
  destruct (chunks_of fs (length its) its) as [cs0|] eqn:Hc; [|discriminate H]. cbn [option_map] in H. injection H as <-.
  rewrite cnorm_sound. rewrite (items_of_wes_sound E wes its HPB Hits). apply (chunks_of_sound E fs _ _ _ HPB Hfs Hc).
Qed.

Section SWB.
Variables (it : itab) (L : layout).
Hypothesis HIT : itab_ok segs it.

Theorem node_sw_b : forall (T P : sstate) (C : swcert) (fd : Z) (cs : list chunk) (k : shp),
  sw_verify segs it L fdok T P C
  && sres_eqb (run segs it [] T) (c_T1 C)
  && forallb (fun t => explore_chk_comb (lt_c (tc_tpl t)) (explore segs it FUEL (c_ra C) (post_done (tc_tpl t)))
                         (explore segs it FUEL (c_ra C) (post_loop (tc_tpl t) false))
                         (explore segs it FUEL (c_ra C) (post_loop (tc_tpl t) true))
                         (tc_exits t) (tc_ns t) (tc_sw t)) (c_tpls C)
  && Z.eqb (c_fd C) fd
  && match bytes_chk (s_facts T) (c_wes C) with Some cs' => chunks_eqb cs' cs | None => false end = true ->
  NODE P (DR R k) -> NODE T (DR R (SWr fd cs k)).
Proof.
  intros T P C fd cs k H HP.
  apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H4.
  destruct (bytes_chk (s_facts T) (c_wes C)) as [cs'|] eqn:HB; [|discriminate H5]. apply chunks_eqb_eq in H5. subst cs'.
  change (DR R (SWr fd cs k)) with (W fd (den_chunks a0 p1 cs) (DR R k)).
  intros E ms m HPB HMP HS.
  rewrite <- (bytes_chk_sound _ _ _ E HB HPB (so_facts _ _ _ _ _ _ HS)), <- H4.
  apply (stdio_write_sound_b segs (OPS R) it L fdok HIT fdok_sound MP (r_MPA R) T P C E ms m (DR R k) H1 H2 H3 HS HMP (D_nil _ _ _ _)).
  intros E' ms' mo' Heb HMP' HS'. apply (HP E' ms' mo'); [rewrite Heb; exact HPB | exact HMP' | exact HS'].
Qed.
End SWB.

Lemma filter_chunks : forall (keep : chunk -> bool) cs,
  (forall c, keep c = false -> den_chunk a0 p1 c = []) -> den_chunks a0 p1 (List.filter keep cs) = den_chunks a0 p1 cs.
Proof.
  intros keep cs Hk. induction cs as [|c cs IH]; [reflexivity|]. cbn [List.filter].
  destruct (keep c) eqn:Kc; cbn [den_chunks]; rewrite IH; [reflexivity|]. rewrite (Hk c Kc). reflexivity.
Qed.

Lemma strip_empty_sound : forall E fs cs, PB (eb E) -> facts_hold E fs ->
  den_chunks a0 p1 (strip_empty fs cs) = den_chunks a0 p1 cs.
Proof.
  intros E fs cs HPB Hfs. unfold strip_empty. apply filter_chunks.
  assert (Z0 : forall e, str_ok E e -> has_len_fact fs (se_jl e) 0%Z = true -> den_chunk a0 p1 (se_c e) = []).
  { intros e Hok Hl. pose proof (has_len_fact_sound E fs e 0%Z Hfs Hok Hl) as HL.
    destruct (den_chunk a0 p1 (se_c e)); [reflexivity | cbn in HL; lia]. }
  intros c Hc. destruct c as [zs| |]; [discriminate Hc| |]; apply negb_false_iff in Hc.
  - destruct (str_of_blob_ok E 1%uint63 (SE 1%uint63 9%uint63 CA0) HPB eq_refl) as [_ Hok]. exact (Z0 _ Hok Hc).
  - destruct (str_of_blob_ok E 3%uint63 (SE 3%uint63 10%uint63 CP1) HPB eq_refl) as [_ Hok]. exact (Z0 _ Hok Hc).
Qed.

Lemma stripf_sound : forall E fs s, PB (eb E) -> facts_hold E fs -> t_eq (DR R (stripf fs s)) (DR R s).
Proof.
  intros E fs s HPB Hfs. unfold DR. fold a0 p1. induction s as [fd cs k IH | c | a IHa b IHb]; cbn [stripf D].
  - change (den_chunks (r_a0 R) (r_p1 R)) with (den_chunks a0 p1). rewrite (strip_empty_sound E fs cs HPB Hfs). apply W_cong. exact IH.
  - apply t_eq_refl.
  - apply alt2_cong; assumption.
Qed.

Theorem node_eqv_f : forall T a b, shp_eqv_f (s_facts T) a b = true -> NODE T (DR R a) -> NODE T (DR R b).
Proof.
  intros T a b Hab HN. apply (node_facts T _ _ HN). intros E HPB _ Hfs.
  eapply t_eq_trans; [apply t_eq_sym; apply (stripf_sound E _ a HPB Hfs)|].
  eapply t_eq_trans; [| apply (stripf_sound E _ b HPB Hfs)]. apply shp_eqv_sound. exact Hab.
Qed.

Let p1' := r_p1 R.
Lemma PB_arg1 : forall b, PB b -> b 3%uint63 = p1' ++ [Z_to_bv 8 0] /\ b 10%uint63 = Z_to_le_bytes 8 (Z.of_nat (length p1') + 1).
Proof. intros b Hb. exact (r_PB_p1 R b Hb). Qed.

Section OpenFile.
Hypothesis MP_file : forall m, MP m -> fs_lookup (m_fs m) (r_p1 R) = Some (r_file R).
Hypothesis fam_file : path_has_slash (r_p1 R) = false /\ path_is_dirref (r_p1 R) = false /\ (length (r_p1 R) < 4096)%nat /\ r_p1 R <> [].

Theorem node_open_file : forall (T : sstate) (sts : list sstate) (KA KB : TSet),
  open_file_apply T = Some sts -> ecall_atb (s_pc T) = true ->
  NODE (hd T sts) KA -> Forall (fun st' => NODE st' KB) (tl sts) ->
  NODE T (t_alt2 KA KB).
Proof.
  intros T sts KA KB Happ Hat HA HB E ms m HPB HMP HS.
  apply (CtrSys.open_file_fork segs (r_heap R) (r_ext R) (r_p1 R) (r_file R) (r_RS R) (r_RSr R) (r_heap_fds R) (r_ext_fds R) (r_tm R) (r_tm_fds R) (r_tm_cov1 R) MP (r_MP_fds R) (r_MPA R) PB
           MP_file PB_arg1 (r_p1_nz R) (r_p1_len R) fam_file T sts KA KB E ms m Happ HS HMP HPB (ecall_atb_sound _ Hat)).
  - intros ms' m' HMP' HS'. exact (HA E ms' m' HPB HMP' HS').
  - intros st' Hin ms' m' HMP' HS'. exact (proj1 (Forall_forall _ _) HB st' Hin E ms' m' HPB HMP' HS').
Qed.
End OpenFile.

Section OpenDir.
Hypothesis fam_dir : path_is_dirref (r_p1 R) = true.

Theorem node_open_dir : forall (T : sstate) (sts : list sstate) (KA KB : TSet),
  open_dir_apply T = Some sts -> ecall_atb (s_pc T) = true ->
  NODE (hd T sts) KA -> Forall (fun st' => NODE st' KB) (tl sts) ->
  NODE T (t_alt2 KA KB).
Proof.
  intros T sts KA KB Happ Hat HA HB E ms m HPB HMP HS.
  apply (CtrSys.open_dir_fork segs (r_heap R) (r_ext R) (r_p1 R) (r_file R) (r_RS R) (r_RSr R) (r_heap_fds R) (r_ext_fds R) (r_tm R) (r_tm_fds R) (r_tm_cov1 R) MP (r_MP_fds R) (r_MPA R) PB
           PB_arg1 (r_p1_nz R) (r_p1_len R) fam_dir T sts KA KB E ms m Happ HS HMP HPB (ecall_atb_sound _ Hat)).
  - intros ms' m' HMP' HS'. exact (HA E ms' m' HPB HMP' HS').
  - intros st' Hin ms' m' HMP' HS'. exact (proj1 (Forall_forall _ _) HB st' Hin E ms' m' HPB HMP' HS').
Qed.
End OpenDir.

Definition mfork_ok (pc : int) (app : sstate -> option (list sstate)) : Prop :=
  forall st stA stB (KA KB : TSet) E ms m,
    s_pc st = pc -> app st = Some [stA; stB] ->
    st_ok segs (OPS R) E st ms m -> MP m -> PB (eb E) ->
    (forall E' ms' m', env_ext (s_next st) E E' -> MP m' -> st_ok segs (OPS R) E' stA ms' m' -> realizes segs (mkCfg ms' m') KA) ->
    (forall E' ms' m', env_ext (s_next st) E E' -> MP m' -> st_ok segs (OPS R) E' stB ms' m' -> realizes segs (mkCfg ms' m') KB) ->
    realizes segs (mkCfg ms m) (t_alt2 KA KB).

Definition mnofork_ok (pc : int) (app : sstate -> option (list sstate)) : Prop :=
  forall st stA stB (KB : TSet) E ms m,
    s_pc st = pc -> app st = Some [stA; stB] ->
    st_ok segs (OPS R) E st ms m -> MP m -> PB (eb E) ->
    (forall E' ms' m', env_ext (s_next st) E E' -> MP m' -> st_ok segs (OPS R) E' stB ms' m' -> realizes segs (mkCfg ms' m') KB) ->
    realizes segs (mkCfg ms m) KB.

Theorem node_mnofork : forall pc app (T stA stB : sstate) (KB : TSet),
  mnofork_ok pc app -> s_pc T = pc -> app T = Some [stA; stB] -> NODE stB KB -> NODE T KB.
Proof.
  intros pc app T stA stB KB HF Hpc Happ HB E ms m HPB HMP HS.
  apply (HF T stA stB KB E ms m Hpc Happ HS HMP HPB).
  intros E' ms' m' HX HMP' HS'. apply (HB E' ms' m'); [destruct HX as [Hb _]; rewrite Hb; exact HPB | exact HMP' | exact HS'].
Qed.

Theorem node_mfork : forall pc app (T stA stB : sstate) (KA KB : TSet),
  mfork_ok pc app -> s_pc T = pc -> app T = Some [stA; stB] -> NODE stA KA -> NODE stB KB -> NODE T (t_alt2 KA KB).
Proof.
  intros pc app T stA stB KA KB HF Hpc Happ HA HB E ms m HPB HMP HS.
  apply (HF T stA stB KA KB E ms m Hpc Happ HS HMP HPB).
  - intros E' ms' m' HX HMP' HS'. apply (HA E' ms' m'); [destruct HX as [Hb _]; rewrite Hb; exact HPB | exact HMP' | exact HS'].
  - intros E' ms' m' HX HMP' HS'. apply (HB E' ms' m'); [destruct HX as [Hb _]; rewrite Hb; exact HPB | exact HMP' | exact HS'].
Qed.

Definition lib_ok (GEN RET : sstate) : Prop :=
  forall (K : TSet) E ms m,
    PB (eb E) -> MP m -> st_ok segs (OPS R) E GEN ms m ->
    (forall E' ms' m', env_ext (s_next GEN) E E' -> MP m' -> st_ok segs (OPS R) E' RET ms' m' -> realizes segs (mkCfg ms' m') K) ->
    realizes segs (mkCfg ms m) K.

Definition lib_sg_ok (sg : subst) (nT nG nR : int) (RET : sstate) : bool :=
  PrimInt63.leb nT nG && PrimInt63.leb nG nR && PrimInt63.ltb 0%uint63 nR && bst_b sg
  && IMap.forallb (fun k u => if PrimInt63.ltb k nG then vars_below nT u else true) sg
  && forallb (fun k => match IMap.find k sg with Some u => sv_eqb u (VP k wzero) | None => false end)
             (iota_int nG (Z.to_nat (to_Z nR - to_Z nG)))
  && svars_below nR RET.

Theorem node_lib : forall (GEN RET T : sstate) (sg : subst) (n : int) (TRET : sstate) (K : TSet),
  lib_ok GEN RET ->
  sstate_wfb GEN = true -> entails T GEN sg = true ->
  st_inst sg n RET = Some TRET ->
  lib_sg_ok sg (s_next T) (s_next GEN) (s_next RET) RET = true ->
  NODE TRET K -> NODE T K.
Proof.
  intros GEN RET T sg n TRET K HL WF EN INST OK HK E ms m HPB HMP HS.
  unfold lib_sg_ok in OK.
  apply andb_prop in OK as [OK SVB]. apply andb_prop in OK as [OK IDS]. apply andb_prop in OK as [OK BEL].
  apply andb_prop in OK as [OK BST]. apply andb_prop in OK as [OK POS]. apply andb_prop in OK as [LE1 LE2].
  apply leb_spec in LE1. apply leb_spec in LE2. apply ltb_spec in POS. change (to_Z 0%uint63) with 0 in POS.
  apply bst_b_sound in BST.
  set (nT := s_next T) in *. set (nG := s_next GEN) in *. set (nR := s_next RET) in *.
  pose proof (entails_sound segs (OPS R) E T GEN sg ms m WF EN HS) as HS1.
  apply (HL K (subst_env E sg) ms m); [cbn [subst_env eb]; exact HPB | exact HMP | exact HS1 |].
  intros E' ms' m' HX HMP' HS'.

  set (E2 := Env (fun k => if PrimInt63.ltb k nT then ev E k else ev E' k) (eb E)
                 (fun k => if PrimInt63.ltb k nT then eg E k else eg E' k)).
  assert (X2 : env_ext nT E E2).
  { split; [reflexivity|]. intros k Hk. cbn [E2 ev eg]. replace (PrimInt63.ltb k nT) with true; [auto|].
    symmetry. apply ltb_spec. exact Hk. }
  assert (BELk : forall k u, IMap.find k sg = Some u -> to_Z k < to_Z nG -> vars_below nT u = true).
  { intros k u Hf Hk. pose proof (proj1 (IMap.forallb_spec _ sg BST) BEL k u Hf) as Q. cbn beta in Q.
    replace (PrimInt63.ltb k nG) with true in Q; [exact Q|]. symmetry. apply ltb_spec. exact Hk. }
  assert (IDk : forall k, to_Z nG <= to_Z k < to_Z nR -> IMap.find k sg = Some (VP k wzero)).
  { intros k Hk. pose proof (int_range nR). pose proof (int_range nG).
    assert (Hin : In k (iota_int nG (Z.to_nat (to_Z nR - to_Z nG)))).
    { apply SW.iota_int_In; rewrite Z2Nat.id by lia; [rewrite wB_two63; lia | lia]. }
    pose proof (proj1 (forallb_forall _ _) IDS k Hin) as Q. cbn beta in Q.
    destruct (IMap.find k sg) as [u|]; [|discriminate Q]. apply sv_eqb_eq in Q. rewrite Q. reflexivity. }
  destruct HX as [HXb HXk].

  assert (AGR : env_ext nR E' (subst_env E2 sg)).
  { split; [cbn [subst_env eb E2]; symmetry; exact HXb|].
    intros k Hk. pose proof (int_range k).
    destruct (Z_lt_ge_dec (to_Z k) (to_Z nG)) as [LG|GG].
    -
      destruct (HXk k LG) as [Hev Heg]. cbn [subst_env ev eg] in Hev, Heg |- *.
      assert (EV2 : PrimInt63.ltb k nT = false -> ev E2 k = ev E' k) by (intros C; cbn [E2 ev]; rewrite C; reflexivity).
      assert (EG2 : PrimInt63.ltb k nT = false -> eg E2 k = eg E' k) by (intros C; cbn [E2 eg]; rewrite C; reflexivity).
      assert (EV1 : PrimInt63.ltb k nT = true -> ev E2 k = ev E k) by (intros C; cbn [E2 ev]; rewrite C; reflexivity).
      assert (EG1 : PrimInt63.ltb k nT = true -> eg E2 k = eg E k) by (intros C; cbn [E2 eg]; rewrite C; reflexivity).
      split.
      + rewrite Hev. destruct (IMap.find k sg) as [u|] eqn:Hf.
        * apply (PlanS.den_env_ext nT E E2 u X2 (BELk k u Hf LG)).
        * case_eq (PrimInt63.ltb k nT); intros C; [rewrite (EV1 C); reflexivity | rewrite (EV2 C), Hev; reflexivity].
      + rewrite Heg. destruct (svar sg k) as [k'|] eqn:Hsv.
        * pose proof (BELk k _ (PlanS.svar_find sg k k' Hsv) LG) as VB. cbn [vars_below] in VB. cbn [E2 eg]. rewrite VB. reflexivity.
        * case_eq (PrimInt63.ltb k nT); intros C; [rewrite (EG1 C); reflexivity | rewrite (EG2 C), Heg; reflexivity].
    -
      pose proof (IDk k ltac:(lia)) as Hf. cbn [subst_env ev eg]. unfold svar. rewrite Hf.
      assert (C : PrimInt63.ltb k nT = false).
      { destruct (PrimInt63.ltb k nT) eqn:C; [|reflexivity]. apply ltb_spec in C. lia. }
      cbn [den E2 ev eg]. rewrite weqb_refl, C. split; [|reflexivity].
      rewrite wbv_wzero. apply bv_add_0_r. reflexivity. }
  pose proof (st_ok_env segs (OPS R) nR E' (subst_env E2 sg) AGR RET ms' m' POS SVB HS') as HS2.
  pose proof (st_inst_sound segs (OPS R) E2 sg n RET TRET ms' m' INST HS2) as HS3.
  exact (HK E2 ms' m' HPB HMP' HS3).
Qed.

Lemma region_ok_mem_equiv : forall priv E m m' k r,
  (forall a, rb segs m' a = rb segs m a) -> (forall a, wb segs m' a = wb segs m a) ->
  region_ok segs priv E m k r -> region_ok segs priv E m' k r.
Proof.
  intros priv E m m' k r Hrb Hwb RO. destruct RO as [B RG V C CI BG]. constructor.
  - exact B.
  - exact RG.
  - intros K a Ha. rewrite Hrb, Hwb. exact (V K a Ha).
  - intros g gr Hg. destruct (C g gr Hg) as [S F]. split; [exact S|].
    apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) F c Hc) as (H1 & H2 & H3 & H4).
    split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. intros i Hi. rewrite Hrb. exact (H4 i Hi).
  - exact CI.
  - intros o H1 H2 H3. pose proof (BG o H1 H2 H3) as X. destruct (bg_byte segs E k r o); [rewrite Hrb; exact X | exact I].
Qed.

Lemma st_ok_mem_back : forall E st ms m' model,
  st_ok segs (OPS R) E st (ms_upd ms (with_resv (ms_resv ms) (core_of ms)) m') model ->
  s_ops st = [] -> ms_svc_pending ms = None ->
  (forall a, rb segs m' a = rb segs (ms_mem ms) a) -> (forall a, wb segs m' a = wb segs (ms_mem ms) a) ->
  (forall a b, ms_mem ms a = Some b -> forall seg, find_segment segs (bv_unsigned a) 1 = Some seg -> seg_writable seg = true) ->
  st_ok segs (OPS R) E st ms model.
Proof.
  intros E st ms m' model HS Hops Hsvc Hrb Hwb Hminv.
  destruct HS as [Hpc Hx0 Hregs Hfregs Hsvc' Hresv Hfcsr Hrom Hz Hbst Hreg Hdisj Hpub Hfacts Hop Hapart Hmf Hcov' Hminv'].
  cbn [ms_upd ms_pc_val ms_regs ms_fregs ms_fcsr ms_resv ms_mem ms_rom c_regs c_fregs c_pc c_fcsr c_resv with_resv core_of] in *.
  constructor; try assumption.
  - intros k r Hk. apply (region_ok_mem_equiv (s_priv st) E m' (ms_mem ms) k r); [intros a; symmetry; apply Hrb | intros a; symmetry; apply Hwb |].
    exact (Hreg k r Hk).
  - rewrite Hops. constructor.
Qed.

Lemma ov_read_bytes_inv : forall m A n bs, ov_read_bytes segs m (Z_to_bv 64 A) n = Some bs ->
  0 <= A -> A + Z.of_nat n <= two64 ->
  length bs = n /\ forall i, 0 <= i < Z.of_nat n -> rb segs m (A + i) = nth_error bs (Z.to_nat i).
Proof.
  intros m A n. revert A. induction n as [|n IH]; intros A bs H HA HAn.
  - cbn in H. injection H as <-. split; [reflexivity | intros i Hi; lia].
  - cbn [ov_read_bytes] in H. rewrite <- rb_unfold in H.
    destruct (rb segs m A) as [b|] eqn:Hb; [|discriminate H].
    rewrite Z_to_bv_succ in H.
    destruct (ov_read_bytes segs m (Z_to_bv 64 (A + 1)) n) as [bs'|] eqn:Hr; [|discriminate H]. injection H as <-.
    destruct (IH (A + 1) bs' Hr ltac:(lia) ltac:(lia)) as [Hlen Hbs]. split; [cbn; lia|].
    intros i Hi. destruct (Z.eq_dec i 0) as [->|Hi0].
    + rewrite Z.add_0_r. cbn. exact Hb.
    + replace (A + i) with (A + 1 + (i - 1)) by lia. rewrite Hbs by lia.
      replace (Z.to_nat i) with (S (Z.to_nat (i - 1))) by lia. reflexivity.
Qed.

Lemma Z_to_le_bytes_roundtrip : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes]. rewrite bytes_le_to_Z_cons.
  pose proof (byte_small b). pose proof (bytes_le_to_Z_nonneg bs). f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
    replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bv_unsigned b + bytes_le_to_Z bs * 256) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    replace ((bv_unsigned b + 256 * bytes_le_to_Z bs) / 256) with (bytes_le_to_Z bs); [exact IH|].
    symmetry. rewrite Z.add_comm, Z.mul_comm, Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
Qed.

Lemma store_bytes_of_load : forall w bs, length bs = Z.to_nat (to_Z w) -> wok w ->
  store_bytes w (ext_word false 0 (to_Z w) (le_bytes_to_word bs)) = bs.
Proof.
  intros w bs Hlen Hw. assert (Hw8 : 1 <= to_Z w <= 8) by (unfold wok in Hw; lia).
  unfold store_bytes, ext_word, le_bytes_to_word.
  pose proof (bytes_le_to_Z_bound bs) as Hbd. rewrite Hlen, Z2Nat.id in Hbd by lia.
  assert (Hlt : bytes_le_to_Z bs < two64).
  { eapply Z.lt_le_trans; [apply Hbd|]. unfold two64. change 18446744073709551616 with (2 ^ 64). apply Z.pow_le_mono_r; lia. }
  rewrite (Z_to_bv64_unsigned (bytes_le_to_Z bs)) by (unfold two64 in Hlt; lia).
  unfold ext_Z. change (2 ^ (8 * 0)) with 1. rewrite Z.div_1_r, Z.mod_small by lia.
  rewrite Z_to_bv64_unsigned by (unfold two64 in Hlt; lia). rewrite <- Hlen. apply Z_to_le_bytes_roundtrip.
Qed.

Lemma rb_mod : forall m a, rb segs m a = rb segs m (a mod two64).
Proof. intros m a. rewrite !rb_unfold, StepM.Z_to_bv64_mod. reflexivity. Qed.
Lemma wb_mod : forall m a, wb segs m a = wb segs m (a mod two64).
Proof. intros m a. unfold wb. rewrite StepM.Z_to_bv64_mod. reflexivity. Qed.

Lemma wokb_sound : forall w, wokb w = true -> wok w.
Proof.
  intros w H. unfold wokb in H. unfold wok.
  repeat (apply orb_prop in H; destruct H as [H|H]); apply Uint63.eqb_correct in H; subst w;
    [left | right; left | right; right; left | right; right; right]; reflexivity.
Qed.

Lemma remat1_sound : forall E st aw st' ms model,
  st_ok segs (OPS R) E st ms model -> s_ops st = [] -> (s_resv st = RNone \/ s_resv st = RUnk) ->
  remat1 segs st aw = Some st' ->
  st_ok segs (OPS R) E st' ms model /\ s_ops st' = [] /\ (s_resv st' = RNone \/ s_resv st' = RUnk) /\ s_priv st' = s_priv st
  /\ s_pc st' = s_pc st /\ s_rf st' = s_rf st /\ s_ff st' = s_ff st /\ s_facts st' = s_facts st /\ s_next st' = s_next st.
Proof.
  intros E st [a w] st' ms model HS Hops Hrv H. unfold remat1 in H. cbn [fst snd] in H.
  destruct (wokb w) eqn:Hwk; [|discriminate H]. cbn [negb] in H. pose proof (wokb_sound w Hwk) as Hw.
  destruct (do_load segs st (VL (wlit a)) w false) as [[v|]|] eqn:HL; try discriminate H.
  destruct (do_store segs st (VL (wlit a)) w v) as [st1|] eqn:HST; [|discriminate H]. injection H as <-.
  destruct (StepM.do_store_inv segs st _ w v st1 HST) as (k & o & r & key & Ha & Hr & Hk & CW & ->).
  cbn [addr_of] in Ha. injection Ha as <- <-.
  cbn [s_ops s_resv s_priv s_pc s_rf s_ff s_facts s_next].
  split; [| split; [exact Hops|]; split; [destruct Hrv as [Hrv|Hrv]; rewrite Hrv; cbn; auto | repeat split; reflexivity]].
  pose proof (so_zero _ _ _ _ _ _ HS) as Hz. pose proof (so_facts _ _ _ _ _ _ HS) as Hfs.
  assert (Hw8 : 1 <= to_Z w <= 8) by (unfold wok in Hw; lia).

  destruct (StepM.do_load_sound segs (OPS R) E st ms model (VL (wlit a)) w false v HS Hw HL) as (bs & Hlen & Hrd & Hv).

  destruct (can_write_sound segs (s_priv st) E (ms_mem ms) (s_facts st) 0%uint63 r key w Hfs Hz (so_reg _ _ _ _ _ _ HS _ _ Hr) Hw CW)
    as (CR & WB & SEGW).
  destruct (can_read_sound segs (s_priv st) E (ms_mem ms) (s_facts st) 0%uint63 r key w Hfs Hz (so_reg _ _ _ _ _ _ HS _ _ Hr) Hw CR)
    as (RA1 & RA2 & _ & _ & _).
  set (A := addrZ E 0%uint63 key) in *.
  pose proof (StepM.access_addr E (VL (wlit a)) 0%uint63 (wlit a) key A Hz eq_refl Hk eq_refl ltac:(lia) ltac:(lia)) as HA.
  rewrite HA in Hrd.
  destruct (ov_read_bytes_inv (ms_mem ms) A _ bs Hrd ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as [_ Hrb].

  assert (Hresv : resv_ok E (resv_after_store (s_facts st) (s_resv st) (VL (wlit a))) (ms_resv ms)).
  { pose proof (so_resv _ _ _ _ _ _ HS) as X. destruct Hrv as [Hrv|Hrv]; rewrite Hrv in X |- *; cbn [resv_after_store]; exact X. }
  destruct (StepM.store_sound segs (OPS R) E st ms model (VL (wlit a)) 0%uint63 (wlit a) r key w v _ (ms_resv ms) HS Hw eq_refl Hr Hk CW Hresv)
    as [SOK HS'].
  rewrite HA, Hv, (store_bytes_of_load w bs Hlen Hw) in HS'.

  assert (Hlen' : Z.of_nat (length bs) = to_Z w) by (rewrite Hlen, Z2Nat.id; lia).
  assert (EQm : forall x, 0 <= x < two64 -> rb segs (write_to_mem (ms_mem ms) (Z_to_bv 64 A) bs) x = rb segs (ms_mem ms) x
                                      /\ wb segs (write_to_mem (ms_mem ms) (Z_to_bv 64 A) bs) x = wb segs (ms_mem ms) x).
  { intros x Hx. destruct (Z_lt_ge_dec x A) as [L|G]; [| destruct (Z_lt_ge_dec x (A + to_Z w)) as [L2|G2]].
    - rewrite (rb_ext segs (ms_mem ms)), (wb_ext segs (ms_mem ms)); [auto| |]; apply write_to_mem_frame; lia.
    -
      replace x with (A + (x - A)) by lia.
      assert (W1 : write_to_mem (ms_mem ms) (Z_to_bv 64 A) bs (Z_to_bv 64 (A + (x - A))) = nth_error bs (Z.to_nat (x - A)))
        by (apply write_to_mem_in; lia).
      pose proof (Hrb (x - A) ltac:(lia)) as R1.
      destruct (nth_error bs (Z.to_nat (x - A))) as [b|] eqn:Hb.
      2:{ exfalso. apply nth_error_None in Hb. lia. }
      split.
      + rewrite rb_unfold, W1. symmetry. exact R1.
      + pose proof (WB (x - A) ltac:(lia)) as W2. fold A in W2.
        transitivity true; [| symmetry; exact W2]. unfold wb, wview. rewrite W1. reflexivity.
    - rewrite (rb_ext segs (ms_mem ms)), (wb_ext segs (ms_mem ms)); [auto| |]; apply write_to_mem_frame; lia. }
  assert (EQr : forall x, rb segs (write_to_mem (ms_mem ms) (Z_to_bv 64 A) bs) x = rb segs (ms_mem ms) x).
  { intros x. rewrite !(rb_mod _ x). apply (proj1 (EQm _ (Z.mod_pos_bound x two64 ltac:(unfold two64; lia)))). }
  assert (EQw : forall x, wb segs (write_to_mem (ms_mem ms) (Z_to_bv 64 A) bs) x = wb segs (ms_mem ms) x).
  { intros x. rewrite !(wb_mod _ x). apply (proj2 (EQm _ (Z.mod_pos_bound x two64 ltac:(unfold two64; lia)))). }
  apply (st_ok_mem_back E _ ms _ model HS' Hops (so_svc _ _ _ _ _ _ HS) EQr EQw (so_minv _ _ _ _ _ _ HS)).
Qed.

Lemma remat_sound : forall E rm st st' ms model,
  st_ok segs (OPS R) E st ms model -> s_ops st = [] -> (s_resv st = RNone \/ s_resv st = RUnk) ->
  remat segs st rm = Some st' ->
  st_ok segs (OPS R) E st' ms model /\ s_ops st' = [] /\ (s_resv st' = RNone \/ s_resv st' = RUnk) /\ s_priv st' = s_priv st
  /\ s_pc st' = s_pc st /\ s_rf st' = s_rf st /\ s_ff st' = s_ff st /\ s_facts st' = s_facts st /\ s_next st' = s_next st.
Proof.
  intros E rm. induction rm as [|aw rm IH]; intros st st' ms model HS Hops Hrv H; cbn [remat] in H.
  - injection H as <-. split; [exact HS|]. split; [exact Hops|]. split; [exact Hrv|]. repeat split; reflexivity.
  - destruct (remat1 segs st aw) as [st1|] eqn:H1; [|discriminate H].
    destruct (remat1_sound E st aw st1 ms model HS Hops Hrv H1) as (HS1 & Ho1 & Hr1 & Hp1 & Q1 & Q2 & Q3 & Q4 & Q5).
    destruct (IH st1 st' ms model HS1 Ho1 Hr1 H) as (HS' & Ho' & Hr' & Hp' & P1 & P2 & P3 & P4 & P5).
    split; [exact HS'|]. split; [exact Ho'|]. split; [exact Hr'|]. repeat split; congruence.
Qed.

Lemma prune_region_ok : forall priv E m k r ghi,
  region_ok segs priv E m k r -> region_ok segs priv E m k (prune_region r ghi).
Proof.
  intros priv E m k r ghi RO. destruct RO as [B RG V C CI BG].
  assert (FI : forall g gr, IMap.find g (rg_cells (prune_region r ghi)) = Some gr -> IMap.find g (rg_cells r) = Some gr).
  { intros g gr Hf. cbn [prune_region rg_cells] in Hf. apply imap_of_find_in in Hf. apply filter_In in Hf. destruct Hf as [Hin _].
    apply (proj1 (IMap.elements_spec g gr (rg_cells r) B)). exact Hin. }
  constructor.
  - cbn [prune_region rg_cells]. apply imap_of_bst.
  - exact RG.
  - exact V.
  - intros g gr Hg. exact (C g gr (FI g gr Hg)).
  - intros g gr c i Hg Hc Hi. exact (CI g gr c i (FI g gr Hg) Hc Hi).
  - intros o _ _ _. cbn [bg_byte prune_region rg_bg]. exact I.
Qed.

Lemma prune1_sound : forall E st ghi st' ms model,
  st_ok segs (OPS R) E st ms model -> prune1 st ghi = Some st' ->
  st_ok segs (OPS R) E st' ms model /\ s_ops st' = s_ops st /\ s_priv st' = s_priv st /\ s_resv st' = s_resv st.
Proof.
  intros E st ghi st' ms model HS H. unfold prune1 in H.
  destruct (IMap.find 1%uint63 (s_regs st)) as [r|] eqn:Hr; [|discriminate H]. injection H as <-.
  cbn [setregs s_ops s_priv s_resv]. split; [| repeat split; reflexivity].
  destruct HS as [Hpc Hx0 Hregs Hfregs Hsvc Hresv Hfcsr Hrom Hz Hbst Hreg Hdisj Hpub Hfacts Hop Hapart Hmf Hcov Hminv].
  assert (Hlo : rg_lo (prune_region r ghi) = rg_lo r) by reflexivity.
  assert (Hhi : rg_hi (prune_region r ghi) = rg_hi r) by reflexivity.
  constructor; cbn [setregs s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]; try assumption.
  - apply IMap.add_bst. exact Hbst.
  - intros k r1 Hk. destruct (StepM.find_add_cases E (s_regs st) 1%uint63 r (prune_region r ghi) Hbst Hr Hlo Hhi k r1 Hk) as (r0 & G & _ & _ & [[-> ->]|[_ ->]]).
    + rewrite Hr in G. injection G as <-. apply prune_region_ok. exact (Hreg _ _ Hr).
    + exact (Hreg _ _ G).
  - apply (StepM.same_range_disjoint E (s_regs st) 1%uint63 r (prune_region r ghi) Hbst Hr Hlo Hhi eq_refl Hdisj).
  - intros r0 g gr c H0 Hg Hc i Hi. rewrite IMap.find_add_other in H0 by (exact Hbst || (intros X; discriminate X)).
    exact (Hpub r0 g gr c H0 Hg Hc i Hi).
  - unfold ops_apart in *. apply Forall_forall. intros o Ho a Ha.
    destruct (proj1 (Forall_forall _ _) Hapart o Ho a Ha) as [NB PR]. split; [|exact PR].
    intros HB. apply NB. exact (StepM.same_range_in_based E (s_regs st) 1%uint63 r (prune_region r ghi) Hbst Hr Hlo Hhi a HB).
  -
    intros a [B|S]; apply Hcov; [left; exact (StepM.same_range_in_based E (s_regs st) 1%uint63 r (prune_region r ghi) Hbst Hr Hlo Hhi a B) | right; exact S].
Qed.

Lemma region_ok_priv : forall priv E m k r,
  (PrimInt63.eqb k 0%uint63 = true -> forall g gr c i, IMap.find g (rg_cells r) = Some gr -> In c (g_cells gr) -> 0 <= i < to_Z (c_w c) ->
     ~ in_priv priv (8 * keyZ g + to_Z (c_idx c) + i)) ->
  region_ok segs [] E m k r -> region_ok segs priv E m k r.
Proof.
  intros priv E m k r Hcells RO. destruct RO as [B RG V C CI BG]. constructor; try assumption.
  - intros g gr c i Hg Hc Hi. destruct (CI g gr c i Hg Hc Hi) as [X Y]. split; [exact X|].
    intros K. destruct (Y K) as (Y1 & Y2 & _). split; [exact Y1|]. split; [exact Y2|]. exact (Hcells K g gr c i Hg Hc Hi).
  - intros o H1 H2 H3. apply (BG o H1); [|exact H3]. intros K. destruct (H2 K) as (X1 & X2 & X3). split; [exact X1|]. split; [exact X2|].
    intros Hin. unfold in_priv in Hin. apply Exists_exists in Hin. destruct Hin as (iv & Hiv & _). destruct Hiv.
Qed.

Lemma with_ops_priv_sound : forall E st ops priv st' ms model,
  st_ok segs (OPS R) E st ms model -> with_ops_priv st ops priv = Some st' ->
  ops_hold (OPS R) E ops (ms_mem ms) model ->
  ops_apart segs (OPS R) E ops (s_regs st) priv ->
  abs_cells_public priv (s_regs st) ->
  st_ok segs (OPS R) E st' ms model.
Proof.
  intros E st ops priv st' ms model HS H Hops Hapart Hpub. unfold with_ops_priv in H.
  destruct (s_ops st) eqn:Eo; [|discriminate H]. destruct (s_priv st) eqn:Ep; [|discriminate H]. injection H as <-.
  destruct HS as [Hpc Hx0 Hregs Hfregs Hsvc Hresv Hfcsr Hrom Hz Hbst Hreg Hdisj Hpub0 Hfacts Hop Hapart0 Hmf Hcov Hminv].
  rewrite Ep in Hreg.
  constructor; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]; try assumption.
  - intros k r Hk. apply region_ok_priv; [|exact (Hreg k r Hk)].
    intros K g gr c i Hg Hc Hi. apply Uint63.eqb_correct in K. subst k. exact (Hpub r g gr c Hk Hg Hc i Hi).
  -
    intros a Ha. apply (op_cov_mono (OPS R) (insts E []) _ a); [intros o []|]. rewrite <- Eo. exact (Hcov a Ha).
Qed.

Theorem drv_bridge : forall rm ghi ops priv (M D : sstate) E ms model,
  drv_of_main segs rm ghi ops priv M = Some D ->
  st_ok segs (OPS R) E M ms model -> s_ops M = [] -> (s_resv M = RNone \/ s_resv M = RUnk) ->
  ops_hold (OPS R) E ops (ms_mem ms) model ->
  ops_apart segs (OPS R) E ops (s_regs D) priv ->
  abs_cells_public priv (s_regs D) ->
  st_ok segs (OPS R) E D ms model.
Proof.
  intros rm ghi ops priv M D E ms model H HS Hops0 Hrv Hops Hapart Hpub. unfold drv_of_main in H.
  destruct (remat segs M rm) as [st1|] eqn:H1; [|discriminate H].
  destruct (prune1 st1 ghi) as [st2|] eqn:H2; [|discriminate H].
  destruct (remat_sound E rm M st1 ms model HS Hops0 Hrv H1) as (HS1 & _).
  destruct (prune1_sound E st1 ghi st2 ms model HS1 H2) as (HS2 & _).
  assert (Hregs : s_regs D = s_regs st2).
  { unfold with_ops_priv in H. destruct (s_ops st2); [|discriminate H]. destruct (s_priv st2); [|discriminate H].
    injection H as <-. reflexivity. }
  rewrite Hregs in Hapart, Hpub.
  exact (with_ops_priv_sound E st2 ops priv D ms model HS2 H Hops Hapart Hpub).
Qed.

Definition cells_public_b (priv : list (int * int)) (R0 : IMap.t region) : bool :=
  match IMap.find 0%uint63 R0 with
  | None => true
  | Some r => IMap.forallb (fun g gr => forallb (fun c => negb (in_priv_b priv (PrimInt63.add (PrimInt63.lsl g 3%uint63) (c_idx c)) (c_w c))
                                                  && PrimInt63.ltb g (PrimInt63.lsl 1%uint63 59%uint63))%bool (g_cells gr)) (rg_cells r)
  end.

End Run.
End DrvLib.
