(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Frame Step Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull Restrict.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.  (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record chunkP := CP { cp_class : Z; cp_idx : Z }.
(* [comment removed for export] *)
Record chunkS := CS { cs_map : Z; cs_n : Z }.
Inductive chunk := ChP (p : chunkP) | ChS (s : chunkS).

Definition chunkS_eq_dec : forall x y : chunkS, {x = y} + {x <> y}.
Proof. intros [a b] [c d]. destruct (Z.eq_dec a c); destruct (Z.eq_dec b d); try (left; congruence); right; congruence. Defined.
Definition chunk_eq_dec : forall x y : chunk, {x = y} + {x <> y}.
Proof. intros [[a b]|[a b]] [[c d]|[c d]]; try (right; discriminate);
  destruct (Z.eq_dec a c); destruct (Z.eq_dec b d); try (left; congruence); right; congruence.
Defined.

Section Geometry.
  Context (sb : Z).   (* [comment removed for export] *)

  Definition alloc_beg (ch : chunk) : Z :=
    match ch with ChP (CP c k) => chunk_addr sb c k | ChS (CS mb _) => sec_alloc_beg mb end.
  (* [comment removed for export] *)
  Definition user_of (ch : chunk) (n : Z) : Z :=
    match ch with ChP p => user_beg (alloc_beg ch) n | ChS (CS mb _) => sec_user_beg mb end.
  Definition hdr_of (ch : chunk) (n : Z) : Z := user_of ch n - kChunkHeaderSize.
  (* [comment removed for export] *)
  Definition chunk_lo (ch : chunk) : Z := match ch with ChP _ => alloc_beg ch | ChS (CS mb _) => mb end.
  Definition chunk_hi (ch : chunk) : Z :=
    match ch with ChP (CP c k) => chunk_addr sb c k + class_size c | ChS (CS mb n) => mb + map_size n end.
End Geometry.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record liveinfo := LI { li_chunk : chunk; li_n : Z }.
(* [comment removed for export] *)
Record qentry := QE { qe_chunk : chunk; qe_n : Z }.
(* [comment removed for export] *)
Record batch := BA { ba_idx : Z; ba_entries : list qentry }.
(* [comment removed for export] *)
Record region := RG { rg_mapped_user : Z; rg_allocated_user : Z; rg_mapped_fa : Z; rg_free : list Z }.
Definition region_zero : region := RG 0 0 0 [].
(* [comment removed for export] *)
Record pcache := PCc { pk_chunks : list Z }.
(* [comment removed for export] *)
Record secreg := SR { sr_chunks : list chunkS; sr_reserved : Z }.
(* [comment removed for export] *)
Record fframe := FF { ff_class : Z; ff_age : nat }.

(* [comment removed for export] *)
Record aplace := mkP {
  p_b6 : Z;          (* [comment removed for export] *)
  p_pa : Z;          (* [comment removed for export] *)
  p_thr : Z;         (* [comment removed for export] *)
  p_ctx : Z;         (* [comment removed for export] *)
  p_nodes0 : Z;      (* [comment removed for export] *)
  p_frames0 : Z;     (* [comment removed for export] *)
  p_fs : Z;          (* [comment removed for export] *)
  p_itab : Z;        (* [comment removed for export] *)
  p_m64k : Z;        (* [comment removed for export] *)
  p_gvec : Z;        (* [comment removed for export] *)
  p_dvec : Z;        (* [comment removed for export] *)
  p_m11 : Z;         (* [comment removed for export] *)
  p_dtls : Z;        (* [comment removed for export] *)
  p_tlsb : Z;        (* [comment removed for export] *)
  p_tlse : Z;
  p_sp0 : Z;         (* [comment removed for export] *)
  p_stk_span : Z;    (* [comment removed for export] *)
  p_stk_top : Z;     (* [comment removed for export] *)
  p_stk_bot : Z;     (* [comment removed for export] *)
  p_eager0 : Z;      (* [comment removed for export] *)
  p_brk : Z;         (* [comment removed for export] *)
  p_dkeys : list (list Z); (* [comment removed for export] *)
  p_extra : list (Z * Z); (* [comment removed for export] *)
  p_tlim : Z         (* [comment removed for export] *)
}.
Definition p_sb (P : aplace) : Z := space_beg_of (p_b6 P).
Definition p_ri (P : aplace) : Z := p_sb P + kSpaceSize.               (* [comment removed for export] *)

(* [comment removed for export] *)
Record AState := mkA {
  a_pl : aplace;
  (* [comment removed for export] *)
  a_reg : Z -> region;          (* [comment removed for export] *)
  a_cache_inited : bool;        (* [comment removed for export] *)
  a_cache : Z -> pcache;        (* [comment removed for export] *)
  (* [comment removed for export] *)
  a_livemap : gmap Z liveinfo;  (* [comment removed for export] *)
  a_qthread : list batch;       (* [comment removed for export] *)
  a_qglobal : list batch;       (* [comment removed for export] *)
  (* [comment removed for export] *)
  a_sec : secreg;
  (* [comment removed for export] *)
  a_depot : list (list Z);
  (* [comment removed for export] *)
  a_fhint : Z -> Z;             (* [comment removed for export] *)
  a_fframes : gmap Z fframe;    (* [comment removed for export] *)
  (* [comment removed for export] *)
  a_ia_inited : bool;           (* [comment removed for export] *)
  a_oom : bool;                 (* [comment removed for export] *)
  a_tiny : Z;                   (* [comment removed for export] *)
  (* [comment removed for export] *)
  a_qlimbo : list batch;        (* [comment removed for export] *)
  a_scred : Z;                (* [comment removed for export] *)
  a_deadsh : list (Z * Z);      (* [comment removed for export] *)
  (* [comment removed for export] *)
  a_pcred : Z;                  (* [comment removed for export] *)
  a_paid : Z -> list Z          (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Definition a_b6 (A : AState) : Z := p_b6 (a_pl A).
Definition a_pa (A : AState) : Z := p_pa (a_pl A).
Definition a_thr (A : AState) : Z := p_thr (a_pl A).
Definition a_ctx (A : AState) : Z := p_ctx (a_pl A).
Definition a_nodes0 (A : AState) : Z := p_nodes0 (a_pl A).
Definition a_frames0 (A : AState) : Z := p_frames0 (a_pl A).
Definition a_fs (A : AState) : Z := p_fs (a_pl A).
Definition a_itab (A : AState) : Z := p_itab (a_pl A).
Definition a_m64k (A : AState) : Z := p_m64k (a_pl A).
Definition a_sp0 (A : AState) : Z := p_sp0 (a_pl A).
Definition a_sb (A : AState) : Z := p_sb (a_pl A).
Definition a_ri (A : AState) : Z := p_ri (a_pl A).

(* [comment removed for export] *)
Definition set_reg (A : AState) (r : Z -> region) : AState :=
  mkA (a_pl A) r (a_cache_inited A) (a_cache A) (a_livemap A) (a_qthread A) (a_qglobal A) (a_sec A) (a_depot A)
      (a_fhint A) (a_fframes A) (a_ia_inited A) (a_oom A) (a_tiny A) (a_qlimbo A) (a_scred A) (a_deadsh A) (a_pcred A) (a_paid A).
Definition set_cache_inited (A : AState) (b : bool) : AState :=
  mkA (a_pl A) (a_reg A) b (a_cache A) (a_livemap A) (a_qthread A) (a_qglobal A) (a_sec A) (a_depot A)
      (a_fhint A) (a_fframes A) (a_ia_inited A) (a_oom A) (a_tiny A) (a_qlimbo A) (a_scred A) (a_deadsh A) (a_pcred A) (a_paid A).
Definition set_cache (A : AState) (k : Z -> pcache) : AState :=
  mkA (a_pl A) (a_reg A) (a_cache_inited A) k (a_livemap A) (a_qthread A) (a_qglobal A) (a_sec A) (a_depot A)
      (a_fhint A) (a_fframes A) (a_ia_inited A) (a_oom A) (a_tiny A) (a_qlimbo A) (a_scred A) (a_deadsh A) (a_pcred A) (a_paid A).
Definition set_livemap (A : AState) (lm : gmap Z liveinfo) : AState :=
  mkA (a_pl A) (a_reg A) (a_cache_inited A) (a_cache A) lm (a_qthread A) (a_qglobal A) (a_sec A) (a_depot A)
      (a_fhint A) (a_fframes A) (a_ia_inited A) (a_oom A) (a_tiny A) (a_qlimbo A) (a_scred A) (a_deadsh A) (a_pcred A) (a_paid A).
Definition set_qthread (A : AState) (q : list batch) : AState :=
  mkA (a_pl A) (a_reg A) (a_cache_inited A) (a_cache A) (a_livemap A) q (a_qglobal A) (a_sec A) (a_depot A)
      (a_fhint A) (a_fframes A) (a_ia_inited A) (a_oom A) (a_tiny A) (a_qlimbo A) (a_scred A) (a_deadsh A) (a_pcred A) (a_paid A).
Definition set_qglobal (A : AState) (q : list batch) : AState :=
  mkA (a_pl A) (a_reg A) (a_cache_inited A) (a_cache A) (a_livemap A) (a_qthread A) q (a_sec A) (a_depot A)
      (a_fhint A) (a_fframes A) (a_ia_inited A) (a_oom A) (a_tiny A) (a_qlimbo A) (a_scred A) (a_deadsh A) (a_pcred A) (a_paid A).
Definition set_sec (A : AState) (x : secreg) : AState :=
  mkA (a_pl A) (a_reg A) (a_cache_inited A) (a_cache A) (a_livemap A) (a_qthread A) (a_qglobal A) x (a_depot A)
      (a_fhint A) (a_fframes A) (a_ia_inited A) (a_oom A) (a_tiny A) (a_qlimbo A) (a_scred A) (a_deadsh A) (a_pcred A) (a_paid A).
Definition set_depot (A : AState) (D : list (list Z)) : AState :=
  mkA (a_pl A) (a_reg A) (a_cache_inited A) (a_cache A) (a_livemap A) (a_qthread A) (a_qglobal A) (a_sec A) D
      (a_fhint A) (a_fframes A) (a_ia_inited A) (a_oom A) (a_tiny A) (a_qlimbo A) (a_scred A) (a_deadsh A) (a_pcred A) (a_paid A).
Definition set_fhint (A : AState) (h : Z -> Z) : AState :=
  mkA (a_pl A) (a_reg A) (a_cache_inited A) (a_cache A) (a_livemap A) (a_qthread A) (a_qglobal A) (a_sec A) (a_depot A)
      h (a_fframes A) (a_ia_inited A) (a_oom A) (a_tiny A) (a_qlimbo A) (a_scred A) (a_deadsh A) (a_pcred A) (a_paid A).
Definition set_fframes (A : AState) (g : gmap Z fframe) : AState :=
  mkA (a_pl A) (a_reg A) (a_cache_inited A) (a_cache A) (a_livemap A) (a_qthread A) (a_qglobal A) (a_sec A) (a_depot A)
      (a_fhint A) g (a_ia_inited A) (a_oom A) (a_tiny A) (a_qlimbo A) (a_scred A) (a_deadsh A) (a_pcred A) (a_paid A).
Definition set_ia (A : AState) (b : bool) : AState :=
  mkA (a_pl A) (a_reg A) (a_cache_inited A) (a_cache A) (a_livemap A) (a_qthread A) (a_qglobal A) (a_sec A) (a_depot A)
      (a_fhint A) (a_fframes A) b (a_oom A) (a_tiny A) (a_qlimbo A) (a_scred A) (a_deadsh A) (a_pcred A) (a_paid A).
Definition set_oom (A : AState) (b : bool) : AState :=
  mkA (a_pl A) (a_reg A) (a_cache_inited A) (a_cache A) (a_livemap A) (a_qthread A) (a_qglobal A) (a_sec A) (a_depot A)
      (a_fhint A) (a_fframes A) (a_ia_inited A) b (a_tiny A) (a_qlimbo A) (a_scred A) (a_deadsh A) (a_pcred A) (a_paid A).
Definition set_tiny (A : AState) (t : Z) : AState :=
  mkA (a_pl A) (a_reg A) (a_cache_inited A) (a_cache A) (a_livemap A) (a_qthread A) (a_qglobal A) (a_sec A) (a_depot A)
      (a_fhint A) (a_fframes A) (a_ia_inited A) (a_oom A) t (a_qlimbo A) (a_scred A) (a_deadsh A) (a_pcred A) (a_paid A).
Definition set_qlimbo (A : AState) (q : list batch) : AState :=
  mkA (a_pl A) (a_reg A) (a_cache_inited A) (a_cache A) (a_livemap A) (a_qthread A) (a_qglobal A) (a_sec A) (a_depot A)
      (a_fhint A) (a_fframes A) (a_ia_inited A) (a_oom A) (a_tiny A) q (a_scred A) (a_deadsh A) (a_pcred A) (a_paid A).
Definition set_scred (A : AState) (c : Z) : AState :=
  mkA (a_pl A) (a_reg A) (a_cache_inited A) (a_cache A) (a_livemap A) (a_qthread A) (a_qglobal A) (a_sec A) (a_depot A)
      (a_fhint A) (a_fframes A) (a_ia_inited A) (a_oom A) (a_tiny A) (a_qlimbo A) c (a_deadsh A) (a_pcred A) (a_paid A).
Definition set_deadsh (A : AState) (d : list (Z * Z)) : AState :=
  mkA (a_pl A) (a_reg A) (a_cache_inited A) (a_cache A) (a_livemap A) (a_qthread A) (a_qglobal A) (a_sec A) (a_depot A)
      (a_fhint A) (a_fframes A) (a_ia_inited A) (a_oom A) (a_tiny A) (a_qlimbo A) (a_scred A) d (a_pcred A) (a_paid A).
Definition set_pcred (A : AState) (c : Z) : AState :=   (* [comment removed for export] *)
  mkA (a_pl A) (a_reg A) (a_cache_inited A) (a_cache A) (a_livemap A) (a_qthread A) (a_qglobal A) (a_sec A) (a_depot A)
      (a_fhint A) (a_fframes A) (a_ia_inited A) (a_oom A) (a_tiny A) (a_qlimbo A) (a_scred A) (a_deadsh A) c (a_paid A).
Definition set_paid (A : AState) (pd : Z -> list Z) : AState :=   (* [comment removed for export] *)
  mkA (a_pl A) (a_reg A) (a_cache_inited A) (a_cache A) (a_livemap A) (a_qthread A) (a_qglobal A) (a_sec A) (a_depot A)
      (a_fhint A) (a_fframes A) (a_ia_inited A) (a_oom A) (a_tiny A) (a_qlimbo A) (a_scred A) (a_deadsh A) (a_pcred A) pd.
(* [comment removed for export] *)
Definition paid_add (paid : Z -> list Z) (c k : Z) : Z -> list Z := fun c' => if Z.eqb c' c then k :: paid c else paid c'.
Lemma paid_add_eq : forall paid c k, paid_add paid c k c = k :: paid c.
Proof. intros. unfold paid_add. rewrite Z.eqb_refl. reflexivity. Qed.
Lemma paid_add_ne : forall paid c k c', c' <> c -> paid_add paid c k c' = paid c'.
Proof. intros paid c k c' H. unfold paid_add. destruct (Z.eqb_spec c' c); [contradiction| reflexivity]. Qed.
Lemma paid_add_incl : forall paid c k c' x, In x (paid c') -> In x (paid_add paid c k c').
Proof. intros paid c k c' x H. unfold paid_add. destruct (Z.eqb_spec c' c) as [->|]; [right|]; exact H. Qed.
(* [comment removed for export] *)
Ltac asimp := cbn [a_pl a_reg a_cache_inited a_cache a_livemap a_qthread a_qglobal a_sec a_depot a_fhint a_fframes a_ia_inited a_oom a_tiny
                   a_qlimbo a_scred a_deadsh a_pcred a_paid
                   set_reg set_cache_inited set_cache set_livemap set_qthread set_qglobal set_sec set_depot set_fhint set_fframes
                   set_ia set_oom set_tiny set_qlimbo set_scred set_deadsh set_pcred set_paid].
Tactic Notation "asimp" "in" hyp(H) :=
  cbn [a_pl a_reg a_cache_inited a_cache a_livemap a_qthread a_qglobal a_sec a_depot a_fhint a_fframes a_ia_inited a_oom a_tiny
       a_qlimbo a_scred a_deadsh a_pcred a_paid
       set_reg set_cache_inited set_cache set_livemap set_qthread set_qglobal set_sec set_depot set_fhint set_fframes
       set_ia set_oom set_tiny set_qlimbo set_scred set_deadsh set_pcred set_paid] in H.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition as_live_ (lm : gmap Z liveinfo) (p : Z) : option Z := option_map li_n (lm !! p).
Definition as_fframe_ (ffs : gmap Z fframe) (ff : Z) : option (Z * nat) :=
  option_map (fun f => (ff_class f, ff_age f)) (ffs !! ff).
Definition as_livebytes_ (lm : gmap Z liveinfo) : Z := map_fold (fun _ li acc => li_n li + acc) 0 lm.
Definition as_live (A : AState) : Z -> option Z := as_live_ (a_livemap A).
Definition as_fframe (A : AState) : Z -> option (Z * nat) := as_fframe_ (a_fframes A).
Definition as_release (A : AState) (ff : Z) : AState := set_fframes A (delete ff (a_fframes A)).
Definition as_tinycred (A : AState) : Z := a_tiny A.
Definition as_seccred (A : AState) : Z := a_scred A.       (* [comment removed for export] *)
Definition as_primcred (A : AState) : Z := a_pcred A.      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition as_nlive_ (lm : gmap Z liveinfo) : Z := Z.of_nat (size lm).
Definition as_nlive (A : AState) : Z := as_nlive_ (a_livemap A).
Definition is_tiny (n : Z) : Z := if Z.ltb n 16 then 1 else 0.
Definition tiny_live_ (lm : gmap Z liveinfo) : Z := map_fold (fun _ li acc => is_tiny (li_n li) + acc) 0 lm.
Definition as_livebytes (A : AState) : Z := as_livebytes_ (a_livemap A).

(* [comment removed for export] *)
Definition qe_bytes (e : qentry) : Z := user_size (qe_n e).
Definition batch_bytes (b : batch) : Z := kQuarantineBatchBytes + fold_right (fun e acc => qe_bytes e + acc) 0 (ba_entries b).
Definition q_bytes (bs : list batch) : Z := fold_right (fun b acc => batch_bytes b + acc) 0 bs.
Definition batch_addr (sb : Z) (b : batch) : Z := chunk_addr sb kQuarantineBatchClass (ba_idx b).
Definition q_entries (bs : list batch) : list qentry := flat_map ba_entries bs.
Definition quarantined_chunks_ (qt qg : list batch) : list chunk := map qe_chunk (q_entries (qt ++ qg)).
Definition quarantined_chunks (A : AState) : list chunk := quarantined_chunks_ (a_qthread A) (a_qglobal A).

(* [comment removed for export] *)
Definition carved_count_ (reg : Z -> region) (c : Z) : Z := rg_allocated_user (reg c) / class_size c.
Definition carved_count (A : AState) : Z -> Z := carved_count_ (a_reg A).
Definition batch_indices_ (qt qg : list batch) : list Z := map ba_idx (qt ++ qg).
Definition batch_indices (A : AState) : list Z := batch_indices_ (a_qthread A) (a_qglobal A).

(* [comment removed for export] *)
Fixpoint index_of (x : Z) (l : list chunkS) : option nat :=
  match l with [] => None | CS mb n :: l' => if Z.eqb mb x then Some 0%nat else option_map S (index_of x l') end.

(* [comment removed for export] *)
Fixpoint key_index (k : list Z) (ks : list (list Z)) : option nat :=
  match ks with [] => None | k' :: ks' => if list_eq_dec Z.eq_dec k k' then Some 0%nat else option_map S (key_index k ks') end.
Definition depot_id_ (D : list (list Z)) (k : list Z) : option Z := option_map (fun i => Z.of_nat i + 1) (key_index k D).
Definition depot_n_ (D : list (list Z)) : Z := Z.of_nat (length D).
(* [comment removed for export] *)
Definition depot_frames_ (D : list (list Z)) : Z := fold_right (fun k acc => 1 + Z.of_nat (length k) + acc) 0 D.
(* [comment removed for export] *)
Definition depot_put_ (D : list (list Z)) (k : list Z) : list (list Z) :=
  match key_index k D with Some _ => D | None => D ++ [k] end.
Definition depot_id (A : AState) : list Z -> option Z := depot_id_ (a_depot A).
Definition depot_n (A : AState) : Z := depot_n_ (a_depot A).
Definition depot_frames (A : AState) : Z := depot_frames_ (a_depot A).

(* [comment removed for export] *)
Definition kFakeStackSizeLog : Z := 20.
Definition kFakeFlagsOffset : Z := 4096.
Definition kFakeFlagsBytes : Z := 2 ^ 15.                    (* [comment removed for export] *)
Definition kFakeFramesOffset : Z := 4096 + 2 ^ 15.
Definition kFakeStackBytes : Z := 4096 + 2 ^ 15 + 11 * 2 ^ 20.  (* [comment removed for export] *)
Definition fflags_off (k : Z) : Z := 2 ^ 15 - 2 ^ (15 - k).   (* [comment removed for export] *)
Definition fflag_addr (fs k pos : Z) : Z := fs + kFakeFlagsOffset + fflags_off k + pos.
Definition fframe_addr (fs k pos : Z) : Z := fs + kFakeFramesOffset + 2 ^ kFakeStackSizeLog * k + fsize k * pos.
(* [comment removed for export] *)
Definition ff_pos (h : Z) (k : Z) (age : nat) : Z := (h - 1 - Z.of_nat age) mod fslots k.
Definition ff_addr_of_ (fs : Z) (fhint : Z -> Z) (k : Z) (age : nat) : Z := fframe_addr fs k (ff_pos (fhint k) k age).
Definition saved_flag_ptr (ff k : Z) : Z := ff + fsize k - 8.
(* [comment removed for export] *)
Lemma kFakeFramesOffset_val : kFakeFramesOffset = 36864. Proof. reflexivity. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition shadow_region (b s : Z) : Z * Z :=
  let lo := round_down (sh b) 8 in
  let hi := round_up (sh (b + s - 1) + 1) 8 in (lo, hi - lo).
(* [comment removed for export] *)
Section StackBand.
Context {Clg : Ceiling}.
(* [comment removed for export] *)
Definition app_rangeA (L : alayout) (p n : Z) : Prop :=
  (4096 <= p /\ 0 <= n /\ p + n <= kLowShadowMapBeg /\ (p + n <= al_image_lo L \/ al_image_hi L <= p))
  \/ (kHighMemBeg <= p /\ 0 <= n /\ p + n <= alloc_ceiling).
Definition stack_band_iv : Z * Z := (alloc_ceiling, 2^47 - alloc_ceiling).
Definition stack_shadow_iv : Z * Z := shadow_region alloc_ceiling (2^47 - alloc_ceiling).
(* [comment removed for export] *)
Lemma app_rangeA_sub : forall L p n p' n', app_rangeA L p n -> p <= p' -> 0 <= n' -> p' + n' <= p + n -> app_rangeA L p' n'.
Proof. unfold app_rangeA. intros. lia. Qed.
Lemma app_rangeA_hi : forall L p n, kHighMemBeg <= p -> 0 <= n -> p + n <= alloc_ceiling -> app_rangeA L p n.
Proof. unfold app_rangeA. intros. right. lia. Qed.
Lemma app_rangeA_arith : forall L p n, app_rangeA L p n ->
  4096 <= p /\ 0 <= n /\ p + n <= alloc_ceiling /\ (p + n <= al_image_lo L \/ al_image_hi L <= p \/ kHighMemBeg <= p) /\
  (p + n <= kLowShadowMapBeg \/ kHighMemBeg <= p).
Proof. intros L p n H. pose proof alloc_ceiling_val. unfold app_rangeA, kLowShadowMapBeg, kHighMemBeg in *. lia. Qed.
End StackBand.

Section Hulls.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context (pa_image_ivs : hull) (L : alayout).

  (* [comment removed for export] *)
  Definition class_regions_ (sb : Z) (R : region) (c : Z) : list (Z * Z) :=
    let rb := region_beg sb c in
    (if rg_mapped_user R =? 0 then [] else [(rb, rg_mapped_user R); shadow_region rb (rg_mapped_user R)]) ++
    (if rg_mapped_fa R =? 0 then [] else [(rb + kFreeArrayOffset, rg_mapped_fa R); shadow_region (rb + kFreeArrayOffset) (rg_mapped_fa R)]).
  Fixpoint classes_regions_ (sb : Z) (reg : Z -> region) (n : nat) : list (Z * Z) :=
    match n with O => [] | S n' => classes_regions_ sb reg n' ++ class_regions_ sb (reg (Z.of_nat n)) (Z.of_nat n) end.
  Definition sec_regions_ (chunks : list chunkS) : list (Z * Z) :=
    flat_map (fun s => [(cs_map s, map_size (cs_n s)); shadow_region (cs_map s) (map_size (cs_n s))]) chunks.

  (* [comment removed for export] *)
  Definition fixed_regions_ (P : aplace) : list (Z * Z) :=
    [ (* [comment removed for export] *)
      (p_sp0 P - 0x800000, 0x800000 + p_stk_span P);
      stack_shadow_iv;
      (* [comment removed for export] *)
      shadow_region (al_image_lo L) (al_image_hi L - al_image_lo L);
      (* [comment removed for export] *)
      (p_thr P, 4096); (p_ctx P, 0x10000); (p_ri P, 4096);
      (* [comment removed for export] *)
      (p_fs P, kFakeStackBytes); shadow_region (p_fs P) kFakeStackBytes;
      (* [comment removed for export] *)
      (p_nodes0 P, kDepotNodesBlock); (p_frames0 P, kStackStoreBlockBytes); (p_pa P, 8 * kChunksBlockCount);
      (* [comment removed for export] *)
      (p_itab P, 0x38e000); (p_m64k P, 0x10000); (p_dtls P, 4096);
      (* [comment removed for export] *)
      shadow_region (p_gvec P) 4096; shadow_region (p_dvec P) 4096; shadow_region (p_m11 P) 4096;
      shadow_region (p_thr P) 4096; shadow_region (p_ctx P) 0x10000; shadow_region (p_dtls P) 4096;
      shadow_region (p_ri P) 4096; shadow_region (p_nodes0 P) kDepotNodesBlock;
      shadow_region (p_frames0 P) kStackStoreBlockBytes; shadow_region (p_itab P) 0x38e000;
      shadow_region (p_m64k P) 0x10000 ].

  Definition aregions_ (P : aplace) (reg : Z -> region) (sec : secreg) : list (Z * Z) :=
    fixed_regions_ P ++ classes_regions_ (p_sb P) reg 31 ++ sec_regions_ (sr_chunks sec).
  Definition ahull_of_ (P : aplace) (reg : Z -> region) (sec : secreg) (dead : list (Z * Z)) : hull :=
    pa_image_ivs ++ hull_of (aregions_ P reg sec) ++ dead ++ p_extra P.
      (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition lfixed_regions_ (P : aplace) : list (Z * Z) :=
    [ stack_shadow_iv;
      shadow_region (al_image_lo L) (al_image_hi L - al_image_lo L);
      (p_thr P, 4096); (p_ctx P, 0x10000); (p_ri P, 4096);
      (p_fs P, kFakeStackBytes); shadow_region (p_fs P) kFakeStackBytes;
      (p_nodes0 P, kDepotNodesBlock); (p_frames0 P, kStackStoreBlockBytes); (p_pa P, 8 * kChunksBlockCount);
      (p_itab P, 0x38e000); (p_m64k P, 0x10000); (p_dtls P, 4096);
      shadow_region (p_gvec P) 4096; shadow_region (p_dvec P) 4096; shadow_region (p_m11 P) 4096;
      shadow_region (p_thr P) 4096; shadow_region (p_ctx P) 0x10000; shadow_region (p_dtls P) 4096;
      shadow_region (p_ri P) 4096; shadow_region (p_nodes0 P) kDepotNodesBlock;
      shadow_region (p_frames0 P) kStackStoreBlockBytes; shadow_region (p_itab P) 0x38e000;
      shadow_region (p_m64k P) 0x10000 ].
  Lemma fixed_regions_split : forall P, fixed_regions_ P = (p_sp0 P - 0x800000, 0x800000 + p_stk_span P) :: lfixed_regions_ P.
  Proof. reflexivity. Qed.
  Definition lclass_regions_ (sb : Z) (R : region) (c : Z) : list (Z * Z) :=
    let rb := region_beg sb c in
    (if rg_mapped_user R =? 0 then [] else [shadow_region rb (rg_mapped_user R)]) ++
    (if rg_mapped_fa R =? 0 then [] else [shadow_region (rb + kFreeArrayOffset) (rg_mapped_fa R)]).
  Fixpoint lclasses_regions_ (sb : Z) (reg : Z -> region) (n : nat) : list (Z * Z) :=
    match n with O => [] | S n' => lclasses_regions_ sb reg n' ++ lclass_regions_ sb (reg (Z.of_nat n)) (Z.of_nat n) end.
  Definition lsec_regions_ (chunks : list chunkS) : list (Z * Z) :=
    map (fun s => shadow_region (cs_map s) (map_size (cs_n s))) chunks.
  Definition alregions_ (P : aplace) (reg : Z -> region) (sec : secreg) : list (Z * Z) :=
    lfixed_regions_ P ++ lclasses_regions_ (p_sb P) reg 31 ++ lsec_regions_ (sr_chunks sec).
  Definition alhull_of_ (P : aplace) (reg : Z -> region) (sec : secreg) (dead : list (Z * Z)) : hull :=
    hull_of (alregions_ P reg sec) ++ dead ++ p_extra P.

  (* [comment removed for export] *)
  Fixpoint classes_eager_ (reg : Z -> region) (n : nat) : Z :=
    match n with O => 0 | S n' => classes_eager_ reg n' + rg_mapped_user (reg (Z.of_nat n)) + rg_mapped_fa (reg (Z.of_nat n)) end.
  Definition sec_eager_ (chunks : list chunkS) : Z := fold_right (fun s acc => map_size (cs_n s) + acc) 0 chunks.
  Definition aeager_of_ (P : aplace) (reg : Z -> region) (sec : secreg) : Z :=
    p_eager0 P + classes_eager_ reg 31 + 8 * sr_reserved sec + sec_eager_ (sr_chunks sec).

  Definition aregions (A : AState) : list (Z * Z) := aregions_ (a_pl A) (a_reg A) (a_sec A).
  Definition ahull_of (A : AState) : hull := ahull_of_ (a_pl A) (a_reg A) (a_sec A) (a_deadsh A).
  Definition aeager_of (A : AState) : Z := aeager_of_ (a_pl A) (a_reg A) (a_sec A).
  Definition alregions (A : AState) : list (Z * Z) := alregions_ (a_pl A) (a_reg A) (a_sec A).      (* [comment removed for export] *)
  Definition alhull_of (A : AState) : hull := alhull_of_ (a_pl A) (a_reg A) (a_sec A) (a_deadsh A).  (* [comment removed for export] *)
End Hulls.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Owned.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context (cl : clayout).

  Definition in_regions (R : list (Z * Z)) (a : Z) : Prop := exists b s, In (b, s) R /\ b <= a < b + s.
  (* [comment removed for export] *)
  Definition in_live_user_ (lm : gmap Z liveinfo) (a : Z) : Prop :=
    exists p li, lm !! p = Some li /\ p <= a < p + li_n li.
  Definition in_live_frame_ (ffs : gmap Z fframe) (a : Z) : Prop :=
    exists ff f, ffs !! ff = Some f /\ ff <= a < ff + fsize (ff_class f) - 8.
  Definition in_live_frame_shadow_ (ffs : gmap Z fframe) (a : Z) : Prop :=
    exists ff f, ffs !! ff = Some f /\ sh ff <= a < sh ff + fsize (ff_class f) / 8.

  (* [comment removed for export] *)
  Definition runtime_maps_ (P : aplace) (reg : Z -> region) (sec : secreg) : list (Z * Z) :=
    [ (p_thr P, 4096); (p_ctx P, 0x10000); (p_ri P, 4096); (p_fs P, kFakeStackBytes);
      (p_nodes0 P, kDepotNodesBlock); (p_frames0 P, kStackStoreBlockBytes); (p_pa P, 8 * kChunksBlockCount);
      (p_itab P, 0x38e000); (p_m64k P, 0x10000); (p_dtls P, 4096);
      (* [comment removed for export] *)
      (p_gvec P, 4096); (p_dvec P, 4096); (p_m11 P, 4096) ]
    ++ flat_map (fun c => let R := reg c in let rb := region_beg (p_sb P) c in
                          [(rb, rg_mapped_user R); (rb + kFreeArrayOffset, rg_mapped_fa R)])
                (map Z.of_nat (seq 1 30))
    ++ map (fun s => (cs_map s, map_size (cs_n s))) (sr_chunks sec).
  (* [comment removed for export] *)
  Definition heap_shadow_ (sb : Z) (reg : Z -> region) (sec : secreg) (a : Z) : Prop :=
    (exists c, 1 <= c <= 30 /\ let R := reg c in let rb := region_beg sb c in
        sh rb <= a < sh rb + rg_mapped_user R / 8)
    \/ (exists c, 1 <= c <= 30 /\ let R := reg c in let fa := region_beg sb c + kFreeArrayOffset in
        sh fa <= a < sh fa + rg_mapped_fa R / 8)
    \/ (exists s, In s (sr_chunks sec) /\ sh (cs_map s) <= a < sh (cs_map s) + map_size (cs_n s) / 8).
  (* [comment removed for export] *)
  Definition fs_shadow_owned_ (fs : Z) (ffs : gmap Z fframe) (a : Z) : Prop :=
    sh fs <= a < sh fs + kFakeStackBytes / 8 /\ ~ in_live_frame_shadow_ ffs a.

  (* [comment removed for export] *)
  Definition VIS0 (P : aplace) : list (Z * Z) :=
    [ (p_gvec P, 4096); (p_dvec P, 4096); (p_frames0 P, kStackStoreBlockBytes); (p_nodes0 P, kDepotNodesBlock);
      (p_fs P, kFakeStackBytes); (p_thr P, 4096); (p_m11 P, 4096); (p_ctx P, 0x10000); (p_dtls P, 4096); (p_ri P, 4096);
      (p_itab P, 0x38e000); (p_m64k P, 0x10000); (0x10000, 0x5fa000); stack_band_iv ].   (* [comment removed for export] *)
  Definition in_vis_shadow (V : list (Z * Z)) (z : Z) : Prop :=
    exists b n, In (b, n) V /\ kShadowOffset + b / 8 <= z < kShadowOffset + (b + n) / 8.
  (* [comment removed for export] *)
  Definition in_shadow_maps (a : Z) : Prop :=
    kLowShadowMapBeg <= a < kLowShadowMapBeg + 0x10000000 \/ kHighShadowMapBeg <= a < kHighShadowMapBeg + kHighShadowMapSize.
  Definition ghost_hs_ (P : aplace) (a : Z) : Prop :=
    in_shadow_maps a /\ ~ in_vis_shadow (VIS0 P) a.

  Definition aowned_ (P : aplace) (reg : Z -> region) (lm : gmap Z liveinfo) (sec : secreg) (ffs : gmap Z fframe) (a : Z) : Prop :=
    cl_static cl a
    \/ ((in_regions (runtime_maps_ P reg sec) a /\ ~ in_live_user_ lm a /\ ~ in_live_frame_ ffs a)
        \/ heap_shadow_ (p_sb P) reg sec a \/ fs_shadow_owned_ (p_fs P) ffs a)
    \/ ghost_hs_ P a.

  Definition in_live_user (A : AState) : Z -> Prop := in_live_user_ (a_livemap A).
  Definition in_live_frame (A : AState) : Z -> Prop := in_live_frame_ (a_fframes A).
  Definition in_live_frame_shadow (A : AState) : Z -> Prop := in_live_frame_shadow_ (a_fframes A).
  Definition runtime_maps (A : AState) : list (Z * Z) := runtime_maps_ (a_pl A) (a_reg A) (a_sec A).
  Definition heap_shadow (A : AState) : Z -> Prop := heap_shadow_ (a_sb A) (a_reg A) (a_sec A).
  Definition aowned (A : AState) : Z -> Prop := aowned_ (a_pl A) (a_reg A) (a_livemap A) (a_sec A) (a_fframes A).
End Owned.

(* [comment removed for export] *)
Ltac athin :=
  unfold as_live, as_fframe, as_release, as_tinycred, as_seccred, as_primcred, as_nlive, as_livebytes, quarantined_chunks, carved_count, batch_indices,
         depot_id, depot_n, depot_frames, aregions, ahull_of, aeager_of, alregions, alhull_of, in_live_user, in_live_frame, in_live_frame_shadow, runtime_maps, heap_shadow, aowned,
         a_b6, a_pa, a_thr, a_ctx, a_nodes0, a_frames0, a_fs, a_itab, a_m64k, a_sp0, a_sb, a_ri;
  cbn [a_pl a_reg a_cache_inited a_cache a_livemap a_qthread a_qglobal a_sec a_depot a_fhint a_fframes a_ia_inited a_oom a_tiny a_qlimbo a_scred a_deadsh a_pcred a_paid
       set_reg set_cache_inited set_cache set_livemap set_qthread set_qglobal set_sec set_depot set_fhint set_fframes set_ia set_oom set_tiny set_qlimbo set_scred set_deadsh set_pcred set_paid].
Tactic Notation "athin" "in" hyp(H) :=
  unfold as_live, as_fframe, as_release, as_tinycred, as_seccred, as_primcred, as_nlive, as_livebytes, quarantined_chunks, carved_count, batch_indices,
         depot_id, depot_n, depot_frames, aregions, ahull_of, aeager_of, alregions, alhull_of, in_live_user, in_live_frame, in_live_frame_shadow, runtime_maps, heap_shadow, aowned,
         a_b6, a_pa, a_thr, a_ctx, a_nodes0, a_frames0, a_fs, a_itab, a_m64k, a_sp0, a_sb, a_ri in H;
  cbn [a_pl a_reg a_cache_inited a_cache a_livemap a_qthread a_qglobal a_sec a_depot a_fhint a_fframes a_ia_inited a_oom a_tiny a_qlimbo a_scred a_deadsh a_pcred a_paid
       set_reg set_cache_inited set_cache set_livemap set_qthread set_qglobal set_sec set_depot set_fhint set_fframes set_ia set_oom set_tiny set_qlimbo set_scred set_deadsh set_pcred set_paid] in H.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma set_fframes_frames : forall A g, a_fframes (set_fframes A g) = g.
Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma set_fframes_id : forall A, set_fframes A (a_fframes A) = A.
Proof. intros [P r ci c lm qt qg s d fh ff ia oo bg ql sc dd]. reflexivity. Qed.
Lemma fold_release : forall rel A, fold_left as_release rel A = set_fframes A (fold_left (fun g ff => delete ff g) rel (a_fframes A)).
Proof.
  induction rel as [|ff rel IH]; intros A; cbn [fold_left].
  - symmetry. apply set_fframes_id.
  - rewrite IH. reflexivity.
Qed.

Lemma as_fframe_release_same : forall A ff, as_fframe (as_release A ff) ff = None.
Proof. intros. unfold as_fframe, as_release, as_fframe_. rewrite set_fframes_frames. rewrite (lookup_delete_eq (a_fframes A) ff). reflexivity. Qed.
Lemma as_fframe_release_other : forall A ff g, g <> ff -> as_fframe (as_release A ff) g = as_fframe A g.
Proof. intros. unfold as_fframe, as_release, as_fframe_. rewrite set_fframes_frames. rewrite (lookup_delete_ne (a_fframes A) ff g) by congruence. reflexivity. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma q_entries_app : forall a b, q_entries (a ++ b) = q_entries a ++ q_entries b.
Proof. intros. unfold q_entries. rewrite flat_map_app. reflexivity. Qed.

(* [comment removed for export] *)
Lemma fslots_pos : forall k, 0 <= k <= 10 -> 16 <= fslots k <= 16384.
Proof.
  intros k Hk. unfold fslots.
  assert (2 ^ 4 <= 2 ^ (14 - k)) by (apply Z.pow_le_mono_r; lia).
  assert (2 ^ (14 - k) <= 2 ^ 14) by (apply Z.pow_le_mono_r; lia).
  change (2^4) with 16 in *. change (2^14) with 16384 in *. lia.
Qed.
Lemma fsize_pos : forall k, 0 <= k <= 10 -> 64 <= fsize k <= 65536 /\ fsize k * fslots k = 2 ^ 20.
Proof.
  intros k Hk. unfold fsize, fslots.
  assert (2 ^ 0 <= 2 ^ k) by (apply Z.pow_le_mono_r; lia). assert (2 ^ k <= 2 ^ 10) by (apply Z.pow_le_mono_r; lia).
  change (2^0) with 1 in *. change (2^10) with 1024 in *. split; [lia|].
  assert (E : 2 ^ k * 2 ^ (14 - k) = 2 ^ 14) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  change (2 ^ 20) with (64 * 2 ^ 14). rewrite <- E. ring.
Qed.
Lemma ff_pos_range : forall h k age, 0 <= k <= 10 -> 0 <= ff_pos h k age < fslots k.
Proof. intros. unfold ff_pos. pose proof (fslots_pos k H). apply Z.mod_pos_bound. lia. Qed.
Lemma ff_pos_inj : forall h k a1 a2, 0 <= k <= 10 -> Z.of_nat a1 < fslots k -> Z.of_nat a2 < fslots k ->
  ff_pos h k a1 = ff_pos h k a2 -> a1 = a2.
Proof.
  intros h k a1 a2 Hk H1 H2 E. unfold ff_pos in E. pose proof (fslots_pos k Hk).
  set (n := fslots k) in *.
  assert (((h - 1 - Z.of_nat a1) - (h - 1 - Z.of_nat a2)) mod n = 0).
  { rewrite Zminus_mod, E, Z.sub_diag. apply Z.mod_0_l. lia. }
  replace (h - 1 - Z.of_nat a1 - (h - 1 - Z.of_nat a2)) with (Z.of_nat a2 - Z.of_nat a1) in H0 by lia.
  destruct (Z.lt_trichotomy (Z.of_nat a1) (Z.of_nat a2)) as [LT|[EQ|GT]]; [|lia|].
  - rewrite Z.mod_small in H0 by lia. lia.
  - assert (((Z.of_nat a1 - Z.of_nat a2)) mod n = 0).
    { replace (Z.of_nat a1 - Z.of_nat a2) with (- (Z.of_nat a2 - Z.of_nat a1)) by lia. apply Z_mod_zero_opp_full. exact H0. }
    rewrite Z.mod_small in H3 by lia. lia.
Qed.
Lemma fflags_off_range : forall k, 0 <= k <= 10 -> 0 <= fflags_off k /\ fflags_off k + fslots k <= 2 ^ 15 - 16.
Proof.
  intros k Hk. unfold fflags_off, fslots.
  assert (2 ^ (15 - k) = 2 * 2 ^ (14 - k)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
  assert (2 ^ 4 <= 2 ^ (14 - k)) by (apply Z.pow_le_mono_r; lia).
  assert (2 ^ (15 - k) <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia).
  change (2^4) with 16 in *. lia.
Qed.
(* [comment removed for export] *)
Lemma fflag_addr_inj : forall fs k p k' p', 0 <= k <= 10 -> 0 <= k' <= 10 -> 0 <= p < fslots k -> 0 <= p' < fslots k' ->
  fflag_addr fs k p = fflag_addr fs k' p' -> k = k' /\ p = p'.
Proof.
  intros fs k p k' p' Hk Hk' Hp Hp' E. unfold fflag_addr, fflags_off, fslots in *.
  assert (G : forall a b, 0 <= a <= 10 -> 0 <= b <= 10 -> a < b -> 2 ^ 15 - 2 ^ (15 - a) + 2 ^ (14 - a) <= 2 ^ 15 - 2 ^ (15 - b)).
  { intros a b Ha Hb Hab.
    assert (2 ^ (15 - a) = 2 * 2 ^ (14 - a)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
    assert (2 ^ (15 - b) <= 2 ^ (14 - a)) by (apply Z.pow_le_mono_r; lia). lia. }
  destruct (Z.lt_trichotomy k k') as [LT|[->|GT]].
  - pose proof (G k k' Hk Hk' LT). lia.
  - lia.
  - pose proof (G k' k Hk' Hk GT). lia.
Qed.
Lemma fflag_addr_range : forall fs k p, 0 <= k <= 10 -> 0 <= p < fslots k ->
  fs + kFakeFlagsOffset <= fflag_addr fs k p < fs + kFakeFramesOffset - 16.
Proof. intros fs k p Hk Hp. pose proof (fflags_off_range k Hk). unfold fflag_addr, kFakeFlagsOffset, kFakeFramesOffset. lia. Qed.
Lemma fframe_addr_range : forall fs k p, 0 <= k <= 10 -> 0 <= p < fslots k ->
  fs + kFakeFramesOffset + 2 ^ 20 * k <= fframe_addr fs k p /\ fframe_addr fs k p + fsize k <= fs + kFakeFramesOffset + 2 ^ 20 * (k + 1) /\
  fframe_addr fs k p + fsize k <= fs + kFakeStackBytes.
Proof.
  intros fs k p Hk Hp. pose proof (fsize_pos k Hk) as [S M]. unfold fframe_addr, kFakeStackSizeLog, kFakeStackBytes, kFakeFramesOffset.
  assert (fsize k * p + fsize k <= 2 ^ 20) by nia. split; [nia|]. split; nia.
Qed.
(* [comment removed for export] *)
Lemma fframe_addr_disjoint : forall fs k p k' p', 0 <= k <= 10 -> 0 <= k' <= 10 -> 0 <= p < fslots k -> 0 <= p' < fslots k' ->
  (k, p) <> (k', p') ->
  fframe_addr fs k p + fsize k <= fframe_addr fs k' p' \/ fframe_addr fs k' p' + fsize k' <= fframe_addr fs k p.
Proof.
  intros fs k p k' p' Hk Hk' Hp Hp' NE.
  destruct (Z.eq_dec k k') as [<-|NK].
  - assert (p <> p') by congruence. pose proof (fsize_pos k Hk) as [S _]. unfold fframe_addr.
    destruct (Z.lt_ge_cases p p'); [left|right]; nia.
  - pose proof (fframe_addr_range fs k p Hk Hp) as (A1 & A2 & _). pose proof (fframe_addr_range fs k' p' Hk' Hp') as (B1 & B2 & _).
    destruct (Z.lt_ge_cases k k'); [left|right]; nia.
Qed.
Lemma fframe_addr_align : forall fs k p, 0 <= k <= 10 -> 0 <= p -> fs mod 4096 = 0 -> fframe_addr fs k p mod Z.min (fsize k) 4096 = 0.
Proof.
  intros fs k p Hk Hp Hfs. pose proof (fsize_pos k Hk) as [S _].
  assert (D1 : (Z.min (fsize k) 4096 | 4096)).
  { unfold fsize. destruct (Z.le_gt_cases k 6).
    - rewrite Z.min_l. 2:{ assert (2 ^ k <= 2 ^ 6) by (apply Z.pow_le_mono_r; lia). change (2^6) with 64 in *. lia. }
      exists (2 ^ (6 - k)). assert (E : 2 ^ (6 - k) * 2 ^ k = 64) by (rewrite <- Z.pow_add_r by lia; replace (6 - k + k) with 6 by lia; reflexivity). nia.
    - rewrite Z.min_r. 2:{ assert (2 ^ 7 <= 2 ^ k) by (apply Z.pow_le_mono_r; lia). change (2^7) with 128 in *. lia. } exists 1. lia. }
  assert (D2 : (Z.min (fsize k) 4096 | fsize k)).
  { unfold fsize. destruct (Z.le_gt_cases k 6).
    - rewrite Z.min_l. 2:{ assert (2 ^ k <= 2 ^ 6) by (apply Z.pow_le_mono_r; lia). change (2^6) with 64 in *. lia. } exists 1; lia.
    - rewrite Z.min_r. 2:{ assert (2 ^ 7 <= 2 ^ k) by (apply Z.pow_le_mono_r; lia). change (2^7) with 128 in *. lia. }
      exists (2 ^ (k - 6)). assert (E : 2 ^ (k - 6) * 2 ^ 6 = 2 ^ k) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
      change (2 ^ 6) with 64 in E. nia. }
  set (M := Z.min (fsize k) 4096) in *. assert (0 < M) by lia.
  destruct D1 as [q1 E1]. destruct D2 as [q2 E2].
  pose proof (Z_div_exact_full_2 fs 4096 ltac:(lia) Hfs) as Efs.
  unfold fframe_addr. rewrite kFakeFramesOffset_val. unfold kFakeStackSizeLog. change (2 ^ 20) with (256 * 4096).
  match goal with |- ?x mod _ = 0 => replace x with ((fs / 4096 * q1 + 9 * q1 + 256 * k * q1 + p * q2) * M) by nia end.
  apply Z_mod_mult.
Qed.
