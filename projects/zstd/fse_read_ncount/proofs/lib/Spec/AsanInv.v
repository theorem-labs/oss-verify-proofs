(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation FinFun.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState Nodes Decode.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import AcctCore.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import BackingAlgebra.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl AsanCtrlProps SizeHist.
Import ListNotations.
Open Scope Z_scope.
Definition RES_HI : Z := 0x7fff7000.
Definition ACEIL : Z := 0x7fff7f800000.
Definition ATOP_MAX : Z := 0x7FFFFF800000.
Definition KHIGH : Z := 0x10007fff8000.
Definition LS_LO : Z := 0x7fff7000.
Definition LS_SZ : Z := 0x10000000.
Definition GAP_LO : Z := 0x8fff7000.
Definition GAP_SZ : Z := 0x20000000000.
Definition HS_LO : Z := 0x2008fff7000.
Definition HS_SZ : Z := 0xdfff0001000.
Definition PRIM_SZ : Z := 0x2000011000.
Definition PTR_SZ : Z := 0x800000.
Definition EAGER0 : Z := 2^25.
Definition TOT0 : Z := 2^45.
Definition RTOT0 : Z := 2^30.
Definition LEN0 : Z := 32.
Definition LIMIT : Z := 0x8000000000.
Definition SECM : Z := 2^33 - 2^30.
Definition NOPS : Z := 128.
Definition VC0 : Z := 31 * 0x40000.
Definition VCMAX : Z := VC0 + 2^19 * (2 * NOPS + 2) + 2^20.
Definition UWIN : Z := 2^27 + 2^24.
Definition FWIN : Z := 2^25.
Definition inW (sb pa a len : Z) : Prop :=
(exists c, 1 <= c <= 31 /\
((sb + c * K_REGION <= a /\ a + len <= sb + c * K_REGION + UWIN)
\/ (sb + c * K_REGION + K_FREEARR_OFF <= a /\ a + len <= sb + c * K_REGION + K_FREEARR_OFF + FWIN)))
\/ (pa <= a /\ a + len <= pa + K_PTRARR_RESERVE).
Definition RESERVE34 : Z := 2^33 - 2^29.
Definition CBROOM : Z := 0x400000000 - 2^25 - (2^33 - 2^30) - (2^33 - 2^29).
Definition LIMIT34 : Z := 0x400000000.
Definition atop_ok (ATOP : Z) : Prop := ACEIL <= ATOP <= ATOP_MAX.
Lemma LIMIT_eq : LIMIT = target_alloc_limit. Proof. reflexivity. Qed.
Lemma LIMIT34_eq : LIMIT34 = source_alloc_limit. Proof. reflexivity. Qed.
Lemma LIMIT34_le_LIMIT : LIMIT34 <= LIMIT. Proof. vm_compute. discriminate. Qed.
Definition is_prim_of (c : Z) (ch : achunk) : bool := match ch with CPrim c' _ => c' =? c | CSec _ _ _ => false end.
Definition sec_of (ch : achunk) : list (Z * Z) := match ch with CSec mb ms _ => [(mb, ms)] | CPrim _ _ => [] end.
Definition zlen {A} (l : list A) : Z := Z.of_nat (length l).
Definition cntP (c : Z) (l : list achunk) : Z := zlen (List.filter (is_prim_of c) l).
Definition secs (l : list achunk) : list (Z * Z) := flat_map sec_of l.
Definition live_chunks (st : astate) : list achunk := map snd (map_to_list (a_live st)).
Definition qchunks (bs : list abatch) : list achunk := flat_map b_chunks bs.
Definition qbatches (pb : list abatch) (st : astate) : list abatch := pb ++ a_qloc st ++ a_qglob st.
Definition all_chunks (pc : list achunk) (pb : list abatch) (st : astate) : list achunk :=
pc ++ live_chunks st ++ qchunks (qbatches pb st).
Definition CH (pc : list achunk) (pb : list abatch) (st : astate) : list (Z * Z) := secs (all_chunks pc pb st).
Definition nbatch (c : Z) (bs : list abatch) : Z := if c =? K_BATCH_CLASS then zlen bs else 0.
Fixpoint zsumc (l : list achunk) : Z := match l with [] => 0 | ch :: l' => chunk_size ch + zsumc l' end.
Fixpoint bsum (bs : list abatch) : Z := match bs with [] => 0 | b :: bs' => b_size b + bsum bs' end.
Definition chunk_wf (ATOP : Z) (ch : achunk) : Prop :=
match ch with
| CPrim c n => 0 <= n <= 64512 /\ c = class_id (needed_size n)
| CSec mb ms n => 64512 < n <= 536871936 /\ ms = sec_map_size n /\ mb mod 4096 = 0 /\ 0 < mb
/\ (mb + ms <= LS_LO \/ (KHIGH <= mb /\ mb + ms <= ATOP))
end.
Definition batch_wf (b : abatch) : Prop :=
b_count b = zlen (b_chunks b) /\ b_count b <= Q_BATCH /\ b_size b = Q_BATCH_BYTES + zsumc (b_chunks b)
/\ Forall (fun ch => 0 <= chunk_size ch <= Q_MAX) (b_chunks b).
Definition LMAX (c : Z) : Z :=
if c =? 1 then 32 * (2 * HB + 6) else if c =? 2 then 64 * (HB + 4) else 2^28.
Definition SMAX : Z := HB / 16127 + 4.
Definition LSBYTES : Z := 5 * HB + 4 * 536871936.
Fixpoint secbytes (l : list achunk) : Z :=
match l with [] => 0 | CSec _ _ n :: l' => n + secbytes l' | CPrim _ _ :: l' => secbytes l' end.
Definition live_budget (st : astate) : Prop :=
(forall c, 1 <= c <= 31 -> size_of_class c * cntP c (live_chunks st) <= LMAX c)
/\ zlen (secs (live_chunks st)) <= SMAX
/\ secbytes (live_chunks st) <= LSBYTES.
Definition cls_inv (pc : list achunk) (pb : list abatch) (st : astate) (c : Z) : Prop :=
let r := get_cls st c in
0 <= c_allocated_user r /\ c_allocated_user r <= c_mapped_user r /\ c_mapped_user r <= K_FREEARR_OFF
/\ c_mapped_user r - c_allocated_user r <= 2 * K_USER_MAP
/\ c_mapped_user r mod K_USER_MAP = 0
/\ 0 <= c_mapped_free_array r <= K_FREEARR_MAX /\ c_mapped_free_array r mod K_FREEARR_MAP = 0
/\ 0 <= c_num_freed r /\ 0 <= c_count r <= max_count st c
/\ c_allocated_user r = size_of_class c * (cntP c (all_chunks pc pb st) + nbatch c (qbatches pb st) + c_count r + c_num_freed r).
Definition AINV (ATOP : Z) (pc : list achunk) (pb : list abatch) (st : astate) : Prop :=
(forall c, 1 <= c <= 31 -> cls_inv pc pb st c)
/\ Forall (chunk_wf ATOP) (all_chunks pc pb st)
/\ Forall batch_wf (qbatches pb st)
/\ a_qloc_bytes st = bsum (a_qloc st) /\ a_qglob_bytes st = bsum (a_qglob st)
/\ a_nsec st = zlen (CH pc pb st)
/\ (a_nres st = 0 \/ a_nres st = K_CHUNKS_BLOCK)
/\ (forall id ch, (a_live st) !! id = Some ch -> (id < a_next st)%N)
/\ a_space_beg st mod 65536 = 0 /\ 0 < a_space_beg st /\ a_ptr_array st mod 4096 = 0 /\ 0 < a_ptr_array st
/\ live_budget st.
Definition went (e : Z * Z) : word * word := (Z_to_bv 64 (fst e), Z_to_bv 64 (snd e)).
Definition Pm (mo : Model) (x : Z) : bool := negb (covered (vm_noaccess (m_vmmaps mo) ++ m_vm_lazy mo) x).
Definition wsep (p q : word * word) : Prop :=
bv_unsigned (fst p) + bv_unsigned (snd p) <= bv_unsigned (fst q) \/ bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned (fst p).
Inductive seps : list (word * word) -> Prop :=
| seps_nil : seps []
| seps_cons : forall p l, Forall (wsep p) l -> seps l -> seps (p :: l).
Definition entry_ok (ATOP : Z) (e : word * word) : Prop :=
0 < bv_unsigned (snd e) /\ bv_unsigned (fst e) mod 4096 = 0 /\ bv_unsigned (snd e) mod 4096 = 0
/\ bv_unsigned (fst e) + bv_unsigned (snd e) <= ATOP.
Definition CLASSES : list Z := map Z.of_nat (seq 1 31).
Definition csum (f : aclass -> Z) (st : astate) : Z := fold_right (fun c acc => f (get_cls st c) + acc) 0 CLASSES.
Definition cls_mapped_bytes' (r : aclass) : Z := c_mapped_user r + c_mapped_free_array r.
Definition commit_bytes (st : astate) : Z := csum cls_mapped_bytes' st + 8 * a_nres st.
Definition rcov (P : list (word * word)) (iv : Z * Z) : Prop :=
exists e, In e P /\ bv_unsigned (fst e) <= fst iv /\ snd iv <= bv_unsigned (fst e) + bv_unsigned (snd e).
Definition START (RESV : list (Z * Z)) (ATOP : Z) (L0 R : list (word * word)) (st : astate) : Prop :=
(exists pb0, In (went (pb0, PRIM_SZ)) L0 /\ pb0 <= a_space_beg st /\ a_space_beg st + 2^37 + 2^12 <= pb0 + PRIM_SZ
/\ KHIGH <= pb0 /\ pb0 + PRIM_SZ <= ATOP)
/\ In (went (a_ptr_array st, PTR_SZ)) L0 /\ a_ptr_array st + PTR_SZ <= ATOP
/\ region_free R (Z_to_bv 64 (a_ptr_array st)) (Z_to_bv 64 PTR_SZ) = true
/\ In (went (LS_LO, LS_SZ)) L0 /\ In (went (GAP_LO, GAP_SZ)) L0 /\ In (went (HS_LO, HS_SZ)) L0
/\ zlen L0 <= LEN0 /\ live_bytes L0 <= TOT0
/\ Forall (rcov (R ++ L0)) RESV.
Definition AMI (RESV : list (Z * Z)) (ATOP : Z) (ch : list (Z * Z)) (st : astate) (mo : Model) : Prop :=
m_vm_materialized mo = []
/\ LIMIT34 <= vm_limit (m_vmmaps mo)
/\ Forall (fun e => bv_unsigned (fst e) + bv_unsigned (snd e) <= RES_HI) (vm_reserved (m_vmmaps mo))
/\ zlen (vm_reserved (m_vmmaps mo)) <= LEN0 /\ live_bytes (vm_reserved (m_vmmaps mo)) <= RTOT0
/\ Forall (entry_ok ATOP) (vm_maps (m_vmmaps mo))
/\ ivs_wf (vm_noaccess (m_vmmaps mo))
/\ ivs_wf (m_vm_lazy mo)
/\ seps (vm_maps (m_vmmaps mo))
/\ (atop_ok ATOP /\ alloc_top (m_vmmaps mo) = ATOP)
/\ exists L0, Permutation (vm_maps (m_vmmaps mo)) (L0 ++ map went ch)
/\ START RESV ATOP L0 (vm_reserved (m_vmmaps mo)) st
/\ sum_count (Pm mo) L0 <= EAGER0 + commit_bytes st.
Definition grant_model (mo : Model) (z nZ : Z) : Model :=
with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps mo)) ((Z_to_bv 64 z, Z_to_bv 64 nZ) :: vm_maps (m_vmmaps mo))
(vm_noaccess (m_vmmaps mo)) (vm_start_brk (m_vmmaps mo)) (vm_brk (m_vmmaps mo)) (vm_limit (m_vmmaps mo))
(vm_mmap_base (m_vmmaps mo)) (vm_init_sp (m_vmmaps mo))) mo.
Definition fixed_model (mo : Model) (flags addr nZ : Z) : Model :=
with_mmap_replacement (Z_to_bv 64 flags) (Z_to_bv 64 addr) (Z_to_bv 64 nZ)
(with_vmmaps (mmap_fixed_rw_next (m_vmmaps mo) (Z_to_bv 64 addr) (Z_to_bv 64 nZ)) mo).
Definition munmap_model (mo : Model) (addr nZ : Z) : Model :=
with_mmap_destroyed (Z_to_bv 64 addr) (Z_to_bv 64 nZ)
(mkVmMapsFull (vm_reserved (m_vmmaps mo)) (map_remove (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr))
(maps_subtract (vm_noaccess (m_vmmaps mo)) addr (addr + nZ))
(vm_start_brk (m_vmmaps mo)) (vm_brk (m_vmmaps mo)) (vm_limit (m_vmmaps mo))
(vm_mmap_base (m_vmmaps mo)) (vm_init_sp (m_vmmaps mo))) mo.
Definition INV (RESV : list (Z * Z)) (ATOP : Z) (pc : list achunk) (pb : list abatch) (st : astate) (mo : Model) : Prop :=
AINV ATOP pc pb st /\ AMI RESV ATOP (CH pc pb st) st mo.
Lemma all_chunks_put : forall pc pb c r st, all_chunks pc pb (put_cls c r st) = all_chunks pc pb st. Proof. reflexivity. Qed.
Lemma qbatches_put : forall pb c r st, qbatches pb (put_cls c r st) = qbatches pb st. Proof. reflexivity. Qed.
Lemma CH_put : forall pc pb c r st, CH pc pb (put_cls c r st) = CH pc pb st. Proof. reflexivity. Qed.
Lemma all_chunks_init_cache : forall pc pb st, all_chunks pc pb (init_cache st) = all_chunks pc pb st.
Proof. intros. unfold init_cache. destruct (a_cinit st); reflexivity. Qed.
Lemma qbatches_init_cache : forall pb st, qbatches pb (init_cache st) = qbatches pb st.
Proof. intros. unfold init_cache. destruct (a_cinit st); reflexivity. Qed.
Lemma CH_init_cache : forall pc pb st, CH pc pb (init_cache st) = CH pc pb st.
Proof. intros. unfold init_cache. destruct (a_cinit st); reflexivity. Qed.
Lemma all_chunks_set_nsec : forall pc pb v st, all_chunks pc pb (set_nsec v st) = all_chunks pc pb st. Proof. reflexivity. Qed.
Lemma In_CLASSES : forall c, In c CLASSES <-> 1 <= c <= 31.
Proof.
intros c. unfold CLASSES. rewrite in_map_iff. split.
- intros (n & <- & Hn). apply in_seq in Hn. Local Ltac2 Set LiaHints.tbl := fun () => "0030=18928195457.225492742081.28758904623.2 00000400800<S2HcS2HcS2Hn".
lia.
- intros Hc. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma CLASSES_nodup : List.NoDup CLASSES.
Proof. unfold CLASSES. Local Ltac2 Set LiaHints.tbl := fun () => "0010=48039668232.3000003S1E".
apply Finite.Injective_map_NoDup; [intros a b E; lia| apply seq_NoDup]. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma NoDup_CLASSES : List.NoDup CLASSES.
Proof. unfold CLASSES. apply (List.NoDup_map_NoDup_ForallPairs Z.of_nat). intros x y Hx Hy E. Local Ltac2 Set LiaHints.tbl := fun () => "0010;991448580.5000003S1E".
lia. apply List.seq_NoDup. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma fold_csum_ext : forall (f : aclass -> Z) st st' l,
(forall c, In c l -> get_cls st' c = get_cls st c) ->
fold_right (fun c acc => f (get_cls st' c) + acc) 0 l = fold_right (fun c acc => f (get_cls st c) + acc) 0 l.
Proof.
induction l as [|c l IH]; intros H; cbn; [reflexivity|]. rewrite H by (left; reflexivity). rewrite IH; [reflexivity|]. intros; apply H; right; assumption.
Qed.
Lemma fold_csum_put : forall (f : aclass -> Z) st c r l,
List.NoDup l -> In c l ->
fold_right (fun c' acc => f (get_cls (put_cls c r st) c') + acc) 0 l
= fold_right (fun c' acc => f (get_cls st c') + acc) 0 l - f (get_cls st c) + f r.
Proof.
induction l as [|c0 l IH]; intros Hnd Hin; [destruct Hin|]. cbn. inversion Hnd; subst.
destruct Hin as [->|Hin].
- rewrite get_put_eq. Local Ltac2 Set LiaHints.tbl := fun () => "0020>32663842154.1154039313488.9 000001002SS".
rewrite (fold_csum_ext f st (put_cls c r st)); [lia|]. intros c' Hc'. apply get_put_ne. congruence.
- rewrite get_put_ne by congruence. rewrite IH by assumption. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma csum_put : forall f st c r, 1 <= c <= 31 -> csum f (put_cls c r st) = csum f st - f (get_cls st c) + f r.
Proof. intros. unfold csum. Local Ltac2 Set LiaHints.tbl := fun () => "0010=48092843475.5000003S1H".
apply fold_csum_put; [apply NoDup_CLASSES| apply In_CLASSES; lia]. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma csum_init_cache : forall f st, csum f (init_cache st) = csum f st.
Proof. intros. unfold init_cache. destruct (a_cinit st); reflexivity. Qed.
Lemma commit_bytes_put : forall st c r, 1 <= c <= 31 ->
commit_bytes (put_cls c r st) = commit_bytes st - cls_mapped_bytes' (get_cls st c) + cls_mapped_bytes' r.
Proof. intros. unfold commit_bytes. rewrite csum_put by assumption. cbn [a_nres put_cls set_cls]. Local Ltac2 Set LiaHints.tbl := fun () => "0010=59470037757.4000001S".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma commit_bytes_init_cache : forall st, commit_bytes (init_cache st) = commit_bytes st.
Proof. intros. unfold commit_bytes. rewrite csum_init_cache. unfold init_cache. destruct (a_cinit st); reflexivity. Qed.
Definition vc_cls (r : aclass) : Z := c_mapped_user r + c_mapped_user r / 8 + K_FREEARR_MAP.
Definition VC (st : astate) : Z := csum vc_cls st + 8 * a_nres st.
Definition FAINV (st : astate) : Prop :=
forall c, 1 <= c <= 31 -> 0 <= c_mapped_free_array (get_cls st c) <= c_mapped_user (get_cls st c) / 8 + K_FREEARR_MAP
/\ 0 <= c_mapped_user (get_cls st c).
Lemma VC_put : forall st c r, 1 <= c <= 31 -> VC (put_cls c r st) = VC st - vc_cls (get_cls st c) + vc_cls r.
Proof. intros. unfold VC. rewrite csum_put by assumption. cbn [a_nres put_cls set_cls]. Local Ltac2 Set LiaHints.tbl := fun () => "0010=59470037757.4000001S".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma VC_init_cache : forall st, VC (init_cache st) = VC st.
Proof. intros. unfold VC. rewrite csum_init_cache. unfold init_cache. destruct (a_cinit st); reflexivity. Qed.
Lemma FAINV_put : forall st c r, 1 <= c <= 31 -> FAINV st ->
0 <= c_mapped_free_array r <= c_mapped_user r / 8 + K_FREEARR_MAP -> 0 <= c_mapped_user r -> FAINV (put_cls c r st).
Proof.
intros st c r Hc HF Hr Hu c' Hc'. destruct (Z.eq_dec c c') as [<-|NE].
- rewrite get_put_eq. auto.
- rewrite get_put_ne by exact NE. apply HF. exact Hc'.
Qed.
Lemma FAINV_init_cache : forall st, FAINV st -> FAINV (init_cache st).
Proof. intros st H c Hc. rewrite get_cls_init_cache. apply H. exact Hc. Qed.
Lemma csum_le : forall f g st, (forall c, 1 <= c <= 31 -> f (get_cls st c) <= g (get_cls st c)) -> csum f st <= csum g st.
Proof.
intros f g st H. unfold csum.
assert (G : forall l, (forall c, In c l -> 1 <= c <= 31) ->
fold_right (fun c acc => f (get_cls st c) + acc) 0 l <= fold_right (fun c acc => g (get_cls st c) + acc) 0 l).
{ Local Ltac2 Set LiaHints.tbl := fun () => "0020=15045126238.55264410137.9 000001008SS2IH2H0".
induction l as [|c l IH]; intros Hl; cbn [fold_right]; [lia|].
pose proof (H c (Hl c (or_introl eq_refl))). specialize (IH ltac:(intros; apply Hl; right; assumption)). lia. }
apply G. intros c Hc; apply In_CLASSES; exact Hc.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma commit_le_VC : forall st, FAINV st -> commit_bytes st <= VC st.
Proof.
intros st HF. unfold commit_bytes, VC. apply Z.add_le_mono_r. apply csum_le.
intros c Hc. destruct (HF c Hc) as [[H0 H1] H2]. unfold cls_mapped_bytes', vc_cls. Local Ltac2 Set LiaHints.tbl := fun () => "0010=68214939885.7000004S2H1".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma zlen_app : forall {A} (l1 l2 : list A), zlen (l1 ++ l2) = zlen l1 + zlen l2.
Proof. intros. unfold zlen. rewrite length_app. Local Ltac2 Set LiaHints.tbl := fun () => "0010=62102050378.3000001S".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma zlen_cons : forall {A} (x : A) l, zlen (x :: l) = 1 + zlen l.
Proof. intros. unfold zlen. cbn [length]. Local Ltac2 Set LiaHints.tbl := fun () => "0010=35073970142.3000001S".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma zlen_nil : forall {A}, zlen (@nil A) = 0. Proof. reflexivity. Qed.
Lemma zlen_nonneg : forall {A} (l : list A), 0 <= zlen l. Proof. intros. unfold zlen. Local Ltac2 Set LiaHints.tbl := fun () => "0010=53421126490.2000001S".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma cntP_app : forall c l1 l2, cntP c (l1 ++ l2) = cntP c l1 + cntP c l2.
Proof. intros. unfold cntP. rewrite filter_app. apply zlen_app. Qed.
Lemma cntP_cons : forall c ch l, cntP c (ch :: l) = (if is_prim_of c ch then 1 else 0) + cntP c l.
Proof. intros. unfold cntP. cbn [List.filter]. destruct (is_prim_of c ch); [rewrite zlen_cons|]; lia. Qed.
Lemma cntP_nil : forall c, cntP c [] = 0. Proof. reflexivity. Qed.
Lemma cntP_nonneg : forall c l, 0 <= cntP c l. Proof. intros. unfold cntP. apply zlen_nonneg. Qed.
Lemma secs_app : forall l1 l2, secs (l1 ++ l2) = secs l1 ++ secs l2.
Proof. intros. unfold secs. apply flat_map_app. Qed.
Lemma secs_cons : forall ch l, secs (ch :: l) = sec_of ch ++ secs l. Proof. reflexivity. Qed.
Lemma qchunks_app : forall b1 b2, qchunks (b1 ++ b2) = qchunks b1 ++ qchunks b2.
Proof. intros. unfold qchunks. apply flat_map_app. Qed.
Lemma qchunks_cons : forall b bs, qchunks (b :: bs) = b_chunks b ++ qchunks bs. Proof. reflexivity. Qed.
Lemma zsumc_app : forall l1 l2, zsumc (l1 ++ l2) = zsumc l1 + zsumc l2.
Proof. Local Ltac2 Set LiaHints.tbl := fun () => "0020=1524810573.4 54478046303.1000001002SS".
induction l1; intros; cbn; [lia|]. rewrite IHl1. lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma bsum_app : forall l1 l2, bsum (l1 ++ l2) = bsum l1 + bsum l2.
Proof. Local Ltac2 Set LiaHints.tbl := fun () => "0020=1524810573.4 54478046303.1000001002SS".
induction l1; intros; cbn; [lia|]. rewrite IHl1. lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma filter_perm : forall {A} (f : A -> bool) l l', Permutation l l' -> Permutation (List.filter f l) (List.filter f l').
Proof.
intros A f l l' HP. induction HP; cbn.
- constructor.
- destruct (f x); [apply perm_skip|]; assumption.
- destruct (f x), (f y); try apply perm_swap; try apply perm_skip; apply Permutation_refl.
- eapply Permutation_trans; eassumption.
Qed.
Lemma cntP_perm : forall c l l', Permutation l l' -> cntP c l = cntP c l'.
Proof. intros. unfold cntP, zlen. rewrite (Permutation_length (filter_perm (is_prim_of c) l l' H)). reflexivity. Qed.
Lemma secs_perm : forall l l', Permutation l l' -> Permutation (secs l) (secs l').
Proof. intros. unfold secs. apply Permutation_flat_map. assumption. Qed.
Lemma live_chunks_insert : forall st id ch,
(a_live st) !! id = None ->
Permutation (live_chunks (set_live (<[id := ch]> (a_live st)) st)) (ch :: live_chunks st).
Proof.
intros st id ch Hn. unfold live_chunks. cbn [a_live set_live].
change (ch :: map snd (map_to_list (a_live st))) with (map snd ((id, ch) :: map_to_list (a_live st))).
apply Permutation_map. apply map_to_list_insert. exact Hn.
Qed.
Lemma live_chunks_delete : forall st id ch,
(a_live st) !! id = Some ch ->
Permutation (live_chunks st) (ch :: live_chunks (set_live (delete id (a_live st)) st)).
Proof.
intros st id ch Hs. unfold live_chunks. cbn [a_live set_live].
change (ch :: map snd (map_to_list (delete id (a_live st)))) with (map snd ((id, ch) :: map_to_list (delete id (a_live st)))).
apply Permutation_map. symmetry. apply map_to_list_delete. exact Hs.
Qed.
Lemma sum_count_cons : forall P e l, sum_count P (e :: l) = iv_count P e + sum_count P l. Proof. reflexivity. Qed.
Lemma sum_count_perm : forall P l l', Permutation l l' -> sum_count P l = sum_count P l'.
Proof. intros P l l' HP. induction HP; rewrite ?sum_count_cons; lia. Qed.
Lemma iv_count_le_S : forall P e, iv_count P e <= S e.
Proof. intros. unfold iv_count. pose proof (zcount_le_len P (B e) (Z.to_nat (S e))). pose proof (S_range e). Local Ltac2 Set LiaHints.tbl := fun () => "0010=48046044546.4000006S1H2H0".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma sum_count_le_live : forall P l, sum_count P l <= live_bytes l.
Proof.
intros P l. rewrite live_bytes_sum_count. Local Ltac2 Set LiaHints.tbl := fun () => "0030=13493783587.615043163682.13908001623.6 00000700800<S3IHl1HSS2H0".
induction l; rewrite ?sum_count_cons; [cbn; lia|].
pose proof (iv_count_le_S P a). unfold iv_count at 2. unfold iv_count in H. rewrite zcount_const_true.
pose proof (S_range a). rewrite Z2Nat.id by lia. cbn [sum_count] in *. unfold iv_count in *. rewrite ?zcount_const_true in IHl. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma sum_count_ext_on : forall P Q l,
(forall e x, In e l -> B e <= x < B e + S e -> P x = Q x) -> sum_count P l = sum_count Q l.
Proof.
intros P Q l H. induction l as [|e l IH]; [reflexivity|]. rewrite !sum_count_cons.
rewrite IH by (intros e' x' He' Hx'; apply (H e' x'); [right|]; assumption).
unfold iv_count. Local Ltac2 Set LiaHints.tbl := fun () => "0030=25358923035.938040274754.640571964741.900000700800<S2Hx2H0SS2Hx".
rewrite (zcount_ext P Q); [lia|]. intros x Hx. apply (H e); [left; reflexivity|].
pose proof (S_range e). rewrite Z2Nat.id in Hx by lia. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma sum_count_sub : forall P l1 l2, sum_count P l1 <= sum_count P (l1 ++ l2).
Proof. intros. rewrite sum_count_app. pose proof (sum_count_nonneg P l2). Local Ltac2 Set LiaHints.tbl := fun () => "0010=41252059738.4000003S1H".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma wsep_sym : forall p q, wsep p q -> wsep q p. Proof. unfold wsep. Local Ltac2 Set LiaHints.tbl := fun () => "0010<3699446385.3000003S1H".
intros; lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma seps_perm : forall l l', Permutation l l' -> seps l -> seps l'.
Proof.
intros l l' HP. induction HP; intros Hs.
- constructor.
- inversion Hs; subst. constructor; [| auto]. eapply Permutation_Forall; eauto.
- inversion Hs; subst. inversion H2; subst. apply Forall_cons_iff in H1 as [Hxy Hl].
constructor. { constructor; [apply wsep_sym; exact Hxy| exact H3]. } constructor; assumption.
- auto.
Qed.
Lemma seps_cons_inv : forall p l, seps (p :: l) -> Forall (wsep p) l /\ seps l.
Proof. intros p l H. inversion H; auto. Qed.
Lemma region_free_wsep : forall l (a n : word),
region_free l a n = true -> Forall (wsep (a, n)) l.
Proof.
induction l as [|[b s] l IH]; intros a n H; [constructor|].
cbn [region_free] in H. apply andb_true_iff in H as [H1 H2]. constructor; [|apply IH; exact H2].
apply negb_true_iff in H1. unfold iv_overlap in H1. unfold wsep. cbn [fst snd].
apply andb_false_iff in H1 as [H1|H1]; apply Z.ltb_ge in H1; lia.
Qed.
Lemma overlap_sum_contained : forall l e lo hi,
seps l -> In e l -> B e <= lo -> hi <= B e + S e -> lo <= hi ->
overlap_sum l lo hi <= hi - lo.
Proof.
intros l e lo hi Hs Hin H1 H2 Hlh. apply in_split in Hin as (l1 & l2 & ->).
unfold overlap_sum. rewrite sum_count_app, sum_count_cons.
assert (Z0 : forall l', Forall (wsep e) l' -> sum_count (in_rng lo hi) l' = 0).
{ intros l' Hf. induction l' as [|q l' IH]; [reflexivity|]. rewrite sum_count_cons. apply Forall_cons_iff in Hf as [Hq Hf].
rewrite IH by exact Hf. fold (iv_count (in_rng lo hi) q). Local Ltac2 Set LiaHints.tbl := fun () => "0030>3116551640.14 32397203359.1366646037945.1400000@00C00DS2H12H22Hq2Hf2IHS1HS".
rewrite iv_count_in_rng_disjoint; [lia|].
unfold wsep, B, S in *. lia. }
pose proof (seps_perm _ _ (Permutation_sym (Permutation_middle l1 l2 e)) Hs) as Hs'.
apply seps_cons_inv in Hs' as [Hf _]. apply Forall_app in Hf as [Hf1 Hf2].
rewrite (Z0 l1 Hf1), (Z0 l2 Hf2). pose proof (iv_count_in_rng_le e lo hi Hlh). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma map_remove_perm : forall l (b s : word) l2,
Permutation l ((b, s) :: l2) -> seps l -> 0 < bv_unsigned s -> Forall (fun e => 0 < bv_unsigned (snd e)) l2 ->
Permutation (map_remove l b) l2.
Proof.
intros l b s l2 HP Hs Hpos Hall.
unfold map_remove. rewrite (filter_perm _ _ _ HP). cbn [List.filter fst]. rewrite bv_eqb_refl. cbn [negb].
pose proof (seps_perm _ _ HP Hs) as Hs'. apply seps_cons_inv in Hs' as [Hf _].
assert (E : List.filter (fun p : word * word => negb (bv_eqb (fst p) b)) l2 = l2).
{ clear HP Hs. induction l2 as [|[b' s'] l2 IH]; [reflexivity|]. apply Forall_cons_iff in Hf as [H1 Hf]. apply Forall_cons_iff in Hall as [H2 Hall].
cbn [List.filter fst]. destruct (bv_eqb b' b) eqn:E.
- exfalso. apply bv_eqb_eq in E. subst b'. unfold wsep in H1. cbn [fst snd] in H1, H2. Local Ltac2 Set LiaHints.tbl := fun () => "0010>59308598507.1100000GS4Hpos2H24Hall2H12Hf2IH".
lia.
- cbn [negb]. rewrite IH; auto. }
rewrite E. apply Permutation_refl.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma map_contains_In : forall l e (a n : word),
In e l -> bv_unsigned (fst e) <= bv_unsigned a -> bv_unsigned a + bv_unsigned n <= bv_unsigned (fst e) + bv_unsigned (snd e) ->
map_contains l a n = true.
Proof.
intros l e a n Hin H1 H2. unfold map_contains. apply existsb_exists. exists e. split; [exact Hin|].
apply andb_true_iff. split; apply Z.leb_le; lia.
Qed.
Lemma map_has_In : forall l (a n : word), In (a, n) l -> map_has l a n = true.
Proof. intros. unfold map_has. apply existsb_exists. exists (a, n). split; [assumption|]. cbn. rewrite !bv_eqb_refl. reflexivity. Qed.
Section AMIT.
Variable RESV : list (Z * Z).
Variable ATOP : Z.
Local Notation AMI' := (AMI RESV ATOP).
#[using="Type"] Lemma AMI_with_fds : forall ch st f mo, AMI' ch st (with_fds f mo) <-> AMI' ch st mo.
Proof. intros. unfold AMI, Pm. cbn. tauto. Qed.
#[using="Type"] Lemma AMI_atop : forall ch st mo, AMI' ch st mo -> atop_ok ATOP /\ alloc_top (m_vmmaps mo) = ATOP.
Proof. intros ch st mo (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & MT & _). exact MT. Qed.
#[using="Type"] Lemma AMI_mono : forall ch st st' mo,
AMI' ch st mo -> a_space_beg st' = a_space_beg st -> a_ptr_array st' = a_ptr_array st ->
commit_bytes st <= commit_bytes st' -> AMI' ch st' mo.
Proof.
intros ch st st' mo H Hsb Hpa Hcb. unfold AMI in *.
destruct H as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & MT & L0 & HP & HS & HB).
repeat (split; [assumption|]). exists L0. split; [exact HP|]. split.
- unfold START in *. rewrite Hsb, Hpa. exact HS.
- Local Ltac2 Set LiaHints.tbl := fun () => "0010=3463576108.23000008S2HB3Hcb".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma AMI_ivs_wf : forall ch st mo, AMI' ch st mo -> model_ivs_wf mo.
Proof.
intros ch st mo (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & [[T1 T2] T3] & _).
unfold ACEIL, ATOP_MAX in T1, T2.
split; [|split; [|split]].
- intros q Hq. unfold iv_wf, B, S. destruct (proj1 (Forall_forall _ _) M6 q Hq) as (_ & _ & _ & Hhi). Local Ltac2 Set LiaHints.tbl := fun () => "0020>13425494527.2067406623260.1700000800?S2T23HhiS2T12T3".
lia.
- exact M7.
- exact M8.
- unfold AsanCeil.init_sp_ok. unfold alloc_top, stack_max_size in T3. unfold sp_window_lo. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma nonlazy_sum_count : forall mo, m_vm_materialized mo = [] -> model_ivs_wf mo ->
nonlazy_bytes mo = sum_count (Pm mo) (vm_maps (m_vmmaps mo)).
Proof.
intros mo Hm Hwf. pose proof (vm_backing_used_sem mo Hwf) as E. rewrite vm_backing_used_split, Hm in E. cbn [length Z.of_nat] in E.
unfold Pm. Local Ltac2 Set LiaHints.tbl := fun () => "0010=63106954891.6000003S1E".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Fixpoint zsum2 (l : list (Z * Z)) : Z := match l with [] => 0 | e :: l' => snd e + zsum2 l' end.
#[using="Type"] Lemma live_bytes_went : forall ch, Forall (fun e => 0 <= snd e < 2^64) ch -> live_bytes (map went ch) = zsum2 ch.
Proof.
induction ch as [|[mb ms] ch IH]; intros Hf; [reflexivity|]. apply Forall_cons_iff in Hf as [H1 Hf]. cbn [map zsum2 snd fst] in *.
change (live_bytes (went (mb, ms) :: map went ch)) with (bv_unsigned (snd (went (mb, ms))) + live_bytes (map went ch)).
cbn [snd went fst]. Local Ltac2 Set LiaHints.tbl := fun () => "0010=48729660752.8000004S2H1".
rewrite unsigned_lit by lia. rewrite IH by exact Hf. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma AMI_nonlazy_bound : forall ch st mo,
AMI' ch st mo -> Forall (fun e => 0 <= snd e < 2^64) ch ->
nonlazy_bytes mo <= EAGER0 + commit_bytes st + zsum2 ch.
Proof.
intros ch st mo H Hch. pose proof (AMI_ivs_wf _ _ _ H) as Hwf.
destruct H as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & MT & L0 & HP & HS & HB).
rewrite (nonlazy_sum_count mo M1 Hwf). rewrite (sum_count_perm _ _ _ HP), sum_count_app.
pose proof (sum_count_le_live (Pm mo) (map went ch)). rewrite live_bytes_went in H by exact Hch. Local Ltac2 Set LiaHints.tbl := fun () => "0010>32954170079.22000006S2HB1H".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma region_free_app : forall l1 l2 (a n : word), region_free (l1 ++ l2) a n = region_free l1 a n && region_free l2 a n.
Proof. induction l1 as [|[b s] l1 IH]; intros; cbn; [reflexivity|]. rewrite IH. apply andb_assoc. Qed.
#[using="Type"] Lemma AMI_grant : forall ch st mo z nZ,
AMI' ch st mo ->
z mod 4096 = 0 -> 0 < z -> z + nZ <= ATOP -> nZ mod 4096 = 0 -> 0 < nZ ->
region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (Z_to_bv 64 z) (Z_to_bv 64 nZ) = true ->
AMI' ((z, nZ) :: ch) st (grant_model mo z nZ).
Proof.
intros ch st mo z nZ H Hal Hz Hce Hnl Hn Hrf.
destruct H as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & MT & L0 & HP & HS & HB).
pose proof MT as [[T1 T2] T3]. unfold ACEIL, ATOP_MAX in T1, T2.
unfold AMI, grant_model. cbn -[Z.add Z.mul Z.pow Z_to_bv bv_unsigned sum_count Pm live_bytes zlen].
repeat match goal with |- _ /\ _ => split end; try assumption.
- constructor; [|exact M6]. unfold entry_ok. cbn [fst snd]. Local Ltac2 Set LiaHints.tbl := fun () => "0060>28170367758.3038557300647.3049919153838.3061654370535.3063232909393.3063824951678.3000000500C00H00V00Z00_S3HnlS2Hz3Hce2Hn2T2S3HalS2Hz3Hce2Hn2T2S2HnS3Hce".
rewrite !unsigned_lit by lia. repeat split; lia.
- constructor; [|exact M9]. rewrite region_free_app in Hrf. apply andb_true_iff in Hrf as [_ Hrf].
apply (region_free_wsep (vm_maps (m_vmmaps mo)) (Z_to_bv 64 z) (Z_to_bv 64 nZ)). exact Hrf.
- exact (proj1 MT).
- exists L0. split; [|split; [exact HS| exact HB]].
change ((Z_to_bv 64 z, Z_to_bv 64 nZ) :: vm_maps (m_vmmaps mo)) with (went (z, nZ) :: vm_maps (m_vmmaps mo)).
cbn [map]. eapply Permutation_trans; [apply perm_skip; exact HP|]. apply Permutation_middle.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma covered_cons : forall e l x, covered (e :: l) x = in_iv e x || covered l x. Proof. reflexivity. Qed.
#[using="Type"] Lemma AMI_commit : forall ch st st' mo E a n,
AMI' ch st mo ->
In E (vm_maps (m_vmmaps mo)) -> B E <= a -> a + n <= B E + S E -> a mod 4096 = 0 -> n mod 4096 = 0 -> 0 < n ->
a_space_beg st' = a_space_beg st -> a_ptr_array st' = a_ptr_array st -> commit_bytes st + n <= commit_bytes st' ->
AMI' ch st' (fixed_model mo F_FIXED a n).
Proof.
intros ch st st' mo E a n H HinE HE1 HE2 Hal Hnl Hn Hsb Hpa Hcb.
pose proof (AMI_ivs_wf _ _ _ H) as (Wm & Wn & Wl & Wsp).
destruct H as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & MT & L0 & HP & HS & HB).
pose proof MT as [[T1 T2] T3]. unfold ACEIL, ATOP_MAX in T1, T2.
assert (HEok : bv_unsigned (fst E) + bv_unsigned (snd E) <= ATOP) by (destruct (proj1 (Forall_forall _ _) M6 E HinE) as (_ & _ & _ & ?); assumption).
Local Ltac2 Set LiaHints.tbl := fun () => "00<0>14246129146.4117081647355.4119348939463.4219348939717.4319349087306.4134437906783.4134447855365.4441893357072.41469334705.41  47477775166.4456765667309.4161929756993.4100000100D00H00L00P00Q00T00U00V00a00h00oFS3HE13HE22T24HEok1HS2HnS2HnS2HnFS1HFFS2HB3Hcb2HOS2Hn2HaS2Hn2Ha".
assert (Ha : 0 <= a /\ a + n < 2^64) by (unfold B, S in *; pose proof (bv_unsigned_in_range 64 (fst E)); lia).
unfold fixed_model, with_mmap_replacement, with_mmap_backing. change (mmap_noreserve_b (Z_to_bv 64 F_FIXED)) with false. cbv iota.
rewrite !unsigned_lit by lia.
unfold AMI. model_proj. unfold mmap_fixed_rw_next. cbn [vm_reserved vm_maps vm_noaccess vm_limit vm_start_brk vm_brk vm_mmap_base vm_init_sp alloc_top].
rewrite !unsigned_lit by lia. rewrite M1. cbn [List.filter].
repeat match goal with |- _ /\ _ => split end; try assumption.
all: try exact (proj1 MT).
all: try (unfold alloc_top in *; cbn [vm_init_sp] in *; lia).
- reflexivity.
- apply maps_subtract_wf; [exact Wn| lia].
- apply maps_subtract_wf; [exact Wl| lia].
- exists L0. split; [exact HP|]. split. { unfold START in *. rewrite Hsb, Hpa. exact HS. }
destruct (maps_subtract_sem _ a (a + n) Wn ltac:(lia)) as (_ & _ & Cn).
destruct (maps_subtract_sem _ a (a + n) Wl ltac:(lia)) as (_ & _ & Cl).
eapply Z.le_trans.
{ apply (sum_count_mono _ (fun x => Pm mo x || in_rng a (a + n) x)).
intros x. unfold Pm. model_proj. cbn [vm_noaccess]. rewrite !covered_app, Cn, Cl.
destruct (covered (vm_noaccess (m_vmmaps mo)) x), (covered (m_vm_lazy mo) x), (in_rng a (a + n) x); cbn; congruence. }
eapply Z.le_trans; [apply sum_count_or_le|].
fold (overlap_sum L0 a (a + n)).
assert (HO : overlap_sum L0 a (a + n) <= n); [|lia].
eapply Z.le_trans. { unfold overlap_sum. apply (sum_count_sub _ L0 (map went ch)). }
fold (overlap_sum (L0 ++ map went ch) a (a + n)). unfold overlap_sum. rewrite <- (sum_count_perm _ _ _ HP).
fold (overlap_sum (vm_maps (m_vmmaps mo)) a (a + n)).
pose proof (overlap_sum_contained (vm_maps (m_vmmaps mo)) E a (a + n) M9 HinE HE1 HE2 ltac:(lia)). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma AMI_recommit : forall ch st mo E a n,
AMI' ch st mo ->
In E (vm_maps (m_vmmaps mo)) -> B E <= a -> a + n <= B E + S E -> a mod 4096 = 0 -> n mod 4096 = 0 -> 0 < n ->
AMI' ch st (fixed_model mo F_FIXNORES a n).
Proof.
intros ch st mo E a n H HinE HE1 HE2 Hal Hnl Hn.
pose proof (AMI_ivs_wf _ _ _ H) as (Wm & Wn & Wl & Wsp).
destruct H as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & MT & L0 & HP & HS & HB).
pose proof MT as [[T1 T2] T3]. unfold ACEIL, ATOP_MAX in T1, T2.
assert (HEok : bv_unsigned (fst E) + bv_unsigned (snd E) <= ATOP) by (destruct (proj1 (Forall_forall _ _) M6 E HinE) as (_ & _ & _ & ?); assumption).
Local Ltac2 Set LiaHints.tbl := fun () => "00@0>14244035090.3817081647355.3719348939463.3919351188386.3834435815095.3843473170007.3845605947752.38467234137.38  51228322604.3856758590070.4156763564037.3856765667309.3761926872282.4161929756993.3761931851433.3862429608688.3800000100D00H00L00M00R00V00W00\00c00j01101801?01F01GFS3HE13HE22T24HEok1HS2HnS2HnFS3HalS2HaFS3HnlS2Hn2HaS2Hn2HaS2Hn2HaS2Hn2HaS2Hn2HaS2Hn2HaF".
assert (Ha : 0 <= a /\ a + n < 2^64) by (unfold B, S in *; pose proof (bv_unsigned_in_range 64 (fst E)); lia).
unfold fixed_model, with_mmap_replacement, with_mmap_backing. change (mmap_noreserve_b (Z_to_bv 64 F_FIXNORES)) with true. cbv iota.
rewrite !unsigned_lit by lia.
pose proof (lazy_interior_aligned (Z_to_bv 64 a) (Z_to_bv 64 n)) as HLI. rewrite !unsigned_lit in HLI by lia.
specialize (HLI ltac:(unfold page_size; lia) ltac:(unfold page_size; lia) Hn ltac:(lia)).
unfold AMI. model_proj. rewrite HLI. unfold mmap_fixed_rw_next. cbn [vm_reserved vm_maps vm_noaccess vm_limit vm_start_brk vm_brk vm_mmap_base vm_init_sp alloc_top app].
rewrite !unsigned_lit by lia. rewrite M1. cbn [List.filter].
repeat match goal with |- _ /\ _ => split end; try assumption.
all: try exact (proj1 MT).
all: try (unfold alloc_top in *; cbn [vm_init_sp] in *; lia).
- reflexivity.
- apply maps_subtract_wf; [exact Wn| lia].
- apply ivs_wf_cons. { unfold iv_wf, B, S. cbn [fst snd]. rewrite !unsigned_lit by lia. lia. } apply maps_subtract_wf; [exact Wl| lia].
- exists L0. split; [exact HP|]. split; [exact HS|].
destruct (maps_subtract_sem _ a (a + n) Wn ltac:(lia)) as (_ & _ & Cn).
destruct (maps_subtract_sem _ a (a + n) Wl ltac:(lia)) as (_ & _ & Cl).
eapply Z.le_trans; [| exact HB]. apply sum_count_mono.
intros x. unfold Pm. model_proj. rewrite HLI. cbn [vm_noaccess app]. rewrite !covered_app, covered_cons, Cn, Cl.
unfold in_iv, B, S. cbn [fst snd]. rewrite !unsigned_lit by lia.
destruct (covered (vm_noaccess (m_vmmaps mo)) x), (covered (m_vm_lazy mo) x), (in_rng a (a + n) x); cbn; congruence.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma seps_filter : forall f l, seps l -> seps (List.filter f l).
Proof.
induction l as [|e l IH]; intros Hs; [constructor|]. apply seps_cons_inv in Hs as [Hf Hs]. cbn.
destruct (f e); [|apply IH; exact Hs]. constructor; [|apply IH; exact Hs].
apply (Forall_incl _ _ _ (incl_filter f l)) || (rewrite Forall_forall in *; intros q Hq; apply Hf; apply (incl_filter f l); exact Hq).
Qed.
#[using="Type"] Lemma AMI_munmap : forall ch1 ch2 st st' mo mb ms,
AMI' (ch1 ++ (mb, ms) :: ch2) st mo -> 0 < mb -> 0 < ms -> mb + ms <= ATOP ->
a_space_beg st' = a_space_beg st -> a_ptr_array st' = a_ptr_array st -> commit_bytes st <= commit_bytes st' ->
AMI' (ch1 ++ ch2) st' (munmap_model mo mb ms).
Proof.
intros ch1 ch2 st st' mo mb ms H Hmb Hms Hce Hsb Hpa Hcb.
pose proof (AMI_ivs_wf _ _ _ H) as (Wm & Wn & Wl & Wsp).
destruct H as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & MT & L0 & HP & HS & HB).
pose proof MT as [[T1 T2] T3]. unfold ACEIL, ATOP_MAX in T1, T2.
assert (HP2 : Permutation (vm_maps (m_vmmaps mo)) (went (mb, ms) :: (L0 ++ map went (ch1 ++ ch2)))).
{ eapply Permutation_trans; [exact HP|]. rewrite !map_app. cbn [map]. rewrite !app_assoc.
apply Permutation_sym. apply Permutation_middle. }
pose proof (seps_perm _ _ HP2 M9) as Hs2. apply seps_cons_inv in Hs2 as [Hfar _].
assert (HR : Permutation (map_remove (vm_maps (m_vmmaps mo)) (Z_to_bv 64 mb)) (L0 ++ map went (ch1 ++ ch2))).
{ Local Ltac2 Set LiaHints.tbl := fun () => "00A0>14246130955.39209975112.46  31949594027.3934341210997.383461562018.41 36787005256.3945679985143.39469328448.39  48725467076.3848729655076.3948729658063.4652726574795.4652726577952.3954891489804.4054891607152.3966750950872.4666833242881.3900000100700800=00E00F00G00H00X00h01801H01X01]01b01h01iFS2Hx1HFS3HmsS2HB3HcbFFFS3Hmb3Hms3Hce2T2S3Hmb3Hms3Hce2T2S3Hmb3Hms3Hce2T2S3Hmb3Hms3Hce2T2S3Hmb3Hms3Hce2T2S3HmsS3HmsS2Hx1HF".
apply (map_remove_perm _ (Z_to_bv 64 mb) (Z_to_bv 64 ms)); [exact HP2| exact M9| rewrite unsigned_lit by lia; lia|].
assert (HF : Forall (fun e : word * word => 0 < bv_unsigned (snd e)) (vm_maps (m_vmmaps mo))).
{ eapply Forall_impl; [|exact M6]. intros e (He & _). exact He. }
pose proof (Permutation_Forall HP2 HF) as HF2. apply Forall_cons_iff in HF2 as [_ HF2]. exact HF2. }
unfold munmap_model, with_mmap_destroyed. rewrite !unsigned_lit by lia.
unfold AMI. model_proj. cbn [vm_reserved vm_maps vm_noaccess vm_limit vm_start_brk vm_brk vm_mmap_base vm_init_sp alloc_top].
rewrite M1. cbn [List.filter].
repeat match goal with |- _ /\ _ => split end; try assumption.
all: try exact (proj1 MT).
all: try (unfold alloc_top in *; cbn [vm_init_sp] in *; lia).
- reflexivity.
- unfold map_remove. rewrite Forall_forall in *. intros e He. apply M6. apply (incl_filter _ _ _ He).
- apply maps_subtract_wf; [exact Wn| lia].
- apply maps_subtract_wf; [exact Wl| lia].
- unfold map_remove. apply seps_filter. exact M9.
- exists L0. split; [exact HR|]. split. { unfold START in *. rewrite Hsb, Hpa. exact HS. }
destruct (maps_subtract_sem _ mb (mb + ms) Wn ltac:(lia)) as (_ & _ & Cn).
destruct (maps_subtract_sem _ mb (mb + ms) Wl ltac:(lia)) as (_ & _ & Cl).
rewrite (sum_count_ext_on _ (Pm mo)); [lia|].
intros e x He Hx. unfold Pm. model_proj. cbn [vm_noaccess]. rewrite !covered_app, Cn, Cl.
apply Forall_app in Hfar as [HfL _]. pose proof (proj1 (Forall_forall _ _) HfL e He) as Hw.
unfold wsep, B, S in *. cbn [fst snd went] in Hw. rewrite !unsigned_lit in Hw by lia.
replace (in_rng mb (mb + ms) x) with false.
2:{ symmetry. unfold in_rng. apply andb_false_iff. destruct Hw; [right; apply Z.ltb_ge| left; apply Z.leb_gt]; lia. }
destruct (covered (vm_noaccess (m_vmmaps mo)) x), (covered (m_vm_lazy mo) x); reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End AMIT.
Arguments AMI_with_fds {RESV ATOP}.
Arguments AMI_atop {RESV ATOP}.
Arguments AMI_mono {RESV ATOP}.
Arguments AMI_ivs_wf {RESV ATOP}.
Arguments AMI_nonlazy_bound {RESV ATOP}.
Arguments AMI_grant {RESV ATOP}.
Arguments AMI_commit {RESV ATOP}.
Arguments AMI_recommit {RESV ATOP}.
Arguments AMI_munmap {RESV ATOP}.
