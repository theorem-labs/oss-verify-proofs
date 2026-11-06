From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YP09 YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s YG0q YG0t.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
(* User-poisoned granules inside live chunks (fuzz/alloc.c poisons a 16-byte head in each block it gets from
   malloc). The donor's AR fixes every chunk granule's shadow byte to the allocator's value; ARU is AR of the memory
   read with the user-poisoned shadow bytes as 0, plus where those ranges are and that their shadow bytes read 0xf7.
   ARU with no range is AR (ARU_nil). Design: design/POISON.md of a Theorem Labs lane. *)
Section u. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
(* s is a shadow byte of one of the ranges U, each (p, len) a run of whole granules. *)
Definition in_ush (U : list (Z * Z)) (s : Z) : bool :=
existsb (fun r => (shadow_addr (fst r) <=? s) && (s <? shadow_addr (fst r) + snd r / 8)) U.
(* The memory as the allocator made it: the user-poisoned shadow bytes read 0. *)
Definition unpoison (U : list (Z * Z)) (mem : word -> option byte) : word -> option byte :=
fun w => if in_ush U (bv_unsigned w) then Some (Z_to_bv 8 0) else mem w.
(* Each range is granule-aligned, in the whole user granules of a live block, and the ranges are disjoint. *)
Definition upoison_ok (ly : alayout) (S : astate) (U : list (Z * Z)) : Prop :=
Forall (fun r => fst r mod 8 = 0 /\ 8 <= snd r /\ snd r mod 8 = 0 /\
exists p n, In (p, n) (ablocks B ly S) /\ p <= fst r /\ fst r + snd r <= p + 8 * (req_size n / 8)) U /\
pairwise zdisjoint U.
(* Their shadow bytes hold kAsanUserPoisonedMemoryMagic. *)
Definition upoisoned (W : world segs) (mem : word -> option byte) (U : list (Z * Z)) : Prop :=
forall s, in_ush U s = true -> aview segs (w_H W) mem s = Some 247.
Definition ARU (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world segs) (mem : word -> option byte)
(md : Model) : Prop :=
AR segs B ly S W (unpoison U mem) md /\ upoison_ok ly S U /\ upoisoned W mem U.
Lemma unpoison_nil : forall mem, unpoison [] mem = mem.
Proof. intros mem. reflexivity. Qed.
Lemma ARU_nil : forall ly S W mem md, ARU ly S [] W mem md <-> AR segs B ly S W mem md.
Proof.
intros ly S W mem md. unfold ARU. rewrite unpoison_nil. split.
- intros (H & _ & _). exact H.
- intros H. split; [exact H|]. split; [split; [constructor | exact I]|]. intros s Hs. discriminate Hs.
Qed.
(* ecall_pre (YG0d.v) with ARU's memory. *)
Definition ecall_preU (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) : Prop :=
ecall_pre segs B ly S W regs (unpoison U mem) md /\ upoison_ok ly S U /\ upoisoned W mem U.
Lemma ecall_preU_nil : forall ly S W regs mem md, ecall_preU ly S [] W regs mem md <-> ecall_pre segs B ly S W regs mem md.
Proof.
intros ly S W regs mem md. unfold ecall_preU. rewrite unpoison_nil. split.
- intros (H & _ & _). exact H.
- intros H. split; [exact H|]. split; [split; [constructor | exact I]|]. intros s Hs. discriminate Hs.
Qed.
End u.
Section l. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
#[local] Abbreviation ARU := (ARU segs B).
#[local] Abbreviation upoison_ok := (upoison_ok B).
#[local] Abbreviation upoisoned := (upoisoned segs).
Lemma wz : forall a, 0 <= a < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 a) = a.
Proof. intros a Ha. rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity|]. change (bv_modulus 64) with (2 ^ 64). lia. Qed.
Lemma unpoison_out : forall U mem w, in_ush U (bv_unsigned w) = false -> unpoison U mem w = mem w.
Proof. intros U mem w H. unfold unpoison. rewrite H. reflexivity. Qed.
Lemma unpoison_in : forall U mem w, in_ush U (bv_unsigned w) = true -> unpoison U mem w = Some (Z_to_bv 8 0).
Proof. intros U mem w H. unfold unpoison. rewrite H. reflexivity. Qed.
Lemma aview_at : forall H m1 m2 a, m1 (Z_to_bv 64 a) = m2 (Z_to_bv 64 a) -> aview segs H m1 a = aview segs H m2 a.
Proof. intros H m1 m2 a E. unfold aview, mbyte, mrestrict. destruct (H (Z_to_bv 64 a)); [reflexivity|]. rewrite E. reflexivity. Qed.
Lemma aview_hidden_same : forall H m1 m2 a, H (Z_to_bv 64 a) = true -> aview segs H m1 a = aview segs H m2 a.
Proof. intros H m1 m2 a E. unfold aview, mbyte, mrestrict. rewrite E. reflexivity. Qed.
Lemma aview_vis_byte : forall H m a b, H (Z_to_bv 64 a) = false -> m (Z_to_bv 64 a) = Some b ->
aview segs H m a = Some (bv_unsigned b).
Proof. intros H m a b E M. unfold aview, mbyte, mrestrict. rewrite E, M. reflexivity. Qed.
Lemma aview_mod : forall H m a, aview segs H m a = aview segs H m (a mod 2 ^ 64).
Proof.
intros H m a. assert (E : Z_to_bv 64 a = Z_to_bv 64 (a mod 2 ^ 64)).
{ apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity. }
unfold aview, mbyte. rewrite E. reflexivity.
Qed.
Lemma aview_unpoison_out : forall H U m a, in_ush U (bv_unsigned (Z_to_bv 64 a)) = false ->
aview segs H (unpoison U m) a = aview segs H m a.
Proof. intros H U m a E. apply aview_at. apply unpoison_out. exact E. Qed.
Lemma aview_unpoison_in : forall H U m1 m2 a, in_ush U (bv_unsigned (Z_to_bv 64 a)) = true ->
aview segs H (unpoison U m1) a = aview segs H (unpoison U m2) a.
Proof. intros H U m1 m2 a E. apply aview_at. rewrite !unpoison_in by exact E. reflexivity. Qed.
Lemma in_ush_spec : forall U s, in_ush U s = true <-> exists r, In r U /\ shadow_addr (fst r) <= s < shadow_addr (fst r) + snd r / 8.
Proof.
intros U s. unfold in_ush. rewrite existsb_exists. split; intros (r & Hr & H); exists r; split; try exact Hr.
- apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
- apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Lemma in_ush_cons : forall r U s, in_ush (r :: U) s = ((shadow_addr (fst r) <=? s) && (s <? shadow_addr (fst r) + snd r / 8)) || in_ush U s.
Proof. reflexivity. Qed.
Lemma upoison_ok_In : forall ly S U r, upoison_ok ly S U -> In r U ->
fst r mod 8 = 0 /\ 8 <= snd r /\ snd r mod 8 = 0 /\
exists p n, In (p, n) (ablocks B ly S) /\ p <= fst r /\ fst r + snd r <= p + 8 * (req_size n / 8).
Proof. intros ly S U r [F _] Hr. exact (proj1 (Forall_forall _ _) F r Hr). Qed.
(* A user-poisoned shadow byte is the shadow of a whole granule of a live block. *)
Lemma ush_granule : forall ly S U s, upoison_ok ly S U -> in_ush U s = true ->
exists g p n, In (p, n) (ablocks B ly S) /\ g mod 8 = 0 /\ shadow_addr g = s /\ p <= g /\ g + 8 <= p + 8 * (req_size n / 8).
Proof.
intros ly S U s OK Hs. apply in_ush_spec in Hs as (r & Hr & Hs).
destruct (upoison_ok_In ly S U r OK Hr) as (A8 & L8 & M8 & p & n & Hb & P1 & P2).
apply Z.mod_divide in A8 as [q Hq]; [|lia]. apply Z.mod_divide in M8 as [m Hm]; [|lia].
unfold shadow_addr in Hs. rewrite Hq, Hm, !Z.div_mul in Hs by lia.
exists (8 * (s - SHADOW_OFF)), p, n. split; [exact Hb|].
split; [rewrite Z.mul_comm; apply Z.mod_mul; lia|].
split; [unfold shadow_addr; rewrite Z.mul_comm, Z.div_mul by lia; lia|].
lia.
Qed.
Lemma ablock_chunk : forall ly S p n, In (p, n) (ablocks B ly S) ->
exists k, In k (st_chunks S) /\ sptr_addr B ly (ck_user k) = p /\ ck_req k = n.
Proof.
intros ly S p n H. unfold ablocks, blocks in H. apply in_map_iff in H as ([q m] & E & H). cbn [fst snd] in E.
injection E as E1 E2. apply in_map_iff in H as (k & E & H). injection E as E3 E4. apply filter_In in H as [Hk _].
exists k. split; [exact Hk|]. subst. split; reflexivity.
Qed.
Lemma find_chunk_at_some : forall ly l g k, In k l -> ck_base B ly k <= g < ck_base B ly k + ck_extent k ->
exists k', find_chunk_at B ly l g = Some k'.
Proof.
intros ly l g k. induction l as [|k0 t IH]; intros Hin Hg; [destruct Hin|]. cbn [find_chunk_at].
destruct ((ck_base B ly k0 <=? g) && (g <? ck_base B ly k0 + ck_extent k0)) eqn:E; [eexists; reflexivity|].
destruct Hin as [<-|Hin]; [|exact (IH Hin Hg)].
exfalso. apply andb_false_iff in E as [E|E]; [apply Z.leb_gt in E | apply Z.ltb_ge in E]; lia.
Qed.
Lemma ablock_ashadow : forall ly S rd p n g, ARm B ly S rd -> In (p, n) (ablocks B ly S) -> p <= g < p + req_size n ->
exists v, ashadow B ly S g = Some v.
Proof.
intros ly S rd p n g M Hb Hg. destruct (ablock_chunk ly S p n Hb) as (k & Hk & Hu & Hn). subst n.
pose proof (chunk_facts B ly S rd k M Hk) as (_ & _ & _ & G4 & G5 & _ & _ & G8 & _).
destruct (find_chunk_at_some ly (st_chunks S) g k Hk) as (k' & F); [lia|].
exists (chunk_granule k' ((g - ck_base B ly k') / 8)). unfold ashadow. rewrite F. reflexivity.
Qed.
Lemma ush_facts : forall ly S U W mem md s, ARU ly S U W mem md -> in_ush U s = true ->
aowned B ly S s /\ SHADOW_OFF <= s < kHighMemBeg.
Proof.
intros ly S U W mem md s (HAR & OK & _) Hs. destruct (ush_granule ly S U s OK Hs) as (g & p & n & Hb & G8 & Gs & Gp & Gn).
pose proof (proj1 HAR) as M.
pose proof (Z.mul_div_le (req_size n) 8 ltac:(lia)) as RD.
destruct (ablock_ashadow ly S _ p n g M Hb ltac:(lia)) as (v & Hv).
rewrite <- Gs. split; [exact (ashadow_owned B ly S _ g v M Hv) | exact (ashadow_low B ly S _ g v M Hv)].
Qed.
Lemma ush_range : forall ly S U W mem md s, ARU ly S U W mem md -> in_ush U s = true -> 0 <= s < 2 ^ 64.
Proof. intros ly S U W mem md s H Hs. pose proof (ush_facts ly S U W mem md s H Hs) as (_ & L1 & L2). unfold SHADOW_OFF, kHighMemBeg in *. lia. Qed.
Lemma ARU_ARm : forall ly S U W mem md, ARU ly S U W mem md -> ARm B ly S (aview segs (w_H W) (unpoison U mem)).
Proof. intros ly S U W mem md (HAR & _ & _). exact (proj1 HAR). Qed.
Lemma ARU_AR : forall ly S U W mem md, ARU ly S U W mem md -> AR segs B ly S W (unpoison U mem) md.
Proof. intros ly S U W mem md (HAR & _ & _). exact HAR. Qed.
Lemma ARU_ok : forall ly S U W mem md, ARU ly S U W mem md -> upoison_ok ly S U.
Proof. intros ly S U W mem md (_ & OK & _). exact OK. Qed.
Lemma ARU_poisoned : forall ly S U W mem md, ARU ly S U W mem md -> upoisoned W mem U.
Proof. intros ly S U W mem md (_ & _ & P). exact P. Qed.
Lemma ARU_stack : forall ly S U W mem md a, ARU ly S U W mem md -> ly_stk_lo ly <= a < ly_stk_hi ly -> ~ aowned B ly S a.
Proof. intros ly S U W mem md a H Ha. exact (al_stack _ _ LAWS ly S W (unpoison U mem) md a (ARU_AR _ _ _ _ _ _ H) Ha). Qed.
(* Below the shadow (the image's cells, the low application memory) the memory is the allocator's. *)
Lemma ARU_mem_low : forall ly S U W mem md w, ARU ly S U W mem md -> bv_unsigned w < SHADOW_OFF -> unpoison U mem w = mem w.
Proof.
intros ly S U W mem md w H Hw. apply unpoison_out. destruct (in_ush U (bv_unsigned w)) eqn:E; [|reflexivity].
exfalso. pose proof (ush_facts ly S U W mem md _ H E) as (_ & L & _). lia.
Qed.
(* Outside the user-poisoned bytes the two readings agree. *)
Lemma ARU_view_out : forall ly S U W mem md a, ARU ly S U W mem md -> in_ush U (bv_unsigned (Z_to_bv 64 a)) = false ->
aview segs (w_H W) mem a = aview segs (w_H W) (unpoison U mem) a.
Proof. intros ly S U W mem md a _ E. symmetry. apply aview_unpoison_out. exact E. Qed.
(* The form of AR_frame_law (YG0d.v) for ARU, with the same U. *)
Lemma ARU_frame : forall ly S U W mem md mem' md',
ARU ly S U W mem md ->
(forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
(forall a, aview segs (w_H W) mem a <> None -> aview segs (w_H W) mem' a <> None) ->
m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
(forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
ARU ly S U W mem' md'.
Proof.
intros ly S U W mem md mem' md' H HOWN HVIS E1 E2 E3 HB.
pose proof H as (HAR & OK & PO).
split; [|split; [exact OK|]].
- apply (al_frame _ _ LAWS ly S W (unpoison U mem) md (unpoison U mem') md' HAR); [| |exact E1|exact E2|exact E3|].
  + intros a Ha Hown. destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))) eqn:Ei.
    * apply aview_unpoison_in. exact Ei.
    * rewrite !aview_unpoison_out by exact Ei. exact (HOWN a Ha Hown).
  + intros a Hv. destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))) eqn:Ei.
    * rewrite (aview_unpoison_in _ U mem' mem a Ei). exact Hv.
    * rewrite aview_unpoison_out in Hv |- * by exact Ei. exact (HVIS a Hv).
  + intros a Hb Hh. unfold unpoison. destruct (in_ush U (bv_unsigned (w64 a))); [reflexivity | exact (HB a Hb Hh)].
- intros s Hs. pose proof (ush_facts ly S U W mem md s H Hs) as (Hown & _).
  rewrite (HOWN s (ush_range ly S U W mem md s H Hs) Hown). exact (PO s Hs).
Qed.
(* The shadow byte of an address outside every live block is not user-poisoned. *)
Lemma ARU_shadow_out_block : forall ly S U W mem md a, ARU ly S U W mem md -> 0 <= a < 2 ^ 64 ->
(forall p n, In (p, n) (ablocks B ly S) -> ~ (p <= a < p + req_size n)) ->
in_ush U (bv_unsigned (Z_to_bv 64 (shadow_addr a))) = false.
Proof.
intros ly S U W mem md a H Ha NB. destruct (in_ush U (bv_unsigned (Z_to_bv 64 (shadow_addr a)))) eqn:E; [|reflexivity]. exfalso.
assert (SA : 0 <= shadow_addr a < 2 ^ 64) by (unfold shadow_addr, SHADOW_OFF; pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)); pose proof (Z.div_le_upper_bound a 8 (2 ^ 61) ltac:(lia) ltac:(lia)); lia).
rewrite (wz _ SA) in E.
destruct (ush_granule ly S U _ (ARU_ok _ _ _ _ _ _ H) E) as (g & p & n & Hb & G8 & Gs & Gp & Gn).
pose proof (Z.mul_div_le (req_size n) 8 ltac:(lia)) as RD.
apply (NB p n Hb). apply Z.mod_divide in G8 as [k Hk]; [|lia]. subst g. unfold shadow_addr in Gs. rewrite Z.div_mul in Gs by lia.
assert (Ak : a / 8 = k) by lia. pose proof (Z.div_mod a 8 ltac:(lia)). pose proof (Z.mod_pos_bound a 8 ltac:(lia)). lia.
Qed.
(* fuzz_malloc's head: the first 16 bytes of a live block of at least 16 bytes, as the only user-poisoned range. *)
Lemma upoison_ok_one : forall ly S W mem md p n, AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) -> 16 <= req_size n ->
upoison_ok ly S [(p, 16)].
Proof.
intros ly S W mem md p n HAR Hb Hn. destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hb) as (P16 & _).
split; [|split; [constructor | exact I]]. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
split; [apply Z.mod_divide in P16 as [q Hq]; [|lia]; rewrite Hq; replace (q * 16) with ((q * 2) * 8) by lia; apply Z.mod_mul; lia|].
split; [lia|]. split; [reflexivity|]. exists p, n. split; [exact Hb|]. split; [lia|].
pose proof (Z.div_le_lower_bound (req_size n) 8 2 ltac:(lia) ltac:(lia)). lia.
Qed.
(* The stack holds no live block. *)
Lemma ARU_stack_not_block : forall ly S U W mem md a, ARU ly S U W mem md -> ly_stk_lo ly <= a < ly_stk_hi ly ->
forall p n, In (p, n) (ablocks B ly S) -> ~ (p <= a < p + req_size n).
Proof.
intros ly S U W mem md a H Ha p n Hb Hin. pose proof (ARU_AR _ _ _ _ _ _ H) as HAR.
destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md p n HAR Hb) as (_ & _ & PC & _).
pose proof (lo_stk_ceil ly (am_layout B ly S _ (proj1 HAR))) as SC. unfold ASAN_CEIL in SC. lia.
Qed.
Lemma in_ush_cons16 : forall h U s, in_ush ((h, 16) :: U) s = ((shadow_addr h <=? s) && (s <? shadow_addr h + 2)) || in_ush U s.
Proof. reflexivity. Qed.
(* The two shadow bytes of a 16-byte range disjoint from U are not user-poisoned by U. *)
Lemma ush16_out : forall h U s, h mod 8 = 0 ->
Forall (fun r => fst r mod 8 = 0 /\ snd r mod 8 = 0) U -> Forall (zdisjoint (h, 16)) U ->
shadow_addr h <= s < shadow_addr h + 2 -> in_ush U s = false.
Proof.
intros h U s H8 AL DJ Hs. destruct (in_ush U s) eqn:E; [|reflexivity]. exfalso.
apply in_ush_spec in E as (r & Hr & Hrs). destruct (proj1 (Forall_forall _ _) AL r Hr) as [A1 A2].
pose proof (proj1 (Forall_forall _ _) DJ r Hr) as D. unfold zdisjoint in D. cbn [fst snd] in D.
apply Z.mod_divide in H8 as [a Ha]; [|lia]. apply Z.mod_divide in A1 as [b Hb]; [|lia]. apply Z.mod_divide in A2 as [c Hc]; [|lia].
unfold shadow_addr in Hs, Hrs. rewrite Ha in Hs, D. rewrite Hb, Hc in Hrs, D. rewrite !Z.div_mul in Hs, Hrs by lia. lia.
Qed.
Lemma upoison_ok_cons16 : forall ly S h U, upoison_ok ly S ((h, 16) :: U) ->
h mod 8 = 0 /\ (exists p n, In (p, n) (ablocks B ly S) /\ p <= h /\ h + 16 <= p + 8 * (req_size n / 8)) /\
Forall (fun r => fst r mod 8 = 0 /\ snd r mod 8 = 0) U /\ Forall (zdisjoint (h, 16)) U /\ upoison_ok ly S U.
Proof.
intros ly S h U [F [DJ PW]]. apply Forall_cons_iff in F as [(H8 & _ & _ & BL) F].
split; [exact H8|]. split; [exact BL|]. split; [|split; [exact DJ | split; [exact F | exact PW]]].
eapply Forall_impl; [|exact F]. intros r (A1 & _ & A2 & _). exact (conj A1 A2).
Qed.
(* A whole user granule of a live block: the allocator's shadow byte is 0. *)
Lemma block_granule0 : forall ly S W mem md p n g, AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
g mod 8 = 0 -> p <= g -> g + 8 <= p + 8 * (req_size n / 8) -> aview segs (w_H W) mem (shadow_addr g) = Some 0.
Proof.
intros ly S W mem md p n g HAR Hb G8 Gp Gn.
destruct (al_shadow _ _ LAWS ly S W mem md p n HAR Hb) as [(P8 & N0 & BS) _].
pose proof (Z.div_le_mono (req_size n) (req_size n + 7) 8 ltac:(lia) ltac:(lia)) as DM.
apply Z.mod_divide in P8 as [a Ha]; [|lia]. apply Z.mod_divide in G8 as [b Hb8]; [|lia].
assert (I1 : (g - p) / 8 = b - a) by (rewrite Ha, Hb8; replace (b * 8 - a * 8) with ((b - a) * 8) by lia; apply Z.div_mul; lia).
assert (I2 : shadow_of_addr SHADOW_OFF p + (g - p) / 8 = shadow_addr g).
{ unfold shadow_of_addr, shadow_addr. rewrite I1, Ha, Hb8, !Z.div_mul by lia. lia. }
rewrite <- I2, BS by lia. destruct (Z.ltb_spec ((g - p) / 8) (req_size n / 8)); [reflexivity | lia].
Qed.
(* The low end of the shadow of a live block is below the stack. *)
Lemma block_shadow_low : forall ly S rd p n g, ARm B ly S rd -> In (p, n) (ablocks B ly S) -> p <= g < p + req_size n ->
SHADOW_OFF <= shadow_addr g < kHighMemBeg.
Proof.
intros ly S rd p n g M Hb Hg. destruct (ablock_ashadow ly S rd p n g M Hb Hg) as (v & Hv). exact (ashadow_low B ly S rd g v M Hv).
Qed.
Lemma stk_kHighMemBeg : forall ly S rd, ARm B ly S rd -> kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd.
Proof. intros ly S rd M. pose proof (lo_top ly (am_layout B ly S rd M)) as (_ & _ & _ & T4 & _ & _ & T7). split; [exact T7 | exact T4]. Qed.
(* __asan_poison_memory_region(h, 16) on whole granules of a live block, disjoint from U: if the run keeps the memory
   outside its stack window and the two shadow bytes, and makes those 0xf7, the head joins U. *)
Lemma ARU_poison_step : forall ly S U W mem md h mem1 md1 lo hi,
ARU ly S U W mem md -> upoison_ok ly S ((h, 16) :: U) ->
ly_stk_lo ly <= lo -> hi <= ly_stk_hi ly ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> ~ (shadow_addr h <= a < shadow_addr h + 2) ->
aview segs (w_H W) mem1 a = aview segs (w_H W) mem a) ->
(forall a, lo <= a < hi -> aview segs (w_H W) mem1 a <> None) ->
aview segs (w_H W) mem1 (shadow_addr h) = Some 247 -> aview segs (w_H W) mem1 (shadow_addr h + 1) = Some 247 ->
m_vmmaps md1 = m_vmmaps md -> m_vm_lazy md1 = m_vm_lazy md -> eager_used md1 = eager_used md ->
(forall a, in_band_rw a -> w_H W (w64 a) = true -> mem1 (w64 a) = mem (w64 a)) ->
ARU ly S ((h, 16) :: U) W mem1 md1.
Proof.
intros ly S U W mem md h mem1 md1 lo hi H OK' Hlo Hhi FR STK P0 P1 E1 E2 E3 HB.
pose proof H as (HAR & OK & PO). pose proof (proj1 HAR) as M.
destruct (upoison_ok_cons16 ly S h U OK') as (H8 & (p & n & Hb & Hp & Hn) & AL & DJ & _).
pose proof (Z.mul_div_le (req_size n) 8 ltac:(lia)) as RD.
pose proof (stk_kHighMemBeg ly S _ M) as [SK1 SK2].
pose proof (block_shadow_low ly S _ p n h M Hb ltac:(lia)) as [BL1 BL2].
assert (SH0 : forall j, 0 <= j < 2 -> aview segs (w_H W) (unpoison U mem) (shadow_addr h + j) = Some 0).
{ intros j Hj. replace (shadow_addr h + j) with (shadow_addr (h + 8 * j)).
  - apply (block_granule0 ly S W (unpoison U mem) md p n (h + 8 * j) HAR Hb); [|lia|lia].
    apply Z.mod_divide in H8 as [q Hq]; [|lia]. rewrite Hq. replace (q * 8 + 8 * j) with ((q + j) * 8) by lia. apply Z.mod_mul. lia.
  - unfold shadow_addr. apply Z.mod_divide in H8 as [q Hq]; [|lia]. rewrite Hq. replace (q * 8 + 8 * j) with ((q + j) * 8) by lia.
    rewrite !Z.div_mul by lia. lia. }
assert (USH : forall s, in_ush U s = true -> SHADOW_OFF <= s < kHighMemBeg).
{ intros s Hs. exact (proj2 (ush_facts ly S U W mem md s H Hs)). }
assert (OUT : forall a, shadow_addr h <= a < shadow_addr h + 2 -> in_ush U a = false) by (intros a Ha; exact (ush16_out h U a H8 AL DJ Ha)).
assert (IMG := al_img_env segs ly S md (am_layout B ly S _ M) (proj1 (proj2 HAR))).
split; [|split; [exact OK'|]].
- apply (al_frame _ _ LAWS ly S W (unpoison U mem) md (unpoison ((h, 16) :: U) mem1) md1 HAR); [| |exact E1|exact E2|exact E3|].
  + intros a Ha Hown.
    destruct (Z_lt_le_dec a (shadow_addr h)) as [A1|A1]; [|destruct (Z_lt_le_dec a (shadow_addr h + 2)) as [A2|A2]].
    3,1: destruct (Z_lt_le_dec a lo) as [L1|L1]; [|destruct (Z_lt_le_dec a hi) as [L2|L2]];
      [| exfalso; exact (ARU_stack ly S U W mem md a H ltac:(lia) Hown) |];
      (destruct (in_ush U a) eqn:Ei;
       [ apply aview_at; rewrite !unpoison_in; [reflexivity | rewrite (wz a Ha); exact Ei | rewrite (wz a Ha), in_ush_cons16, Ei, Bool.orb_true_r; reflexivity]
       | rewrite aview_unpoison_out, aview_unpoison_out; [apply FR; lia | rewrite (wz a Ha); exact Ei | rewrite (wz a Ha), in_ush_cons16, Ei, Bool.orb_false_r; apply andb_false_iff; lia ]]).
    destruct (w_H W (Z_to_bv 64 a)) eqn:Hh; [apply aview_hidden_same; exact Hh|].
    replace a with (shadow_addr h + (a - shadow_addr h)) at 2 by lia. rewrite SH0 by lia.
    rewrite (aview_vis_byte _ _ a (Z_to_bv 8 0) Hh); [reflexivity|].
    apply unpoison_in. rewrite (wz a Ha), in_ush_cons16. apply Bool.orb_true_intro. left. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  + intros a Hv. rewrite aview_mod in Hv |- *. assert (Ha : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
    set (a' := a mod 2 ^ 64) in *. clearbody a'.
    destruct (Z_lt_le_dec a' (shadow_addr h)) as [A1|A1]; [|destruct (Z_lt_le_dec a' (shadow_addr h + 2)) as [A2|A2]].
    2: { destruct (w_H W (Z_to_bv 64 a')) eqn:Hh; [rewrite (aview_hidden_same _ _ (unpoison U mem) a' Hh); exact Hv|].
         rewrite (aview_vis_byte _ _ a' (Z_to_bv 8 0) Hh); [discriminate|].
         apply unpoison_in. rewrite (wz a' Ha), in_ush_cons16. apply Bool.orb_true_intro. left. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
    all: destruct (Z_lt_le_dec a' lo) as [L1|L1]; [|destruct (Z_lt_le_dec a' hi) as [L2|L2]].
    all: destruct (in_ush U a') eqn:Ei.
    all: try (rewrite (aview_at _ (unpoison ((h, 16) :: U) mem1) (unpoison U mem) a'); [exact Hv | rewrite !unpoison_in;
               [reflexivity | rewrite (wz a' Ha); exact Ei | rewrite (wz a' Ha), in_ush_cons16, Ei, Bool.orb_true_r; reflexivity]]).
    all: try (exfalso; pose proof (USH a' Ei); lia).
    all: rewrite aview_unpoison_out by (rewrite (wz a' Ha), in_ush_cons16, Ei, Bool.orb_false_r; apply andb_false_iff; lia).
    all: try (apply STK; lia).
    all: rewrite aview_unpoison_out in Hv by (rewrite (wz a' Ha); exact Ei); rewrite FR by lia; exact Hv.
  + intros a Hb' Hh. unfold unpoison. rewrite in_ush_cons16.
    destruct ((shadow_addr h <=? bv_unsigned (w64 a)) && (bv_unsigned (w64 a) <? shadow_addr h + 2)) eqn:Ein.
    * exfalso. apply andb_prop in Ein as [Q1 Q2]. apply Z.leb_le in Q1. apply Z.ltb_lt in Q2.
      assert (Ha : 0 <= a < 2 ^ 64) by (unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Hb'; lia).
      unfold w64 in Q1, Q2, Hh. rewrite (wz a Ha) in Q1, Q2.
      pose proof (SH0 (a - shadow_addr h) ltac:(lia)) as Z0. replace (shadow_addr h + (a - shadow_addr h)) with a in Z0 by lia.
      rewrite (aview_band_hidden segs (w_H W) (unpoison U mem) a IMG Hb' Hh) in Z0. discriminate Z0.
    * cbn [orb]. destruct (in_ush U (bv_unsigned (w64 a))); [reflexivity | exact (HB a Hb' Hh)].
- intros s Hs. rewrite in_ush_cons16 in Hs. apply Bool.orb_true_iff in Hs as [Hs|Hs].
  + apply andb_prop in Hs as [Q1 Q2]. apply Z.leb_le in Q1. apply Z.ltb_lt in Q2.
    destruct (Z.eq_dec s (shadow_addr h)) as [->|NE]; [exact P0|]. replace s with (shadow_addr h + 1) by lia. exact P1.
  + pose proof (USH s Hs) as [U1 U2]. rewrite FR; [exact (PO s Hs) | clear - U1 U2; unfold SHADOW_OFF, kHighMemBeg in *; lia | lia |].
    intros Hr. rewrite (OUT s Hr) in Hs. discriminate Hs.
Qed.
(* __asan_unpoison_memory_region(h, 16) for a head in U: if the run keeps the memory outside its stack window and the
   two shadow bytes, and makes those 0, the head leaves U. *)
Lemma ARU_unpoison_step : forall ly S U W mem md h mem1 md1 lo hi,
ARU ly S ((h, 16) :: U) W mem md ->
ly_stk_lo ly <= lo -> hi <= ly_stk_hi ly ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> ~ (shadow_addr h <= a < shadow_addr h + 2) ->
aview segs (w_H W) mem1 a = aview segs (w_H W) mem a) ->
(forall a, lo <= a < hi -> aview segs (w_H W) mem1 a <> None) ->
aview segs (w_H W) mem1 (shadow_addr h) = Some 0 -> aview segs (w_H W) mem1 (shadow_addr h + 1) = Some 0 ->
m_vmmaps md1 = m_vmmaps md -> m_vm_lazy md1 = m_vm_lazy md -> eager_used md1 = eager_used md ->
(forall a, in_band_rw a -> w_H W (w64 a) = true -> mem1 (w64 a) = mem (w64 a)) ->
ARU ly S U W mem1 md1.
Proof.
intros ly S U W mem md h mem1 md1 lo hi H Hlo Hhi FR STK P0 P1 E1 E2 E3 HB.
pose proof H as (HAR & OK' & PO). pose proof (proj1 HAR) as M.
destruct (upoison_ok_cons16 ly S h U OK') as (H8 & (p & n & Hb & Hp & Hn) & AL & DJ & OK).
pose proof (stk_kHighMemBeg ly S _ M) as [SK1 SK2].
assert (USH : forall s, in_ush ((h, 16) :: U) s = true -> SHADOW_OFF <= s < kHighMemBeg).
{ intros s Hs. exact (proj2 (ush_facts ly S ((h, 16) :: U) W mem md s H Hs)). }
assert (OUT : forall a, shadow_addr h <= a < shadow_addr h + 2 -> in_ush U a = false) by (intros a Ha; exact (ush16_out h U a H8 AL DJ Ha)).
assert (INH : forall a, shadow_addr h <= a < shadow_addr h + 2 -> in_ush ((h, 16) :: U) a = true).
{ intros a Ha. rewrite in_ush_cons16. apply Bool.orb_true_intro. left. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
assert (M1 : forall j, 0 <= j < 2 -> aview segs (w_H W) mem1 (shadow_addr h + j) = Some 0).
{ intros j Hj. destruct (Z.eq_dec j 0) as [->|NE]; [rewrite Z.add_0_r; exact P0|]. replace j with 1 by lia. exact P1. }
assert (IMG := al_img_env segs ly S md (am_layout B ly S _ M) (proj1 (proj2 HAR))).
split; [|split; [exact OK|]].
- apply (al_frame _ _ LAWS ly S W (unpoison ((h, 16) :: U) mem) md (unpoison U mem1) md1 HAR); [| |exact E1|exact E2|exact E3|].
  + intros a Ha Hown.
    destruct (Z_lt_le_dec a (shadow_addr h)) as [A1|A1]; [|destruct (Z_lt_le_dec a (shadow_addr h + 2)) as [A2|A2]].
    3,1: destruct (Z_lt_le_dec a lo) as [L1|L1]; [|destruct (Z_lt_le_dec a hi) as [L2|L2]];
      [| exfalso; exact (ARU_stack ly S _ W mem md a H ltac:(lia) Hown) |];
      (destruct (in_ush U a) eqn:Ei;
       [ apply aview_at; rewrite !unpoison_in; [reflexivity | rewrite (wz a Ha), in_ush_cons16, Ei, Bool.orb_true_r; reflexivity | rewrite (wz a Ha); exact Ei]
       | rewrite aview_unpoison_out, aview_unpoison_out; [apply FR; lia | rewrite (wz a Ha), in_ush_cons16, Ei, Bool.orb_false_r; apply andb_false_iff; lia | rewrite (wz a Ha); exact Ei ]]).
    destruct (w_H W (Z_to_bv 64 a)) eqn:Hh; [apply aview_hidden_same; exact Hh|].
    rewrite aview_unpoison_out by (rewrite (wz a Ha); apply OUT; lia).
    replace a with (shadow_addr h + (a - shadow_addr h)) at 1 by lia. rewrite M1 by lia.
    rewrite (aview_vis_byte _ _ a (Z_to_bv 8 0) Hh); [reflexivity|].
    apply unpoison_in. rewrite (wz a Ha). apply INH. lia.
  + intros a Hv. rewrite aview_mod in Hv |- *. assert (Ha : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
    set (a' := a mod 2 ^ 64) in *. clearbody a'.
    destruct (Z_lt_le_dec a' (shadow_addr h)) as [A1|A1]; [|destruct (Z_lt_le_dec a' (shadow_addr h + 2)) as [A2|A2]].
    2: { rewrite aview_unpoison_out by (rewrite (wz a' Ha); apply OUT; lia).
         replace a' with (shadow_addr h + (a' - shadow_addr h)) by lia. rewrite M1 by lia. discriminate. }
    all: destruct (Z_lt_le_dec a' lo) as [L1|L1]; [|destruct (Z_lt_le_dec a' hi) as [L2|L2]].
    all: destruct (in_ush U a') eqn:Ei.
    all: try (rewrite (aview_at _ (unpoison U mem1) (unpoison ((h, 16) :: U) mem) a'); [exact Hv | rewrite !unpoison_in;
               [reflexivity | rewrite (wz a' Ha), in_ush_cons16, Ei, Bool.orb_true_r; reflexivity | rewrite (wz a' Ha); exact Ei]]).
    all: try (exfalso; assert (Ei' : in_ush ((h, 16) :: U) a' = true) by (rewrite in_ush_cons16, Ei, Bool.orb_true_r; reflexivity); pose proof (USH a' Ei'); lia).
    all: rewrite aview_unpoison_out by (rewrite (wz a' Ha); exact Ei).
    all: try (apply STK; lia).
    all: rewrite aview_unpoison_out in Hv by (rewrite (wz a' Ha), in_ush_cons16, Ei, Bool.orb_false_r; apply andb_false_iff; lia).
    all: rewrite FR by lia; exact Hv.
  + intros a Hb' Hh. unfold unpoison. rewrite in_ush_cons16.
    destruct ((shadow_addr h <=? bv_unsigned (w64 a)) && (bv_unsigned (w64 a) <? shadow_addr h + 2)) eqn:Ein.
    * exfalso. apply andb_prop in Ein as [Q1 Q2]. apply Z.leb_le in Q1. apply Z.ltb_lt in Q2.
      assert (Ha : 0 <= a < 2 ^ 64) by (unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Hb'; lia).
      unfold w64 in Q1, Q2, Hh. rewrite (wz a Ha) in Q1, Q2.
      pose proof (M1 (a - shadow_addr h) ltac:(lia)) as Z0. replace (shadow_addr h + (a - shadow_addr h)) with a in Z0 by lia.
      rewrite (aview_band_hidden segs (w_H W) mem1 a IMG Hb' Hh) in Z0. discriminate Z0.
    * cbn [orb]. destruct (in_ush U (bv_unsigned (w64 a))); [reflexivity | exact (HB a Hb' Hh)].
- intros s Hs. assert (Hs' : in_ush ((h, 16) :: U) s = true) by (rewrite in_ush_cons16, Hs, Bool.orb_true_r; reflexivity).
  pose proof (USH s Hs') as [U1 U2]. rewrite FR; [exact (PO s Hs') | clear - U1 U2; unfold SHADOW_OFF, kHighMemBeg in *; lia | lia |].
  intros Hr. rewrite (OUT s Hr) in Hs. discriminate Hs.
Qed.
End l.
