(* Threads U through the donor allocator walks in lib/A: AF0w.v / AFij-AFk2 (malloc), AFfs.v / AFeq-AFhl (free), and the shared AFhn.v, AFi3.v, AFk5.v, AFkb-AFkz.v, AFl1.v (refill). This file: the transfer kit, the shared any-U statements and twins, the region lemmas. *)
(* Shared any-U allocator, within-budget units (cgif's EV_MAX 11,776, < 2 GiB per class); the cf form (fuzz_preset / fuzz_reply, YG0dcf.v) bridges to this. *)
(* Modified by Theorem Labs, 2026-10: the image-B port (fuzz_state.asan-ubsan) of lib/A/FSupoisonAllocR.v at c78cdbc32e3: each lib/A donor is its lib/B twin (AFxx -> YFxx, ABxx -> YBxx), every statement is over B's tfibsegs (lib/B/YB1v.v); offU_low / offU_high rest on the segs-generic low_off_ush / high_off_ush of lib/A/FSupoisonARXm.v (section 1, moved there from lib/A/FSupoisonARX.v), not on lib/A/FSupoisonIntrinR.v, whose two lemmas are stated over A's segments. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK04 YP0m YP09 YP0l YI04 YA0i YA0n YA0q YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s YG0q YG0t.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YF0x YFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YL0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoison FSupoisonU FSupoisonARXm.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require YFi3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module FSP := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoison.
Module FSU := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonU.
Module ARXm := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonARXm.

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1. Two readings of one memory. The machine runs on mem; AR holds of FSupoison.unpoison U mem. They differ only   *)
(*    at U's shadow bytes. offU U a: the byte at address a (taken mod 2^64, as a word is) is not one of them.        *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Definition offU (U : list (Z * Z)) (a : Z) : Prop := FSP.in_ush U (a mod 2 ^ 64) = false.

Lemma bvu_mod : forall a, bv_unsigned (Z_to_bv 64 a) = a mod 2 ^ 64.
Proof. intros a. rewrite Z_to_bv_unsigned. reflexivity. Qed.

Lemma unpoison_offU : forall U (m : word -> option byte) a, offU U a -> FSP.unpoison U m (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof. intros U m a H. apply FSP.unpoison_out. rewrite bvu_mod. exact H. Qed.

Lemma unpoison_offU_w : forall U (m : word -> option byte) (x : word), offU U (bv_unsigned x) -> FSP.unpoison U m x = m x.
Proof.
intros U m x H. apply FSP.unpoison_out. unfold offU in H. rewrite Z.mod_small in H; [exact H|]. apply u64_range.
Qed.

Lemma mbyte_unpoison : forall (H : word -> bool) U (m : word -> option byte) a, offU U a ->
  mbyte tfibsegs (mrestrict H (FSP.unpoison U m)) a = mbyte tfibsegs (mrestrict H m) a.
Proof. intros H U m a E. apply mbyte_mrestrict_same. apply unpoison_offU. exact E. Qed.

Lemma aview_unpoison : forall (H : word -> bool) U (m : word -> option byte) a, offU U a ->
  aview tfibsegs H (FSP.unpoison U m) a = aview tfibsegs H m a.
Proof. intros H U m a E. apply aview_same. apply unpoison_offU. exact E. Qed.

Lemma val_mem_of_unpoison : forall (H : word -> bool) U (m : word -> option byte) a (w : nat) v,
  (forall k, (k < w)%nat -> offU U (a + Z.of_nat k)) ->
  val_mem tfibsegs (mrestrict H (FSP.unpoison U m)) a w v -> val_mem tfibsegs (mrestrict H m) a w v.
Proof.
intros H U m a w v O V. apply (val_mem_frame H (FSP.unpoison U m) m a w v); [|exact V].
intros k Hk. symmetry. apply unpoison_offU. exact (O k Hk).
Qed.

Lemma val_mem_to_unpoison : forall (H : word -> bool) U (m : word -> option byte) a (w : nat) v,
  (forall k, (k < w)%nat -> offU U (a + Z.of_nat k)) ->
  val_mem tfibsegs (mrestrict H m) a w v -> val_mem tfibsegs (mrestrict H (FSP.unpoison U m)) a w v.
Proof.
intros H U m a w v O V. apply (val_mem_frame H m (FSP.unpoison U m) a w v); [|exact V].
intros k Hk. apply unpoison_offU. exact (O k Hk).
Qed.

(* Presence: unpoison only turns bytes into Some 0, so it never loses one. *)
Lemma apresent_to_unpoison : forall (H : word -> bool) U (m : word -> option byte) a,
  apresent H m a -> apresent H (FSP.unpoison U m) a.
Proof.
intros H U m a [Hh [b Hb]]. split; [exact Hh|]. unfold FSP.unpoison.
destruct (FSP.in_ush U (bv_unsigned (Z_to_bv 64 a))); [eexists; reflexivity | exists b; exact Hb].
Qed.

Lemma apresent_of_unpoison : forall (H : word -> bool) U (m : word -> option byte) a, offU U a ->
  apresent H (FSP.unpoison U m) a -> apresent H m a.
Proof.
intros H U m a O P. apply (apresent_same H (FSP.unpoison U m) m a); [|exact P]. symmetry. apply unpoison_offU. exact O.
Qed.

(* A symbolic state's regions whose bytes are all off U read the same in both memories. *)
Definition regions_offU (U : list (Z * Z)) (E : env) (rs : smem) : Prop :=
  forall r a, In r rs -> base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r -> offU U a.

Lemma mem_ok_unpoison_iff : forall U E (H : word -> bool) (m : word -> option byte) rs, regions_offU U E rs ->
  mem_ok tfibsegs E (mrestrict H (FSP.unpoison U m)) rs <-> mem_ok tfibsegs E (mrestrict H m) rs.
Proof.
intros U E H m rs O. split; intros M; (eapply YL0a.mem_ok_ext_same; [exact M|]); intros r x Hr Hx;
  unfold mrestrict; rewrite (unpoison_offU U m x (O r x Hr Hx)); reflexivity.
Qed.

Lemma st_ok_unpoison_iff : forall U E ss (H : word -> bool) regs pc (m : word -> option byte) rom,
  regions_offU U E (ss_mem ss) ->
  YP0l.st_ok tfibsegs E ss (restrict H (YK11.mkst regs pc (FSP.unpoison U m) rom)) <->
  YP0l.st_ok tfibsegs E ss (restrict H (YK11.mkst regs pc m rom)).
Proof.
intros U E ss H regs pc m rom O. unfold YP0l.st_ok, restrict, YK11.mkst.
cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem].
split; intros (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9);
  refine (conj X1 (conj X2 (conj X3 (conj X4 (conj X5 (conj X6 (conj X7 (conj _ X9))))))));
  apply (mem_ok_unpoison_iff U E H m _ O); exact X8.
Qed.

(* A frame-pointer chain is read from the stack only. *)
Lemma fpchain_ext : forall (l1 l2 : Z -> option Z) lo top ch bp,
  (forall a, lo <= a < top -> l1 a = l2 a) -> lo + 16 <= bp -> bp <= top ->
  fpchain l1 bp top ch -> fpchain l2 bp top ch.
Proof.
intros l1 l2 lo top ch. induction ch as [|[[fp ra] nfp] rest IH]; intros bp E Hlo Hhi H; cbn [fpchain] in *.
- destruct H as (r & Hr & Hb). exists r. rewrite <- E by lia. split; assumption.
- destruct H as (-> & A8 & L1 & L2 & R4 & HN). rewrite <- !E by lia.
  refine (conj eq_refl (conj A8 (conj L1 (conj L2 (conj R4 _))))).
  destruct (bad_next bp top nfp) eqn:BN; [exact HN|].
  unfold bad_next in BN. apply orb_false_iff in BN as [BN1 BN3]. apply orb_false_iff in BN1 as [BN1 BN2].
  apply Z.leb_gt in BN1. apply Z.leb_gt in BN2. apply (IH nfp E); [lia | lia | exact HN].
Qed.

Lemma rdword_ext : forall (r1 r2 : reader) a, (forall k, 0 <= k < 8 -> r1 (a + k) = r2 (a + k)) -> rdword r1 a = rdword r2 a.
Proof.
intros r1 r2 a E. unfold rdword.
rewrite <- (Z.add_0_r a) at 1 2. rewrite !E by lia. rewrite Z.add_0_r. reflexivity.
Qed.

Section r.
Variable B : asyms.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 2. Where U is not. U's bytes are shadow bytes of whole user granules of live blocks (FSupoison.ush_facts):       *)
(*    never application memory, never outside aowned, never the shadow of a granule outside every live block.       *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Lemma offU_low : forall ly S U W mem md a, FSP.ARU tfibsegs B ly S U W mem md -> 0 <= a < SHADOW_OFF -> offU U a.
Proof.
intros ly S U W mem md a H Ha. exact (ARXm.low_off_ush tfibsegs B ly S U W mem md a H Ha).
Qed.

Lemma offU_high : forall ly S U W mem md a, FSP.ARU tfibsegs B ly S U W mem md -> kHighMemBeg <= a < 2 ^ 64 -> offU U a.
Proof.
intros ly S U W mem md a H Ha. exact (ARXm.high_off_ush tfibsegs B ly S U W mem md a H Ha).
Qed.

Lemma offU_app : forall ly S U W mem md a, FSP.ARU tfibsegs B ly S U W mem md -> 0 <= a < 2 ^ 64 ->
  a < SHADOW_OFF \/ kHighMemBeg <= a -> offU U a.
Proof.
intros ly S U W mem md a H Ha [L|L]; [apply (offU_low ly S U W mem md a H) | apply (offU_high ly S U W mem md a H)]; lia.
Qed.

Lemma offU_not_owned : forall ly S U W mem md a, FSP.ARU tfibsegs B ly S U W mem md -> 0 <= a < 2 ^ 64 ->
  ~ aowned B ly S a -> offU U a.
Proof.
intros ly S U W mem md a H Ha Ho. unfold offU. rewrite Z.mod_small by lia.
destruct (FSP.in_ush U a) eqn:E; [|reflexivity]. exfalso. apply Ho. exact (proj1 (FSP.ush_facts tfibsegs B ly S U W mem md a H E)).
Qed.

(* A zone3 range (YF0x.zone3: below the image, between the image and the low shadow, or high) is off U. *)
Lemma offU_zone3 : forall ly S U W mem md x sz a, FSP.ARU tfibsegs B ly S U W mem md -> zone3 x sz ->
  x <= a < x + sz -> offU U a.
Proof.
intros ly S U W mem md x sz a H (Z1 & Z2 & Z3) Ha. pose proof (proj1 (@ASAN_CEIL_range _)) as CR.
apply (offU_app ly S U W mem md a H); unfold zone3cases, TFIB_IMG_LO, TFIB_IMG_END in Z3;
  unfold kLowShadowBeg, SHADOW_OFF, kHighMemBeg in *; lia.
Qed.

(* A seed whose regions all lie in application memory (below the shadow or at or above kHighMemBeg) is off U. *)
Definition app_ext (x : Z * Z) : Prop := 0 <= fst x /\ snd x <= 2 ^ 64 /\ (snd x <= SHADOW_OFF \/ kHighMemBeg <= fst x).
Lemma regions_offU_of_app : forall ly S U W mem md E rs, FSP.ARU tfibsegs B ly S U W mem md ->
  Forall app_ext (map (extent_of_region E) rs) -> regions_offU U E rs.
Proof.
intros ly S U W mem md E rs H F r a Hr Ha.
pose proof (proj1 (Forall_forall _ _) F (extent_of_region E r) (in_map _ _ _ Hr)) as X.
unfold app_ext, extent_of_region in X. cbn [fst snd] in X.
apply (offU_app ly S U W mem md a H); lia.
Qed.

Lemma offU_shadow_nonlive : forall ly S U W mem md g, FSP.ARU tfibsegs B ly S U W mem md -> 0 <= g < 2 ^ 64 ->
  (forall p n, In (p, n) (ablocks B ly S) -> ~ (p <= g < p + req_size n)) -> offU U (shadow_addr g).
Proof.
intros ly S U W mem md g H Hg NB. unfold offU. rewrite <- bvu_mod. exact (FSP.ARU_shadow_out_block tfibsegs B ly S U W mem md g H Hg NB).
Qed.

(* A byte the unpoisoned reading shows as a value other than 0 and 0xf7 is not one of U's (U's read 0 there when
   visible, and 0xf7 in both readings when hidden). *)
Lemma offU_nonzero : forall ly S U W mem md a v, FSP.ARU tfibsegs B ly S U W mem md -> 0 <= a < 2 ^ 64 ->
  aview tfibsegs (w_H W) (FSP.unpoison U mem) a = Some v -> v <> 0 -> v <> 247 -> offU U a.
Proof.
intros ly S U W mem md a v H Ha Hv Hnz Hn7. unfold offU. rewrite Z.mod_small by lia.
destruct (FSP.in_ush U a) eqn:E; [|reflexivity]. exfalso.
pose proof (FSP.ARU_poisoned tfibsegs B ly S U W mem md H a E) as P.
assert (Ew : FSP.in_ush U (bv_unsigned (Z_to_bv 64 a)) = true) by (rewrite bvu_mod, Z.mod_small by lia; exact E).
destruct (w_H W (Z_to_bv 64 a)) eqn:Hh.
- rewrite (FSP.aview_hidden_same tfibsegs (w_H W) (FSP.unpoison U mem) mem a Hh), P in Hv. injection Hv as Hv. lia.
- rewrite (FSP.aview_vis_byte tfibsegs (w_H W) (FSP.unpoison U mem) a (Z_to_bv 8 0) Hh (FSP.unpoison_in U mem _ Ew)) in Hv.
  injection Hv as Hv. apply Hnz. rewrite <- Hv. reflexivity.
Qed.

(* U's bytes are visible and present in the real memory: they read 0xf7 there, they lie in the shadow band (they are
   shadows of live granules), and a hidden or absent band byte reads None. *)
Lemma ush_present : forall ly S U W mem md s, FSP.ARU tfibsegs B ly S U W mem md -> FSP.in_ush U s = true ->
  apresent (w_H W) mem s.
Proof.
intros ly S U W mem md s H E. pose proof H as (HAR & OK & PO).
destruct (FSP.ush_granule B ly S U s OK E) as (g & p & n & Hb & G8 & Gs & Gp & Gn).
pose proof (Z.mul_div_le (req_size n) 8 ltac:(lia)) as RD.
destruct (FSP.ablock_chunk B ly S p n Hb) as (k & Hk & Hu & Hn).
pose proof (chunk_facts B ly S _ k (proj1 HAR) Hk) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & _).
assert (Happ : in_app g 8) by (unfold in_app in *; subst p n; lia).
pose proof (shadow_addr_band_rw g Happ) as Hband. rewrite Gs in Hband.
pose proof (PO s E) as P247.
pose proof (al_img_env tfibsegs ly S md (am_layout B ly S _ (proj1 HAR)) (proj1 (proj2 HAR))) as IMG.
destruct (w_H W (Z_to_bv 64 s)) eqn:Hh.
- exfalso. rewrite (aview_band_hidden tfibsegs (w_H W) mem s IMG Hband Hh) in P247. discriminate P247.
- split; [exact Hh|]. destruct (mem (Z_to_bv 64 s)) as [b|] eqn:Em; [exists b; reflexivity|]. exfalso.
  pose proof (aview_band_hidden tfibsegs (fun _ => true) mem s IMG Hband eq_refl) as R0.
  unfold aview, mbyte, mrestrict in P247, R0. rewrite Hh, Em in P247. cbv beta iota in P247, R0.
  rewrite R0 in P247. discriminate P247.
Qed.

Lemma some_of_unpoison : forall ly S U W mem md, FSP.ARU tfibsegs B ly S U W mem md ->
  forall w : word, FSP.unpoison U mem w <> None -> mem w <> None.
Proof.
intros ly S U W mem md H w Hw. destruct (FSP.in_ush U (bv_unsigned w)) eqn:E.
- destruct (ush_present ly S U W mem md _ H E) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate.
- rewrite (FSP.unpoison_out U mem w E) in Hw. exact Hw.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 3. The call forms. acall_preU / ecall_preU give ARU, and the stack window and chain on the REAL memory.          *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Lemma ARU_of_acall_preU : forall ly S U W regs mem md ch, FSU.acall_preU tfibsegs B ly S U W regs mem md ch ->
  FSP.ARU tfibsegs B ly S U W mem md.
Proof. intros ly S U W regs mem md ch (P & OK & PO). exact (conj (proj1 P) (conj OK PO)). Qed.

Lemma ARU_intro : forall ly S U W mem md, AR tfibsegs B ly S W (FSP.unpoison U mem) md -> FSP.upoison_ok B ly S U ->
  FSP.upoisoned tfibsegs W mem U -> FSP.ARU tfibsegs B ly S U W mem md.
Proof. intros ly S U W mem md H OK PO. exact (conj H (conj OK PO)). Qed.

(* A cell whose bytes are off U holds in one reading iff in the other. *)
Lemma cell_holds_unpoison : forall ly (H : word -> bool) U (m : word -> option byte) c,
  (forall k, 0 <= k <= Z.of_nat (c_w c) -> offU U (aeval B ly (c_at c) + k)) ->
  cell_holds B ly (aview tfibsegs H (FSP.unpoison U m)) c <-> cell_holds B ly (aview tfibsegs H m) c.
Proof.
intros ly H U m c O. unfold cell_holds. cbv zeta. destruct (c_val c) as [e|mask v].
- split; intros X k Hk; pose proof (O (Z.of_nat k) ltac:(lia)) as Ok;
    [rewrite <- (aview_unpoison H U m _ Ok) | rewrite (aview_unpoison H U m _ Ok)]; exact (X k Hk).
- pose proof (O 0 ltac:(lia)) as O0. rewrite Z.add_0_r in O0. rewrite (aview_unpoison H U m _ O0). reflexivity.
Qed.

Lemma Forall_cell_holds_unpoison : forall ly (H : word -> bool) U (m : word -> option byte) l,
  (forall c k, In c l -> 0 <= k <= Z.of_nat (c_w c) -> offU U (aeval B ly (c_at c) + k)) ->
  Forall (cell_holds B ly (aview tfibsegs H (FSP.unpoison U m))) l <-> Forall (cell_holds B ly (aview tfibsegs H m)) l.
Proof.
intros ly H U m l O. rewrite !Forall_forall. split; intros X c Hc.
- exact (proj1 (cell_holds_unpoison ly H U m c (fun k Hk => O c k Hc Hk)) (X c Hc)).
- exact (proj2 (cell_holds_unpoison ly H U m c (fun k Hk => O c k Hc Hk)) (X c Hc)).
Qed.

(* Where a live block lies: the allocated user area of its primary class, or a secondary extent (YG0s.cfacts). *)
Lemma ablock_in_user : forall ly S rd p n, ARm B ly S rd -> In (p, n) (ablocks B ly S) ->
  (exists c, 1 <= c <= 30 /\ region_base ly c <= p /\ p + req_size n <= region_base ly c + rg_alloc_user (reg S c) /\
     rg_alloc_user (reg S c) <= rg_mapped_user (reg S c) <= kFreeArrayOffset) \/
  (exists e, In e (sec_extents ly S) /\ fst e <= p /\ p + req_size n <= fst e + snd e).
Proof.
intros ly S rd p n M Hb. destruct (FSP.ablock_chunk B ly S p n Hb) as (k & Hk & Hu & Hn). subst p n.
pose proof (chunk_facts B ly S rd k M Hk) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & GG).
destruct (ck_beg k) as [|o|r o|c'' p'] eqn:Eb; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9).
  left. exists (prim_class o). split; [exact D1|]. rewrite C4. split; [lia|]. split; [lia | exact D9].
- destruct GG as (X0 & X1 & X2 & X3 & Hin & _). right. exists (ly_sec ly r, sec_map_size (ck_req k)).
  split; [exact Hin|]. cbn [fst snd]. rewrite C4. unfold kPage in *. lia.
Qed.

(* The stack window of a live stack pointer is above kHighMemBeg, so off U. *)
Lemma stack_offU : forall ly S U W mem md a, FSP.ARU tfibsegs B ly S U W mem md ->
  ly_stk_lo ly <= a < ly_stk_hi ly -> offU U a.
Proof.
intros ly S U W mem md a H Ha. pose proof (FSP.stk_kHighMemBeg B ly S _ (FSP.ARU_ARm tfibsegs B ly S U W mem md H)) as [K1 K2].
apply (offU_high ly S U W mem md a H). unfold kHighMemEnd in K2. lia.
Qed.

Lemma stack_present_real : forall ly S U W mem md lo hi, FSP.ARU tfibsegs B ly S U W mem md ->
  ly_stk_lo ly <= lo -> hi <= ly_stk_hi ly ->
  (forall a, lo <= a < hi -> apresent (w_H W) (FSP.unpoison U mem) a) -> forall a, lo <= a < hi -> apresent (w_H W) mem a.
Proof.
intros ly S U W mem md lo hi H L1 L2 P a Ha. apply (apresent_of_unpoison _ U); [|exact (P a Ha)].
apply (stack_offU ly S U W mem md a H). lia.
Qed.

Lemma chain_pre_real : forall ly S U W regs mem md ch, FSP.ARU tfibsegs B ly S U W mem md ->
  ly_stk_lo ly <= spZ regs ->
  chain_pre ly (aview tfibsegs (w_H W) (FSP.unpoison U mem)) regs ch -> chain_pre ly (aview tfibsegs (w_H W) mem) regs ch.
Proof.
intros ly S U W regs mem md ch H Hlo (R & C). split; [exact R|].
pose proof (FSP.ARU_ARm tfibsegs B ly S U W mem md H) as M.
pose proof (lo_top ly (am_layout B ly S _ M)) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
destruct (frame0_ok ly regs) eqn:F0; [|exact C].
destruct (bad_next (spZ regs) (ly_top ly) (s0Z regs)) eqn:BN; [exact C|]. destruct C as (C1 & C2). split; [exact C1|].
apply (fpchain_ext (rdword (aview tfibsegs (w_H W) (FSP.unpoison U mem))) _ (spZ regs) (ly_top ly) ch (s0Z regs)); [| lia | | exact C2].
- intros a Ha. apply rdword_ext. intros k Hk. apply aview_unpoison. apply (offU_high ly S U W mem md (a + k) H).
  unfold kHighMemBeg, kHighMemEnd in *. lia.
- unfold bad_next in BN. apply orb_false_iff in BN as [BN1 _]. apply orb_false_iff in BN1 as [_ BN2]. apply Z.leb_gt in BN2. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 4. The posts. U's ranges stay in live blocks and keep 0xf7 across a call that keeps those blocks and bytes.      *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Lemma upoison_ok_keep : forall ly S ly' S' U, FSP.upoison_ok B ly S U ->
  (forall r p n, In r U -> In (p, n) (ablocks B ly S) -> p <= fst r -> fst r + snd r <= p + 8 * (req_size n / 8) ->
     In (p, n) (ablocks B ly' S')) ->
  FSP.upoison_ok B ly' S' U.
Proof.
intros ly S ly' S' U [F PW] K. split; [|exact PW]. rewrite Forall_forall in F |- *. intros r Hr.
destruct (F r Hr) as (A & L & M & p & n & Hb & H1 & H2). refine (conj A (conj L (conj M _))).
exists p, n. split; [exact (K r p n Hr Hb H1 H2) | split; assumption].
Qed.

Lemma upoisoned_keep : forall U (W W' : world tfibsegs) mem mem', FSP.upoisoned tfibsegs W mem U ->
  (forall s, FSP.in_ush U s = true -> aview tfibsegs (w_H W') mem' s = aview tfibsegs (w_H W) mem s) ->
  FSP.upoisoned tfibsegs W' mem' U.
Proof. intros U W W' mem mem' P E s Hs. rewrite (E s Hs). exact (P s Hs). Qed.

(* U's bytes are aowned (FSupoison.ush_facts): a frame that keeps every byte outside aowned keeps them only in
   the unpoisoned reading if it says so; this is the frame of acall_post moved between the two readings. *)
Lemma frame_unpoison : forall ly S U W mem md (H' : word -> bool) (mem' : word -> option byte) (P : Z -> Prop),
  FSP.ARU tfibsegs B ly S U W mem md ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> P a -> aview tfibsegs H' mem' a = aview tfibsegs (w_H W) mem a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> P a ->
  aview tfibsegs H' (FSP.unpoison U mem') a = aview tfibsegs (w_H W) (FSP.unpoison U mem) a.
Proof.
intros ly S U W mem md H' mem' P H FR a Ha Ho HP. pose proof (offU_not_owned ly S U W mem md a H Ha Ho) as O.
rewrite !aview_unpoison by exact O. exact (FR a Ha Ho HP).
Qed.

Lemma acall_postU_intro : forall stk ly S U W regs mem md (E : Z -> Prop) ly' S' W' regs' mem' md',
  FSP.ARU tfibsegs B ly S U W mem md ->
  AR tfibsegs B ly' S' W' (FSP.unpoison U mem') md' -> layout_le (length (st_secs S)) ly ly' -> wle W W' ->
  aregs_preserved regs regs' -> same_io md md' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ aowned B ly' S' a -> ~ ascratch B stk regs a -> ~ E a ->
     aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a) ->
  (forall a, spZ regs - stk <= a < spZ regs -> apresent (w_H W') mem' a) ->
  FSP.upoison_ok B ly' S' U -> FSP.upoisoned tfibsegs W' mem' U ->
  FSU.acall_postU tfibsegs B stk ly S U W regs mem md E ly' S' W' regs' mem' md'.
Proof.
intros stk ly S U W regs mem md E ly' S' W' regs' mem' md' H HAR LL WL RP IO FR PR OK PO.
split; [|exact (conj OK PO)].
refine (conj HAR (conj LL (conj WL (conj RP (conj IO (conj _ _)))))).
- intros a Ha N1 N2 N3 N4.
  exact (frame_unpoison ly S U W mem md (w_H W') mem' (fun a => ~ aowned B ly' S' a /\ ~ ascratch B stk regs a /\ ~ E a) H
    (fun a Ha N1 HP => FR a Ha N1 (proj1 HP) (proj1 (proj2 HP)) (proj2 (proj2 HP))) a Ha N1 (conj N2 (conj N3 N4))).
- intros a Ha. apply apresent_to_unpoison. exact (PR a Ha).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 5. Shared state transport: AR_tick (lib/B/YFi3.v:102).                                                            *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Lemma ablocks_tick : forall ly S, ablocks B ly (set_nev (st_nev S + 1) S) = ablocks B ly S.
Proof. intros ly S. reflexivity. Qed.

Lemma ARU_tick : forall ly S U (W : world tfibsegs) mem md, FSP.ARU tfibsegs B ly S U W mem md -> aregime S ->
  FSP.ARU tfibsegs B ly (set_nev (st_nev S + 1) S) U W mem md.
Proof.
intros ly S U W mem md (HAR & OK & PO) Hev. split; [exact (YFi3.AR_tick B ly S W (FSP.unpoison U mem) md HAR Hev)|].
split; [|exact PO]. exact OK.
Qed.
End r.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 6. The refill contract (lib/B/YFl1.v:28-50) for any U: shared by malloc's miss paths and free's enqueue.          *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Section rf.
Variable B : asyms.
Definition refill_preU (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (c : Z) : Prop :=
  refill_pre B ly S W regs (FSP.unpoison U mem) md c /\ FSP.upoison_ok B ly S U /\ FSP.upoisoned tfibsegs W mem U.
(* The leaf's last conjunct is the frame on the RAW memory (route 1's ARU lift): a byte owned in neither state and off
   the refill's stack window keeps its value in mem itself, not only in FSupoison.unpoison U mem; ascratch is not
   excluded, so the errno cells are covered. *)
Definition refill_leafU (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (c : Z) (r : unit * astate) (W' : world tfibsegs) (c' : config) : Prop :=
  exists regs' mem' md',
    c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
    FSU.acall_postU tfibsegs B RSTACK ly S U W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
    getr regs' 10 = w64 (match pc_chunks (cache (snd r) c) with [] => 0 | _ => 1 end) /\
    (forall x : word, ~ aowned B ly S (bv_unsigned x) -> ~ aowned B ly (snd r) (bv_unsigned x) -> ~ (spZ regs - RSTACK <= bv_unsigned x < spZ regs) -> mem' x = mem x).
Definition tfib_refill_specU : Prop :=
  forall ly S U W regs mem md c,
    refill_preU ly S U W regs mem md c ->
    amreal tfibsegs (refill_tree c S) W (cfg_at tfibsegs A_Refill regs mem md) (refill_leafU ly S U W regs mem md c).
Lemma ARU_of_refill_preU : forall ly S U W regs mem md c, refill_preU ly S U W regs mem md c ->
  FSP.ARU tfibsegs B ly S U W mem md.
Proof. intros ly S U W regs mem md c (P & OK & PO). exact (conj (proj1 P) (conj OK PO)). Qed.
Lemma refill_preU_nil : forall ly S W regs mem md c, refill_pre B ly S W regs mem md c -> refill_preU ly S [] W regs mem md c.
Proof. intros ly S W regs mem md c H. split; [exact H|]. split; [split; [constructor | exact I]|]. intros s Hs. discriminate Hs. Qed.
Lemma tfib_refill_spec_of_U : tfib_refill_specU -> tfib_refill_spec B.
Proof.
intros HU ly S W regs mem md c Hpre.
eapply amreal_mono; [|exact (HU ly S [] W regs mem md c (refill_preU_nil _ _ _ _ _ _ _ Hpre))].
intros r W' c' (regs' & mem' & md' & E & (POST & _ & _) & R10 & _). exists regs', mem', md'. exact (conj E (conj POST R10)).
Qed.
End rf.
End k.
