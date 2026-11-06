(* The calls of __asan_poison_memory_region (h, 16) and __asan_unpoison_memory_region (h, 16) from a walk that holds
   the core's journal over the unpoisoned memory (FSW_K's U form): the contracts' raw-memory posts (lib/A/FSpoisonS.v
   apoison16_realizes / aunpoison16_realizes, a working branch 63931ee52ed, with the global presence
   conjunct of fix (a)) converted to FSW_K.fsw_intrin_atU's callee form over the unpoisoned memories, and the two call
   steps that put the caller's journal and ARU back together. Generic in B, in the entry pc and in the caller's FP.
   ONE COPY (kit layout, ruling a Theorem Labs lane 22:30Z): this file is the single writer of the conversion; fuzz_malloc /
   fuzz_free / fuzz_realloc import it. A walk passes the contract it holds for the call (a Theorem Labs lane's proved
   FSpoisonW.tfib_poison16 / tfib_unpoison16 at fs.asan's PC_poison / PC_unpoison) as the first argument.

   Port-from: the unpoisoned-view case split of lib/A/FSupoison.v (ARU_poison_step / ARU_unpoison_step: a head's two
   shadow bytes, U's shadow bytes, the rest; block_granule0 for a live block's granule) and FSupoisonU.v (in_ush_perm,
   AR_ext, ARU_perm: the head anywhere in U); the call steps compose FSW_K.fsw_ecall_preU_at and FSW_K.fsw_intrin_atU
   (a Theorem Labs lane). fsw_unpoison_view0 is a Theorem Labs lane's fsr_unpoison_view0, moved here as the one copy. No rename. No
   Section hypothesis, no axiom. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0s YP09 YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YM05 YG00 YG0a YG01 YG0l YG0f YG0v YG0n YG0d YG05 YG0q YCbq YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v FSupoison FSupoisonU FSpoisonS FSH_Gen FSH_Base FSW_K.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Unpoisoned views on fs.asan                                                                                       *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

(* a shadow byte lies in no loaded segment *)
Lemma fsw_shadow_not_img : forall s, SHADOW_OFF <= s < kHighMemBeg -> 0 <= s < 2 ^ 64 /\ ~ in_img tfibsegs s.
Proof.
intros s Hs. pose proof asan_consts as (_ & _ & C3 & _).
split; [unfold SHADOW_OFF in Hs; lia|].
intros Hi. pose proof (fs_segs_img s Hi). unfold FS_IMG_END, SHADOW_OFF in *. lia.
Qed.

(* a user-poisoned shadow byte reads 0 in the unpoisoned memory of every ARU state *)
Lemma fsw_unpoison_view0 : forall ly S U (W : world tfibsegs) mem md s,
  ARU tfibsegs B ly S U W mem md -> in_ush U s = true -> aview tfibsegs (w_H W) (unpoison U mem) s = Some 0.
Proof.
intros ly S U W mem md s H Hs.
pose proof (ush_facts tfibsegs B ly S U W mem md s H Hs) as (_ & L).
destruct (fsw_shadow_not_img s L) as [H64 NI].
destruct H as (_ & _ & PO). pose proof (PO s Hs) as P247.
revert P247. unfold aview, mbyte, mrestrict, unpoison. rewrite (wz s H64), Hs.
destruct (w_H W (Z_to_bv 64 s)).
- rewrite (seg_rom_none tfibsegs s H64 NI). discriminate.
- intros _. vm_compute. reflexivity.
Qed.

(* a byte outside every segment that reads Some is present *)
Lemma fsw_apresent_of_aview : forall (H : word -> bool) m a v, 0 <= a < 2 ^ 64 -> ~ in_img tfibsegs a ->
  aview tfibsegs H m a = Some v -> apresent H m a.
Proof.
intros H m a v Ha NI. unfold aview, mbyte, mrestrict, apresent.
destruct (H (Z_to_bv 64 a)).
- rewrite (seg_rom_none tfibsegs a Ha NI). discriminate.
- destruct (m (Z_to_bv 64 a)) as [b|].
  + intros _. split; [reflexivity | exists b; reflexivity].
  + rewrite (seg_rom_none tfibsegs a Ha NI). discriminate.
Qed.

(* ecall_preU with U permuted *)
Lemma fsw_ecall_preU_perm : forall ly S U U' (W : world tfibsegs) regs mem md, Permutation U U' ->
  ecall_preU tfibsegs B ly S U W regs mem md -> ecall_preU tfibsegs B ly S U' W regs mem md.
Proof.
intros ly S U U' W regs mem md P ((HAR & Hra & H16 & Hlo & Hhi & Hpres & Hgp & Htp) & OK & PO).
split; [|split; [exact (upoison_ok_perm B ly S U U' P OK)|]].
- split; [exact (AR_ext tfibsegs B LAWS ly S W (unpoison U mem) (unpoison U' mem) md HAR
    (fun w => eq_sym (unpoison_perm U U' mem w P)))|].
  split; [exact Hra|]. split; [exact H16|]. split; [exact Hlo|]. split; [exact Hhi|]. split; [|split; [exact Hgp | exact Htp]].
  intros a Ha. destruct (Hpres a Ha) as [Hh [b Hb]]. split; [exact Hh|]. exists b.
  rewrite <- (unpoison_perm U U' mem _ P). exact Hb.
- intros s Hs. apply PO. rewrite (in_ush_perm U U' s P). exact Hs.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The posts                                                                                                         *)
(* ---------------------------------------------------------------------------------------------------------------- *)

(* the two shadow bytes of a 16-byte head *)
Lemma fsw_head_shadow_dec : forall h a, (shadow_addr h <= a < shadow_addr h + 2) \/ ~ (shadow_addr h <= a < shadow_addr h + 2).
Proof. intros h a. lia. Qed.
Lemma fsw_in_ush16_in : forall h U s, shadow_addr h <= s < shadow_addr h + 2 -> in_ush ((h, 16) :: U) s = true.
Proof.
intros h U s Hs. rewrite in_ush_cons16.
destruct (Z.leb_spec (shadow_addr h) s); destruct (Z.ltb_spec s (shadow_addr h + 2)); cbn; try reflexivity; lia.
Qed.
Lemma fsw_in_ush16_out : forall h U s, ~ (shadow_addr h <= s < shadow_addr h + 2) ->
  in_ush ((h, 16) :: U) s = in_ush U s.
Proof.
intros h U s Hs. rewrite in_ush_cons16.
destruct (Z.leb_spec (shadow_addr h) s); destruct (Z.ltb_spec s (shadow_addr h + 2)); cbn; try reflexivity; lia.
Qed.

(* __asan_poison_memory_region (h, 16): the head joins U, at any position U' of the result; fsw_intrin_atU's callee
   form with Wr the call's window *)
Lemma fsw_poison16_post : forall ly S U U' (W : world tfibsegs) regs mem md h W' c',
  ARU tfibsegs B ly S U W mem md -> upoison_ok B ly S ((h, 16) :: U) -> Permutation ((h, 16) :: U) U' ->
  (W' = W /\ exists regs' mem' md',
     c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
     ARU tfibsegs B ly S ((h, 16) :: U) W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
     (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - PO_WIN <= a < spZ regs) -> ~ (shadow_addr h <= a < shadow_addr h + 2) ->
        aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
     (forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (w_H W) mem' a) /\
     (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)) ->
  W' = W /\ exists regs' mem' md',
    c' = mkCfg (mkst regs' (YK11.getr regs 1) mem' (seg_rom tfibsegs)) md' /\
    ARU tfibsegs B ly S U' W mem' md' /\ same_but_materialized md md' /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - PO_WIN <= a < spZ regs) ->
       aview tfibsegs (w_H W) (unpoison U' mem') a = aview tfibsegs (w_H W) (unpoison U mem) a) /\
    (forall a, apresent (w_H W) (unpoison U mem) a -> apresent (w_H W) (unpoison U' mem') a) /\
    aregs_preserved regs regs'.
Proof.
intros ly S U U' W regs mem md h W' c' HARU OK1 P (-> & regs' & mem' & md' & Ec & HARU' & HP & Hsame & Hfr & _ & Hpres).
destruct (upoison_ok_cons16 B ly S h U OK1) as (H8 & (p & n & Hb & Hp & Hn) & _).
split; [reflexivity|]. exists regs', mem', md'.
split; [rewrite Ec; unfold cfg_at, raZ, YG0d.w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [exact (FSupoisonU.ARU_perm tfibsegs B LAWS ly S _ U' W mem' md' P HARU')|].
split; [exact Hsame|]. split; [|split; [|exact HP]].
- intros a Ha Hw.
  rewrite (FSupoison.aview_at tfibsegs _ (unpoison U' mem') (unpoison ((h, 16) :: U) mem') a
    (eq_sym (unpoison_perm _ _ mem' _ P))).
  destruct (fsw_head_shadow_dec h a) as [Hin|Hout].
  + rewrite (fsw_unpoison_view0 ly S ((h, 16) :: U) W mem' md' a HARU' (fsw_in_ush16_in h U a Hin)).
    assert (E8 : shadow_addr (h + 8) = shadow_addr h + 1).
    { unfold shadow_addr. apply Z.mod_divide in H8 as [x Hx]; [|lia]. subst h.
      replace (x * 8 + 8) with ((x + 1) * 8) by lia. rewrite !Z.div_mul by lia. lia. }
    assert (a = shadow_addr h \/ a = shadow_addr (h + 8)) as [-> | ->] by lia.
    * symmetry. exact (block_granule0 tfibsegs B LAWS ly S W (unpoison U mem) md p n h (proj1 HARU) Hb H8 Hp ltac:(lia)).
    * symmetry. exact (block_granule0 tfibsegs B LAWS ly S W (unpoison U mem) md p n (h + 8) (proj1 HARU) Hb
        ltac:(rewrite Z.add_mod, H8 by lia; reflexivity) ltac:(lia) ltac:(lia)).
  + destruct (in_ush U a) eqn:EU.
    * rewrite (fsw_unpoison_view0 ly S ((h, 16) :: U) W mem' md' a HARU' ltac:(rewrite (fsw_in_ush16_out h U a Hout); exact EU)).
      rewrite (fsw_unpoison_view0 ly S U W mem md a HARU EU). reflexivity.
    * rewrite (aview_unpoison_out tfibsegs _ ((h, 16) :: U) mem' a
          ltac:(rewrite (wz a Ha), (fsw_in_ush16_out h U a Hout); exact EU)),
        (aview_unpoison_out tfibsegs _ U mem a ltac:(rewrite (wz a Ha); exact EU)).
      exact (Hfr a Ha Hw Hout).
- intros a Hpa.
  assert (K : apresent (w_H W) (unpoison ((h, 16) :: U) mem') a).
  { destruct Hpa as [Hh [bb Hbb]]. split; [exact Hh|]. unfold unpoison in Hbb |- *.
    destruct (in_ush ((h, 16) :: U) (bv_unsigned (Z_to_bv 64 a))) eqn:E1; [eexists; reflexivity|].
    assert (EU : in_ush U (bv_unsigned (Z_to_bv 64 a)) = false).
    { destruct (fsw_head_shadow_dec h (bv_unsigned (Z_to_bv 64 a))) as [Hin|Hout];
        [rewrite (fsw_in_ush16_in h U _ Hin) in E1; discriminate E1|].
      rewrite (fsw_in_ush16_out h U _ Hout) in E1. exact E1. }
    rewrite EU in Hbb. destruct (Hpres a (conj Hh (ex_intro _ bb Hbb))) as [_ [b' Hb']]. exists b'. exact Hb'. }
  destruct K as [Hh [bb Hbb]]. split; [exact Hh|]. exists bb. rewrite <- (unpoison_perm _ _ mem' _ P). exact Hbb.
Qed.

(* __asan_unpoison_memory_region (h, 16) for the head anywhere in U (U1 ++ (h, 16) :: U2): the head leaves U *)
Lemma fsw_unpoison16_post : forall ly S U1 U2 (W : world tfibsegs) regs mem md h W' c',
  ARU tfibsegs B ly S (U1 ++ (h, 16) :: U2) W mem md ->
  (W' = W /\ exists regs' mem' md',
     c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
     ARU tfibsegs B ly S (U1 ++ U2) W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
     aview tfibsegs (w_H W) mem' (shadow_addr h) = Some 0 /\ aview tfibsegs (w_H W) mem' (shadow_addr h + 1) = Some 0 /\
     (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - PO_WIN <= a < spZ regs) -> ~ (shadow_addr h <= a < shadow_addr h + 2) ->
        aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
     (forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (w_H W) mem' a) /\
     (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)) ->
  W' = W /\ exists regs' mem' md',
    c' = mkCfg (mkst regs' (YK11.getr regs 1) mem' (seg_rom tfibsegs)) md' /\
    ARU tfibsegs B ly S (U1 ++ U2) W mem' md' /\ same_but_materialized md md' /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - PO_WIN <= a < spZ regs) ->
       aview tfibsegs (w_H W) (unpoison (U1 ++ U2) mem') a =
       aview tfibsegs (w_H W) (unpoison (U1 ++ (h, 16) :: U2) mem) a) /\
    (forall a, apresent (w_H W) (unpoison (U1 ++ (h, 16) :: U2) mem) a -> apresent (w_H W) (unpoison (U1 ++ U2) mem') a) /\
    aregs_preserved regs regs'.
Proof.
intros ly S U1 U2 W regs mem md h W' c' HARU
  (-> & regs' & mem' & md' & Ec & HARU' & HP & Hsame & Z0 & Z1 & Hfr & _ & Hpres).
assert (PU : Permutation (U1 ++ (h, 16) :: U2) ((h, 16) :: U1 ++ U2)) by (symmetry; apply Permutation_middle).
assert (EU : forall s, in_ush (U1 ++ (h, 16) :: U2) s = in_ush ((h, 16) :: U1 ++ U2) s)
  by (intros s; exact (in_ush_perm _ _ s PU)).
pose proof (FSupoisonU.ARU_perm tfibsegs B LAWS ly S _ _ W mem md PU HARU) as HARUf.
destruct (upoison_ok_cons16 B ly S h (U1 ++ U2) (proj1 (proj2 HARUf))) as (H8 & _ & AL & DJ & _).
assert (OUT : forall s, shadow_addr h <= s < shadow_addr h + 2 -> in_ush (U1 ++ U2) s = false)
  by (intros s Hs; exact (ush16_out h (U1 ++ U2) s H8 AL DJ Hs)).
assert (INh : forall s, shadow_addr h <= s < shadow_addr h + 2 -> in_ush (U1 ++ (h, 16) :: U2) s = true)
  by (intros s Hs; rewrite EU; exact (fsw_in_ush16_in h _ s Hs)).
assert (HS : forall s, shadow_addr h <= s < shadow_addr h + 2 -> aview tfibsegs (w_H W) mem' s = Some 0).
{ intros s Hs. assert (s = shadow_addr h \/ s = shadow_addr h + 1) as [-> | ->] by lia; assumption. }
split; [reflexivity|]. exists regs', mem', md'.
split; [rewrite Ec; unfold cfg_at, raZ, YG0d.w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [exact HARU'|]. split; [exact Hsame|]. split; [|split; [|exact HP]].
- intros a Ha Hw. destruct (fsw_head_shadow_dec h a) as [Hin|Hout].
  + rewrite (aview_unpoison_out tfibsegs _ _ _ a ltac:(rewrite (wz a Ha); exact (OUT a Hin))).
    rewrite (HS a Hin). symmetry. exact (fsw_unpoison_view0 ly S _ W mem md a HARU (INh a Hin)).
  + destruct (in_ush (U1 ++ U2) a) eqn:E2.
    * assert (E1 : in_ush (U1 ++ (h, 16) :: U2) a = true) by (rewrite EU, (fsw_in_ush16_out h _ a Hout); exact E2).
      rewrite (fsw_unpoison_view0 ly S _ W mem' md' a HARU' E2), (fsw_unpoison_view0 ly S _ W mem md a HARU E1).
      reflexivity.
    * assert (E1 : in_ush (U1 ++ (h, 16) :: U2) a = false) by (rewrite EU, (fsw_in_ush16_out h _ a Hout); exact E2).
      rewrite (aview_unpoison_out tfibsegs _ (U1 ++ U2) mem' a ltac:(rewrite (wz a Ha); exact E2)),
        (aview_unpoison_out tfibsegs _ (U1 ++ (h, 16) :: U2) mem a ltac:(rewrite (wz a Ha); exact E1)).
      exact (Hfr a Ha Hw Hout).
- intros a [Hh [b Hb]]. split; [exact Hh|]. unfold unpoison in Hb |- *.
  set (s := bv_unsigned (Z_to_bv 64 a)) in *.
  destruct (in_ush (U1 ++ U2) s) eqn:E2; [eexists; reflexivity|].
  destruct (fsw_head_shadow_dec h s) as [Hin|Hout].
  + assert (Hs : 0 <= s < 2 ^ 64 /\ ~ in_img tfibsegs s)
      by exact (fsw_shadow_not_img s (proj2 (ush_facts tfibsegs B ly S _ W mem md s HARU (INh s Hin)))).
    destruct (fsw_apresent_of_aview (w_H W) mem' s 0 (proj1 Hs) (proj2 Hs) (HS s Hin)) as [_ [b' Hb']].
    exists b'. subst s. rewrite Z_to_bv_bv_unsigned in Hb'. exact Hb'.
  + assert (E1 : in_ush (U1 ++ (h, 16) :: U2) s = false) by (rewrite EU, (fsw_in_ush16_out h _ s Hout); exact E2).
    rewrite E1 in Hb. destruct (Hpres a (conj Hh (ex_intro _ b Hb))) as [_ [b' Hb']]. exists b'. exact Hb'.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The two call steps: the caller's journal over the unpoisoned memory (FSW_K's U form) carried over the call, and   *)
(* the caller's frame above the call's sp kept byte for byte (the resume lemmas' keep premise, FSW_rres)            *)
(* ---------------------------------------------------------------------------------------------------------------- *)

(* two equal readings are equal bytes *)
Lemma fsw_mbyte_of_aview : forall (H : word -> bool) (m m' : word -> option byte) a,
  aview tfibsegs H m' a = aview tfibsegs H m a -> mbyte tfibsegs (mrestrict H m') a = mbyte tfibsegs (mrestrict H m) a.
Proof.
intros H m m' a E. unfold aview in E.
destruct (mbyte tfibsegs (mrestrict H m') a) as [b'|], (mbyte tfibsegs (mrestrict H m) a) as [b|];
  cbn in E; try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* a frame on the unpoisoned readings keeps the machine's stack bytes outside the callee's window *)
Lemma fsw_keep_stack : forall ly S U U' (W : world tfibsegs) mem mem' md md' (Wr : Z -> Prop) lo hi,
  ARU tfibsegs B ly S U W mem md -> ARU tfibsegs B ly S U' W mem' md' -> kHighMemBeg <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> ~ Wr a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview tfibsegs (w_H W) (unpoison U' mem') a = aview tfibsegs (w_H W) (unpoison U mem) a) ->
  forall a, lo <= a < hi -> mbyte tfibsegs (mrestrict (w_H W) mem') a = mbyte tfibsegs (mrestrict (w_H W) mem) a.
Proof.
intros ly S U U' W mem mem' md md' Wr lo hi H H' Hlo Hhi HW Hfr a Ha.
pose proof asan_consts as (_ & _ & C3 & _).
apply fsw_mbyte_of_aview.
rewrite <- (fsw_aview_unpoison_high B ly S U' W mem' md' a H' ltac:(lia)),
  <- (fsw_aview_unpoison_high B ly S U W mem md a H ltac:(lia)).
exact (Hfr a ltac:(lia) (HW a Ha)).
Qed.

(* __asan_poison_memory_region (h, 16): the head joins U, at any position U' of the result *)
Lemma fsw_poison16_atU : forall pc, apoison16_realizes tfibsegs B pc ->
  forall STK sp0 FP ly S W0 mem md own lyc Sc U U' (W : world tfibsegs) memT mdc k regsT (o : Z) h p n,
  ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison U memT) mdc k ->
  ARU tfibsegs B lyc Sc U W memT mdc ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
  YK0s.ret_ok (YK11.getr regsT 1) -> YK11.getr regsT 3 = w64 (as_gp B) -> YK11.getr regsT 4 = w64 (as_tp B) ->
  YK11.getr regsT 10 = w64 h -> YK11.getr regsT 11 = w64 16 ->
  upoison_ok B lyc Sc ((h, 16) :: U) -> Permutation ((h, 16) :: U) U' ->
  In (p, n) (ablocks B lyc Sc) -> p <= h -> h + 16 < p + req_size n ->
  SRr tfibsegs W (cfg_at tfibsegs pc regsT memT mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 (YK11.getr regsT 1) mem2 (seg_rom tfibsegs)) md2 /\
       ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison U' mem2) md2 k /\
       ARU tfibsegs B lyc Sc U' W mem2 md2 /\ aregs_preserved regsT regs2 /\
       (forall a, spZ regsT <= a < sp0 ->
          mbyte tfibsegs (mrestrict (w_H W) mem2) a = mbyte tfibsegs (mrestrict (w_H W) memT) a) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - PO_WIN <= a < spZ regsT) ->
          aview tfibsegs (w_H W) (unpoison U' mem2) a = aview tfibsegs (w_H W) (unpoison U memT) a)).
Proof.
intros pc PO STK sp0 FP ly S W0 mem md own lyc Sc U U' W memT mdc k regsT o h p n HJ HARU Hsp Hal Hneg Hbud Hra Hgp Htp
  Ha0 Ha1 OK1 P Hb Hp Hn.
pose proof (fsw_ecall_preU_at B STK sp0 FP ly S W0 mem md own lyc Sc U W memT mdc k regsT o HJ HARU Hsp Hal Hneg Hbud
  Hra Hgp Htp) as HPRE.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & _ & C3 & _).
assert (ESTACK = 4096) as Hes by reflexivity.
(* the call's 64-byte window is below the caller's sp inside its stack budget: the stack arm of the write premise *)
eapply (fsw_intrin_atU B STK sp0 FP ly S W0 mem md own lyc Sc U W memT mdc k U'
  (fun a => spZ regsT - PO_WIN <= a < spZ regsT) (YK11.getr regsT 1) _
  (fun regs' mem' _ => aregs_preserved regsT regs' /\
     (forall a, spZ regsT <= a < sp0 ->
        mbyte tfibsegs (mrestrict (w_H W) mem') a = mbyte tfibsegs (mrestrict (w_H W) memT) a) /\
     (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - PO_WIN <= a < spZ regsT) ->
        aview tfibsegs (w_H W) (unpoison U' mem') a = aview tfibsegs (w_H W) (unpoison U memT) a)) HJ).
all: first
  [ solve [ eapply SRr_mono;
            first
              [ solve [exact (PO lyc Sc U W regsT memT mdc h p n HPRE Ha0 Ha1 OK1 Hb Hp Hn)]
              | solve [intros W' c' _ Hpost;
                       destruct (fsw_poison16_post lyc Sc U U' W regsT memT mdc h W' c' HARU OK1 P Hpost)
                         as (-> & regs2 & mem2 & md2 & Ec & HARU2 & Hsame & Hfr & Hpres & HP2);
                       split; [reflexivity|]; exists regs2, mem2, md2;
                       split; [exact Ec|]; split; [exact HARU2|]; split; [exact Hsame|];
                       split; [exact Hfr|]; split; [exact Hpres|]; split; [exact HP2|];
                       split; [exact (fsw_keep_stack lyc Sc U U' W memT mem2 mdc md2
                         (fun a => spZ regsT - PO_WIN <= a < spZ regsT) (spZ regsT) sp0 HARU HARU2
                         ltac:(lia) ltac:(lia) ltac:(intros a Ha Hw; cbv beta in Hw; unfold PO_WIN in Hw; lia) Hfr)|];
                       exact Hfr] ] ]
  | solve [ intros a Ha; cbv beta in Ha; unfold awr_byte, awr_byte0; left; left;
            unfold PO_WIN in Ha; rewrite Hsp in Ha; lia ] ].
Qed.

(* __asan_unpoison_memory_region (h, 16): the head leaves U from any position *)
Lemma fsw_unpoison16_atU : forall pc, aunpoison16_realizes tfibsegs B pc ->
  forall STK sp0 FP ly S W0 mem md own lyc Sc U1 U2 (W : world tfibsegs) memT mdc k regsT (o : Z) h p n,
  ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison (U1 ++ (h, 16) :: U2) memT) mdc k ->
  ARU tfibsegs B lyc Sc (U1 ++ (h, 16) :: U2) W memT mdc ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
  YK0s.ret_ok (YK11.getr regsT 1) -> YK11.getr regsT 3 = w64 (as_gp B) -> YK11.getr regsT 4 = w64 (as_tp B) ->
  YK11.getr regsT 10 = w64 h -> YK11.getr regsT 11 = w64 16 ->
  In (p, n) (ablocks B lyc Sc) -> p <= h -> h + 16 < p + req_size n ->
  SRr tfibsegs W (cfg_at tfibsegs pc regsT memT mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 (YK11.getr regsT 1) mem2 (seg_rom tfibsegs)) md2 /\
       ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison (U1 ++ U2) mem2) md2 k /\
       ARU tfibsegs B lyc Sc (U1 ++ U2) W mem2 md2 /\ aregs_preserved regsT regs2 /\
       (forall a, spZ regsT <= a < sp0 ->
          mbyte tfibsegs (mrestrict (w_H W) mem2) a = mbyte tfibsegs (mrestrict (w_H W) memT) a) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - PO_WIN <= a < spZ regsT) ->
          aview tfibsegs (w_H W) (unpoison (U1 ++ U2) mem2) a =
          aview tfibsegs (w_H W) (unpoison (U1 ++ (h, 16) :: U2) memT) a)).
Proof.
intros pc UPO STK sp0 FP ly S W0 mem md own lyc Sc U1 U2 W memT mdc k regsT o h p n HJ HARU Hsp Hal Hneg Hbud Hra
  Hgp Htp Ha0 Ha1 Hb Hp Hn.
pose proof (fsw_ecall_preU_at B STK sp0 FP ly S W0 mem md own lyc Sc _ W memT mdc k regsT o HJ HARU Hsp Hal Hneg Hbud
  Hra Hgp Htp) as HPRE.
apply (fsw_ecall_preU_perm lyc Sc _ ((h, 16) :: U1 ++ U2) W regsT memT mdc
  ltac:(symmetry; apply Permutation_middle)) in HPRE.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & _ & C3 & _).
assert (ESTACK = 4096) as Hes by reflexivity.
eapply (fsw_intrin_atU B STK sp0 FP ly S W0 mem md own lyc Sc _ W memT mdc k (U1 ++ U2)
  (fun a => spZ regsT - PO_WIN <= a < spZ regsT) (YK11.getr regsT 1) _
  (fun regs' mem' _ => aregs_preserved regsT regs' /\
     (forall a, spZ regsT <= a < sp0 ->
        mbyte tfibsegs (mrestrict (w_H W) mem') a = mbyte tfibsegs (mrestrict (w_H W) memT) a) /\
     (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - PO_WIN <= a < spZ regsT) ->
        aview tfibsegs (w_H W) (unpoison (U1 ++ U2) mem') a =
        aview tfibsegs (w_H W) (unpoison (U1 ++ (h, 16) :: U2) memT) a)) HJ).
all: first
  [ solve [ eapply SRr_mono;
            first
              [ solve [exact (UPO lyc Sc (U1 ++ U2) W regsT memT mdc h p n HPRE Ha0 Ha1 Hb Hp Hn)]
              | solve [intros W' c' _ Hpost;
                       destruct (fsw_unpoison16_post lyc Sc U1 U2 W regsT memT mdc h W' c' HARU Hpost)
                         as (-> & regs2 & mem2 & md2 & Ec & HARU2 & Hsame & Hfr & Hpres & HP2);
                       split; [reflexivity|]; exists regs2, mem2, md2;
                       split; [exact Ec|]; split; [exact HARU2|]; split; [exact Hsame|];
                       split; [exact Hfr|]; split; [exact Hpres|]; split; [exact HP2|];
                       split; [exact (fsw_keep_stack lyc Sc _ (U1 ++ U2) W memT mem2 mdc md2
                         (fun a => spZ regsT - PO_WIN <= a < spZ regsT) (spZ regsT) sp0 HARU HARU2
                         ltac:(lia) ltac:(lia) ltac:(intros a Ha Hw; cbv beta in Hw; unfold PO_WIN in Hw; lia) Hfr)|];
                       exact Hfr] ] ]
  | solve [ intros a Ha; cbv beta in Ha; unfold awr_byte, awr_byte0; left; left;
            unfold PO_WIN in Ha; rewrite Hsp in Ha; lia ] ].
Qed.
End t.
