(* libreac/fuzz_boxreg, build asan-ubsan: twin of lib/A/Rt/StrncmpFmh.v (a working branch
   e23152c688f). It is the boxreg file that carries the same definitions as a Theorem Labs lane's FMH_Base.v, FMH_Rt.v and
   FMspec_str.v for the names a Theorem Labs lane's relocated strncmp proof uses (lib/B/FMstrncmp.v astrncmp_holds and the FM*
   files under it, from a working branch 445e498a469, relocated onto image B). Those three fm files are NOT
   relocated: they Require fm's program model; a Theorem Labs lane's 03:33Z ruling re-points their Requires to boxreg files
   carrying the same definitions. Here:
   - verbatim from FMH_Base.v at 445e498a469: ecall_pre_k (:156), cstr (:169), cstr_ok (:175), ecall_preU_k (:162),
     bytes_at (:183), with FMH_Base's local abbreviation rdW (:138); verbatim from FMH_Rt.v: rt_post_ro (:89),
     rt_post_roU (:97), astrncmp_realizes (:124). The text is the A twin's, word for word.
     Why ecall_pre_k / cstr_ok are not aliases of boxreg's frozen lib/B/Rt/StrncmpDefB.v abfm_ecall_pre_k /
     abfm_cstr_ok: StrncmpDefB writes fm's `alloc_ceiling` as `ASAN_CEIL` (StrncmpDefB.v:56 / :62), as A's StrncmpDef
     does. The two are equal by definition (YG0f.v:15), but lia treats them as different atoms, so fm's unchanged
     proof does not close over StrncmpDefB's text (on A: FMrt_pre.v:310, diagnostic build
     boxreg-strncmp build-20261029T044600Z.log). lib/B/Rt/StrncmpB.v proves StrncmpDefB's
     abstrncmp_realizes from astrncmp_holds by conversion (a Theorem Labs lane 04:46Z, option B).
   - the other fm names are aliases of StrncmpDefB's identical bodies (no second definition): PC_strncmp ->
     ABSTRNCMP_ENTRY (0x41458), STK_RT_STR, rom_viewN, rom_viewO, strn_eq. StrncmpDefB is Required, not Imported,
     and the aliases name it qualified, so no StrncmpDefB name is shadowed here or in the files that import this one.
   - FMupoison is -pa's shared, image-free lib/A/Rt/FMupoison.v (relocated whole from a Theorem Labs lane by a Theorem Labs lane,
     dc99a2ad20d), one text per module; it has no lib/B twin.
   - the five program-free helpers of FMspec_str.v FMstrncmp uses (nul_last, nul_last_cons, nul_last_tl,
     nth_error_map_nth, u8), verbatim with their proofs.
   No image numeral other than StrncmpDefB's entry.
   Requires: FMH_Base.v / FMH_Rt.v load Reusable/YI16 (FMstrncmp.v:206 names YI16.sink_head), so this file loads it
   too, without importing it. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YI04 YI00 YK06 YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YI16.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require Import FMupoison.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt Require StrncmpDefB.
Import ListNotations.
Open Scope Z_scope.

(* ---- FMH_Base / FMH_Rt names that are aliases of StrncmpDefB's identical bodies ---- *)
Notation PC_strncmp := StrncmpDefB.ABSTRNCMP_ENTRY (only parsing).
Notation STK_RT_STR := StrncmpDefB.ABFM_STK_RT_STR (only parsing).
Notation rom_viewN := StrncmpDefB.abfm_rom_viewN (only parsing).
Notation rom_viewO := StrncmpDefB.abfm_rom_viewO (only parsing).
Notation strn_eq := StrncmpDefB.abfm_strn_eq (only parsing).

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* ---- FMH_Base.v, verbatim ---- *)
Section c.
Variable segs : list Segment.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Definition ecall_pre_k (STK : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) : Prop :=
  ecall_pre segs B ly S W regs mem md /\ alloc_ceiling <= ly_stk_lo ly /\ ly_stk_lo ly + STK <= spZ regs /\
  (forall a, spZ regs - STK <= a < spZ regs -> apresent (w_H W) mem a).
Definition ecall_preU_k (STK : Z) (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world segs)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
  ecall_preU segs B ly S U W regs mem md /\ alloc_ceiling <= ly_stk_lo ly /\ ly_stk_lo ly + STK <= spZ regs /\
  (forall a, spZ regs - STK <= a < spZ regs -> apresent (w_H W) mem a).
Definition cstr (W : world segs) (mem : word -> option byte) (p : Z) (l : list Z) : Prop :=
  garr8 segs (rdW W mem) p (l ++ [0]) /\ Forall (fun c => c <> 0) l.
Definition cstr_ok (W : world segs) (mem : word -> option byte) (p : Z) (l : list Z) : Prop :=
  cstr W mem p l /\ 4096 <= p /\ p + Z.of_nat (length l) + 8 <= alloc_ceiling /\ Z.of_nat (length l) + 1 < 2 ^ 32 /\
  amem_range p (Z.of_nat (length l) + 8) /\
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF p (Z.of_nat (length l) + 1) /\
  shadow_hull_vis (aview segs (w_H W) mem) p (Z.of_nat (length l) + 1) /\
  (forall a, p + Z.of_nat (length l) < a < p + Z.of_nat (length l) - (p + Z.of_nat (length l)) mod 8 + 8 ->
     aview segs (w_H W) mem a <> None).
Definition bytes_at (W : world segs) (mem : word -> option byte) (p : Z) (l : list Z) : Prop :=
  garr8 segs (rdW W mem) p l.
End c.
(* ---- FMH_Rt.v, verbatim ---- *)
Section c.
Variable segs : list Segment.
Variable B : asyms.
Definition rt_post_ro (STK : Z) ly S W regs mem md (R : Z -> Prop) : world segs -> config -> Prop :=
  fun W' c' => W' = W /\ exists regs' mem' md' (v : Z),
    c' = cfg_at segs (raZ regs) regs' mem' md' /\
    AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
    getr regs' 10 = w64 v /\ 0 <= v < 2 ^ 64 /\ R v /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
    (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).
Definition rt_post_roU (STK : Z) ly S (U : list (Z * Z)) W regs mem md (R : Z -> Prop) : world segs -> config -> Prop :=
  fun W' c' => W' = W /\ exists regs' mem' md' (v : Z),
    c' = cfg_at segs (raZ regs) regs' mem' md' /\
    AR segs B ly S W (unpoison U mem') md' /\ upoisoned segs W mem' U /\
    aregs_preserved regs regs' /\ same_but_materialized md md' /\
    getr regs' 10 = w64 v /\ 0 <= v < 2 ^ 64 /\ R v /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
    (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).
Definition astrncmp_realizes (pc : Z) : Prop :=
  forall ly S W regs mem md x y n (l1 l2 : list Z),
  ecall_pre_k segs B STK_RT_STR ly S W regs mem md -> rom_viewN segs B W mem -> rom_viewO segs B W mem ->
  getr regs 10 = w64 x -> getr regs 11 = w64 y -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 63 ->
  cstr_ok segs W mem x l1 -> cstr_ok segs W mem y l2 ->
  SRr segs W (cfg_at segs pc regs mem md)
    (rt_post_ro STK_RT_STR ly S W regs mem md (fun v => v = 0 <-> strn_eq (Z.to_nat n) l1 l2)).
End c.
End b.

(* ---- FMspec_str.v's helpers, verbatim ---- *)
Definition nul_last (m : list Z) : Prop :=
  exists l, m = l ++ [0] /\ Forall (fun c => c <> 0) l /\ Forall (fun c => 0 <= c < 256) l.
Lemma nul_last_cons : forall x r, nul_last (x :: r) -> x = 0 -> r = [].
Proof.
  intros x r (l & Hm & Hnz & _) Hx. subst x.
  destruct l as [|a l]; cbn in Hm.
  - congruence.
  - exfalso. inversion Hnz as [|? ? Hz _]; subst. apply Hz. congruence.
Qed.
Lemma nul_last_tl : forall x r, nul_last (x :: r) -> x <> 0 -> nul_last r.
Proof.
  intros x r (l & Hm & Hnz & Hr) Hx.
  destruct l as [|a l]; cbn in Hm.
  - exfalso. apply Hx. congruence.
  - inversion Hnz as [|? ? _ Hnz']; subst. inversion Hr as [|? ? _ Hr']; subst.
    exists l. split; [congruence | split; [exact Hnz' | exact Hr']].
Qed.
Lemma nth_error_map_nth : forall (m : list Z) (i : nat),
  (i < length m)%nat -> nth_error (map (Z_to_bv 8) m) i = Some (Z_to_bv 8 (nth i m 0)).
Proof.
  intros m i Hi. rewrite nth_error_map.
  destruct (nth_error m i) as [v|] eqn:E.
  - cbn [option_map]. rewrite (nth_error_nth m i 0 E). reflexivity.
  - apply nth_error_None in E. lia.
Qed.
Lemma u8 : forall c, 0 <= c < 256 -> bv_unsigned (Z_to_bv 8 c) = c.
Proof.
  intros c Hc. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  apply Z.mod_small. lia.
Qed.
