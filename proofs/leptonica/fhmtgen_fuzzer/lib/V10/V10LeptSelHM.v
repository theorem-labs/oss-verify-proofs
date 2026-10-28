(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 LeptRecs LeptSlots LeptSel.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10LeptStderr V10LeptBase.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10CL7a.
Import V10CL7a.V10LeptSel_iface.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10_code_fhFG.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10CL8a.
Import V10CL8a.V10LeptSelSegs.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10LeptSelCreate V10LeptSelBrick.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoom10.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section SelHM.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V10Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition HMF (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
  wbytes (wbytes (wbytes m (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
                 (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
         (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)).

Definition hmcells (M : word -> option byte) (s : Z) (ret s0v s1v : word) : Prop :=
  rdn SEGS M (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) /\
  rdn SEGS M (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) /\
  rdn SEGS M (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v).

Lemma hmcells_HMF : forall m s ret regs, (32 <= s)%Z -> (s < 2 ^ 64)%Z -> hmcells (HMF m s ret regs) s ret (getr regs 8) (getr regs 9).
Proof. intros m s ret regs Hs Hs64. unfold hmcells, HMF. repeat split; rdn_chain. Qed.

Lemma hmcells_FRM : forall C M M' s ret s0v s1v, Cok C -> FRM C (s - 32) M M' -> (c_top C - LSTK <= s - 32)%Z -> (s <= c_top C)%Z ->
  hmcells M s ret s0v s1v -> hmcells M' s ret s0v s1v.
Proof.
  intros C M M' s ret s0v s1v CK F Hlo Hhi (C1 & C2 & C3). pose proof CK as [T1 T2 T3 T4 T5]. unfold hmcells.
  rewrite !(FRM_rdn16 C (s - 32) M M' _ _ CK F) by lia. repeat split; assumption.
Qed.

Section SegsH.
Variable rom : word -> option byte.

  Lemma hm_sA : forall regs m (s : Z) (ret : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x27be8 : word) m rom) (mkst regs' (0x26e30 : word) (HMF m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 1 = Z_to_bv 64 0x27c04 /\ getr regs' 10 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 2; 8]%list) regs regs'.
  Proof.
    intros regs m s ret Hs Hs64 SOK H2 H1 H10. eexists. split.
    - zv F_27aec D_27aec (Z_to_bv 64 (s - 32)).
      stepST F_27af0 D_27af0 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_27af4 D_27af4 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_27af8 D_27af8 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      sn F_27afc D_27afc.
      stepb_ft F_27b00 D_27b00 ltac:(condZ).
      sn F_27b04 D_27b04.
      unfold HMF. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma hm_sB : forall regs m (sela : Z),
    (1 <= sela < 2 ^ 64)%Z -> getr regs 10 = Z_to_bv 64 sela ->
    exists regs',
      msteps SEGS (mkst regs (0x27c04 : word) m rom) (mkst regs' (0x27c0c : word) m rom)
      /\ getr regs' 8 = Z_to_bv 64 sela /\ regs_agree (fun r => In r [8]%list) regs regs'.
  Proof.
    intros regs m sela Hs H10. eexists. split.
    - sn F_27b08 D_27b08. stepb_ft F_27b0c D_27b0c ltac:(condZ). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma hm_sZ : forall regs m (s sela : Z) (ret s0v s1v : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> hmcells m s ret s0v s1v ->
    getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 8 = Z_to_bv 64 sela ->
    exists regs',
      msteps SEGS (mkst regs (0x28260 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 sela /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10]%list) regs regs'.
  Proof.
    intros regs m s sela ret s0v s1v Hs Hs64 Hret (C1 & C2 & C3) H2 H8. eexists. split.
    - sn F_28164 D_28164.
      stepLD8 F_28168 D_28168 ret. stepLD8 F_2816c D_2816c s0v. stepLD8 F_28170 D_28170 s1v.
      zv F_28174 D_28174 (Z_to_bv 64 s).
      stepret F_28178 D_28178 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End SegsH.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[local] Definition hm_rest : list (bv 5) := [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Definition hminv (C : lctx) (A : AS) (m : word -> option byte) (md : Model) (s : Z) (regs : bvmap 5 word) (kR bR : Z)
                 (sela arr k c : Z) (Ak : AS) (mk : word -> option byte) (vmk : VmMaps) (rk : bvmap 5 word) (sels : Z -> Z) (vs : Z -> selv) : Prop :=
  let T := alloc_top (c_vm C) in
  W C Ak mk (with_vmmaps vmk md) /\ POSTM C A s m mk /\ hmcells mk s (getr regs 1) (getr regs 8) (getr regs 9) /\
  sela_at T Ak mk sela arr k sels vs hm_name /\
  (forall i, (0 <= i < k)%Z -> v_sy (vs i) = nth (Z.to_nat i) hm_sy 0%Z /\ v_sx (vs i) = nth (Z.to_nat i) hm_sx 0%Z) /\
  sela_off A sela arr k sels vs /\ sela_off (c_A0 C) sela arr k sels vs /\ sela_only A Ak sela arr k sels vs /\
  aroom Ak vmk (kR - c) (bR - c * RB10_small) /\
  getr rk 2 = Z_to_bv 64 (s - 32) /\ getr rk 8 = Z_to_bv 64 sela /\ (forall x, In x hm_rest -> getr rk x = getr regs x).

(* [comment removed for export] *)
Definition hmrs (C : lctx) (Ak : AS) (mk : word -> option byte) (md : Model) (s : Z) (regs : bvmap 5 word) (sela sel : Z) (v : selv)
                (A1 : AS) (m1 : word -> option byte) (vm1 : VmMaps) (r1 : bvmap 5 word) : Prop :=
  let T := alloc_top (c_vm C) in
  W C A1 m1 (with_vmmaps vm1 md) /\ POSTM C Ak (s - 32) mk m1 /\ sub_live Ak A1 /\
  sel_at T A1 m1 sel v /\ sel_off Ak sel v /\ sel_off (c_A0 C) sel v /\ sel_only Ak A1 sel v /\
  getr r1 2 = Z_to_bv 64 (s - 32) /\ getr r1 8 = Z_to_bv 64 sela /\ (forall x, In x hm_rest -> getr r1 x = getr regs x).

Lemma hm_rest_agree : forall (P : reg -> Prop) r r' regs, regs_agree P r r' -> (forall x, In x hm_rest -> ~ P x) ->
  (forall x, In x hm_rest -> getr r x = getr regs x) -> (forall x, In x hm_rest -> getr r' x = getr regs x).
Proof. intros P r r' regs AG NP RR x Hx. rewrite (AG x (NP x Hx)). exact (RR x Hx). Qed.

Lemma hm_rest_cs : forall r r' regs, cs_kept r r' -> (forall x, In x hm_rest -> getr r x = getr regs x) -> (forall x, In x hm_rest -> getr r' x = getr regs x).
Proof.
  intros r r' regs CS RR x Hx. rewrite <- (RR x Hx). unfold hm_rest in Hx. cbn [In] in Hx.
  repeat (destruct Hx as [<-|Hx]; [first [ exact (CS _ cs3) | exact (CS _ cs4) | exact (CS _ cs18) | exact (CS _ cs19) | exact (CS _ cs20) | exact (CS _ cs21)
                                         | exact (CS _ cs22) | exact (CS _ cs23) | exact (CS _ cs24) | exact (CS _ cs25) | exact (CS _ cs26) | exact (CS _ cs27) ]|]).
  destruct Hx.
Qed.

Ltac notin_rest := let x := fresh in let Hx := fresh in let HH := fresh in
  intros x Hx HH; unfold hm_rest in Hx; cbn [In] in Hx, HH;
  repeat (destruct Hx as [<-|Hx]; [repeat (destruct HH as [HH|HH]; [apply (f_equal bv_unsigned) in HH; cbv in HH; discriminate HH|]); exact HH|]); exact Hx.

(* [comment removed for export] *)
Lemma hm_brick_W : forall C A m md (s : Z) regs (kR bR sela arr k c : Z) Ak mk vmk rk sels vs (h w cy cx ty RET : Z) (pca : word) r' (S : TSet),
  Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + SELAHM_STACK <= s)%Z -> (s <= c_top C)%Z -> getr regs 4 = Z_to_bv 64 0x45480 ->
  hminv C A m md s regs kR bR sela arr k c Ak mk vmk rk sels vs ->
  msteps SEGS (mkst rk pca mk al_rom) (mkst r' (0x274cc : word) mk al_rom) ->
  getr r' 1 = Z_to_bv 64 RET -> ret_ok (Z_to_bv 64 RET) ->
  getr r' 10 = Z_to_bv 64 h -> getr r' 11 = Z_to_bv 64 w -> getr r' 12 = Z_to_bv 64 cy -> getr r' 13 = Z_to_bv 64 cx -> getr r' 14 = Z_to_bv 64 ty ->
  regs_agree (fun r => In r [1; 10; 11; 12; 13; 14]%list) rk r' ->
  (1 <= w <= 500)%Z -> (1 <= h <= 250)%Z -> (0 <= ty <= 2)%Z -> (0 <= cy < 2 ^ 31)%Z -> (0 <= cx < 2 ^ 31)%Z ->
  (c + (2 + h) <= kR)%Z -> ((c + (2 + h)) * RB10_small <= bR)%Z ->
  (forall A1 m1 vm1 r1 (sel arrd : Z) (rows : Z -> Z),
     hmrs C Ak mk md s regs sela sel (SELV h w cy cx arrd 0 rows) A1 m1 vm1 r1 -> getr r1 10 = Z_to_bv 64 sel ->
     aroom A1 vm1 (kR - (c + (2 + h))) (bR - (c + (2 + h)) * RB10_small) ->
     realizes SEGS (mkCfg (mkst r1 (Z_to_bv 64 RET) m1 al_rom) (with_vmmaps vm1 md)) S) ->
  realizes SEGS (mkCfg (mkst rk pca mk al_rom) (with_vmmaps vmk md)) S.
Proof.
  intros C A m md s regs kR bR sela arr k c Ak mk vmk rk sels vs h w cy cx ty RET pca r' S CK Hs16 Hlo Hhi H4
         (HW & PM & CE & SLA & SHP & SOA & SO0 & SON & HRM & R2 & R8 & RR) RUN Q1 Hret Q10 Q11 Q12 Q13 Q14 AG Hw Hh Hty Hcy Hcx HK1 HB1 HK.
  unfold SELAHM_STACK in Hlo.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
  assert (Q2 : getr r' 2 = Z_to_bv 64 (s - 32)) by (rewrite (AG 2) by notin_lit; exact R2).
  assert (Q4 : getr r' 4 = Z_to_bv 64 0x45480) by (rewrite (AG 4) by notin_lit; rewrite (RR 4%bv) by (unfold hm_rest; in_lit); exact H4).
  assert (HRM' : aroom Ak (m_vmmaps (with_vmmaps vmk md)) (kR - c) (bR - c * RB10_small)) by (rewrite with_vmmaps_vmmaps; exact HRM).
  apply (selCreateBrick_W C Ak mk _ r' (s - 32) h w cy cx ty (Z_to_bv 64 RET) S CK HW Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(lia) ltac:(lia) Q1 Hret Q4 Q10 Q11 Q12 Q13 Q14 Hw Hh Hty Hcy Hcx (kR - c)%Z (bR - c * RB10_small)%Z HRM' ltac:(lia) ltac:(lia)).
  intros A1 m1 vm1 r1 sel arrd rows HW1 CS1 PM1 R10 SA1 SO1 SO01 SN1 HRM1. rewrite with_vmmaps_twice in HW1 |- *.
  apply (HK A1 m1 vm1 r1 sel arrd rows); [| exact R10 |].
  - split; [exact HW1|]. split; [exact PM1|].
    split.
    { intros q kq Lq. rewrite (SN1 q); [exact Lq|]. intros p Hp ->. rewrite (SO1 p Hp) in Lq. discriminate. }
    split; [exact SA1|]. split; [exact SO1|]. split; [exact SO01|]. split; [exact SN1|].
    split; [rewrite (CS1 2%bv cs2); exact Q2|].
    split; [rewrite (CS1 8%bv cs8); rewrite (AG 8) by notin_lit; exact R8|].
    apply (hm_rest_cs r' r1 regs CS1). apply (hm_rest_agree _ rk r' regs AG); [notin_rest | exact RR].
  - replace (kR - (c + (2 + h)))%Z with (kR - c - (2 + h))%Z by lia.
    replace (bR - (c + (2 + h)) * RB10_small)%Z with (bR - c * RB10_small - (2 + h) * RB10_small)%Z by lia. exact HRM1.
Qed.

(* [comment removed for export] *)
Lemma hm_set_W : forall C Ak mk md (s : Z) regs (sela sel : Z) (v : selv) A1 m1 vm1 r1 (row col ty RET : Z) (pca : word) r' (S : TSet),
  Cok C -> (c_top C - LSTK + SELAHM_STACK <= s)%Z -> (s <= c_top C)%Z ->
  hmrs C Ak mk md s regs sela sel v A1 m1 vm1 r1 ->
  msteps SEGS (mkst r1 pca m1 al_rom) (mkst r' (0x2766c : word) m1 al_rom) ->
  getr r' 1 = Z_to_bv 64 RET -> ret_ok (Z_to_bv 64 RET) ->
  getr r' 10 = Z_to_bv 64 sel -> getr r' 9 = Z_to_bv 64 sel -> getr r' 11 = Z_to_bv 64 row -> getr r' 12 = Z_to_bv 64 col -> getr r' 13 = Z_to_bv 64 ty ->
  getr r' 2 = getr r1 2 -> getr r' 8 = getr r1 8 -> (forall x, In x hm_rest -> getr r' x = getr r1 x) ->
  (0 <= row < v_sy v)%Z -> (0 <= col < v_sx v)%Z -> (0 <= ty <= 2)%Z ->
  (forall m2 r2, hmrs C Ak mk md s regs sela sel v A1 m2 vm1 r2 -> getr r2 9 = Z_to_bv 64 sel ->
     realizes SEGS (mkCfg (mkst r2 (Z_to_bv 64 RET) m2 al_rom) (with_vmmaps vm1 md)) S) ->
  realizes SEGS (mkCfg (mkst r1 pca m1 al_rom) (with_vmmaps vm1 md)) S.
Proof.
  intros C Ak mk md s regs sela sel v A1 m1 vm1 r1 row col ty RET pca r' S CK Hlo Hhi
         (HW & PM & SUB & SA & SO & SO0 & SN & R2 & R8 & RR) RUN Q1 Hret Q10 Q9 Q11 Q12 Q13 E2 E8 ER Hrow Hcol Hty HK.
  unfold SELAHM_STACK in Hlo.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
  apply (selSetElement_W C Ak A1 m1 mk _ r' (s - 32) sel row col ty v (Z_to_bv 64 RET) S CK HW PM SUB ltac:(lia) SA SO SO0 Hrow Hcol Hty Q1 Hret Q10 Q11 Q12 Q13).
  intros m2 r2 HW2 PM2 SA2 FR2 AG2 R10.
  apply (HK m2 r2).
  - split; [exact HW2|]. split; [exact PM2|]. split; [exact SUB|]. split; [exact SA2|]. split; [exact SO|]. split; [exact SO0|]. split; [exact SN|].
    split; [rewrite (AG2 2) by notin_lit; rewrite E2; exact R2|].
    split; [rewrite (AG2 8) by notin_lit; rewrite E8; exact R8|].
    apply (hm_rest_agree _ r' r2 regs AG2); [notin_rest|]. intros x Hx. rewrite (ER x Hx). exact (RR x Hx).
  - rewrite (AG2 9) by notin_lit. exact Q9.
Qed.

Lemma sela_only_sub : forall (A Ak : AS) sela arr k sels vs, sela_off A sela arr k sels vs -> sela_only A Ak sela arr k sels vs -> sub_live A Ak.
Proof. intros A Ak sela arr k sels vs SO SN q n Lq. rewrite (SN q); [exact Lq|]. intros p Hp ->. rewrite (SO p Hp) in Lq. discriminate. Qed.

Lemma live_none_sub : forall (X Y : AS) p, sub_live X Y -> live Y p = None -> live X p = None.
Proof. intros X Y p SUB H. destruct (live X p) as [n|] eqn:E; [|reflexivity]. rewrite (SUB _ _ E) in H. discriminate. Qed.

(* [comment removed for export] *)
Lemma hm_add_W : forall C A m md (s : Z) regs (kR bR sela arr k c : Z) Ak mk vmk rk sels vs (sel h w cy cx arrd : Z) (rows : Z -> Z) A1 m1 vm1 r1
                        (src p RET : Z) (bs wd : list byte) (pca : word) r' (S : TSet),
  Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + SELAHM_STACK <= s)%Z -> (s <= c_top C)%Z -> getr regs 4 = Z_to_bv 64 0x45480 ->
  hminv C A m md s regs kR bR sela arr k c Ak mk vmk rk sels vs -> (0 <= k < 50)%Z ->
  hmrs C Ak mk md s regs sela sel (SELV h w cy cx arrd 0 rows) A1 m1 vm1 r1 ->
  aroom A1 vm1 (kR - (c + (2 + h))) (bR - (c + (2 + h)) * RB10_small) -> (c + (2 + h) + 1 <= kR)%Z -> ((c + (2 + h) + 1) * RB10_small <= bR)%Z ->
  msteps SEGS (mkst r1 pca m1 al_rom) (mkst r' (0x277b4 : word) m1 al_rom) ->
  getr r' 1 = Z_to_bv 64 RET -> ret_ok (Z_to_bv 64 RET) ->
  getr r' 10 = Z_to_bv 64 sela -> getr r' 11 = Z_to_bv 64 sel -> getr r' 12 = Z_to_bv 64 src -> getr r' 13 = Z_to_bv 64 0 ->
  getr r' 2 = getr r1 2 -> (forall x, In x hm_rest -> getr r' x = getr r1 x) -> getr r' 8 = getr r1 8 ->
  h = nth (Z.to_nat k) hm_sy 0%Z -> w = nth (Z.to_nat k) hm_sx 0%Z -> bs = hm_name k ->
  (0x10000 <= src)%Z -> (src + Z.of_nat (length bs) + 16 <= 0x2b000)%Z -> (1 <= Z.of_nat (length bs) <= 2027)%Z ->
  rdn SEGS (fun _ => None) (Z_to_bv 64 src) (Datatypes.S (length bs)) = Some (bs ++ [Z_to_bv 8 0]) -> Forall (fun b => b <> Z_to_bv 8 0) bs ->
  (1 <= p <= 7)%Z -> ((src + p) mod 8 = 0)%Z -> (p <= Z.of_nat (length bs))%Z ->
  rdn SEGS (fun _ => None) (Z_to_bv 64 (src + p)) 8 = Some wd -> strlen_stop (Z_to_bv 64 (bytes_le_to_Z wd)) ->
  (forall A2 m2 vm2 r2 sels' vs', hminv C A m md s regs kR bR sela arr (k + 1) (c + (3 + h)) A2 m2 vm2 r2 sels' vs' ->
     realizes SEGS (mkCfg (mkst r2 (Z_to_bv 64 RET) m2 al_rom) (with_vmmaps vm2 md)) S) ->
  realizes SEGS (mkCfg (mkst r1 pca m1 al_rom) (with_vmmaps vm1 md)) S.
Proof.
  intros C A m md s regs kR bR sela arr k c Ak mk vmk rk sels vs sel h w cy cx arrd rows A1 m1 vm1 r1 src p RET bs wd pca r' S CK Hs16 Hlo Hhi H4
         (HW & PM & CE & SLA & SHP & SOA & SO0 & SON & HRM & _ & _ & _) Hk
         (HW1 & PM1 & SUB & SA1 & SO1 & SO01 & SN1 & R2 & R8 & RR) HRM1 HK1 HB1 RUN Q1 Hret Q10 Q11 Q12 Q13 E2 ER E8 Eh Ew Ebs
         Hsrc0 Hsrc1 Hlen Rlit NZ Hp Hal Hpl Rwd STOP HK.
  unfold SELAHM_STACK, CALLOC_STACK, ALLOC_STACK in Hlo. set (v := SELV h w cy cx arrd 0 rows) in *.
  pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN |].
  pose proof (sela_only_sub A Ak _ _ _ _ _ SOA SON) as SUBA.
  assert (SUBA1 : sub_live A A1) by (eapply sub_live_trans; eassumption).
  pose proof (sela_at_keep _ Ak A1 mk m1 _ _ _ _ _ _ AT SLA SUB (proj2 PM1)) as SLA1.
  assert (Q2 : getr r' 2 = Z_to_bv 64 (s - 32)) by (rewrite E2; exact R2).
  assert (Q4 : getr r' 4 = Z_to_bv 64 0x45480) by (rewrite (ER 4%bv) by (unfold hm_rest; in_lit); rewrite (RR 4%bv) by (unfold hm_rest; in_lit); exact H4).
  assert (HRM1' : aroom A1 (m_vmmaps (with_vmmaps vm1 md)) (kR - (c + (2 + h))) (bR - (c + (2 + h)) * RB10_small)) by (rewrite with_vmmaps_vmmaps; exact HRM1).
  pose proof (sel_off_sub A Ak sel v SUBA SO1) as SOA1.
  assert (NB : forall q, sel_blk sel v q -> q <> sela /\ q <> arr /\ forall i p', (0 <= i < k)%Z -> seln_blk (sels i) (vs i) p' -> p' <> q).
  { intros q Hq. pose proof (SO1 q Hq) as Lq. pose proof SLA as (_ & _ & Lsa & _ & _ & Lar & _).
    split; [intros ->; rewrite Lsa in Lq; discriminate|]. split; [intros ->; rewrite Lar in Lq; discriminate|].
    intros i p' Hi Hp' ->. destruct (sela_blk_live _ Ak mk sela arr k sels vs hm_name i q SLA Hi Hp') as (n & Ln & _). rewrite Ln in Lq. discriminate. }
  apply (selaAddSel_W C A A1 m1 _ r' (s - 32) sela arr k sel src p sels vs hm_name v bs wd (Z_to_bv 64 RET) S CK HW1 SUBA1 Q2
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia) Q1 Hret Q4 Q10 Q11 Q12 Q13 SLA1 Hk SA1 eq_refl
           (SOA sela (or_introl eq_refl)) (SOA arr (or_intror (or_introl eq_refl))) (SOA1 sel (or_introl eq_refl))
           (SO0 sela (or_introl eq_refl)) (SO0 arr (or_intror (or_introl eq_refl))) (SO01 sel (or_introl eq_refl))
           NB Hsrc0 Hsrc1 Hlen Rlit NZ Hp Hal Hpl Rwd STOP _ _ HRM1' ltac:(lia) ltac:(lia)).
  intros A2 m2 vm2 r2 name HW2 CS2 PM2 R10 SLA2 LnA1 Ln0 LEQ2 HRM2. rewrite with_vmmaps_twice in HW2 |- *.
  apply (HK A2 m2 vm2 r2 (upd sels k sel) (upd vs k (set_name v name))).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins.
  split; [exact HW2|].
  split.
  { eapply POSTM_trans; [exact PM|]. eapply POSTM_trans; [apply (POSTM_sub C A Ak _ _ _ SUBA); eapply POSTM_mono; [|exact PM1]; lia | eapply POSTM_mono; [|exact PM2]; lia]. }
  split; [apply (hmcells_FRM C m1 m2 s _ _ _ CK (proj1 PM2) ltac:(lia) ltac:(lia)); apply (hmcells_FRM C mk m1 s _ _ _ CK (proj1 PM1) ltac:(lia) ltac:(lia)); exact CE|].
  split.
  { apply (sela_at_ext _ A2 m2 sela arr (k + 1) (upd sels k sel) (upd vs k (set_name v name)) (upd hm_name k bs)); [|exact SLA2].
    intros i Hi. split; [reflexivity|]. split; [reflexivity|]. destruct (Z.eq_dec i k) as [->|NE]; [rewrite upd_same; symmetry; exact Ebs | rewrite upd_other by exact NE; reflexivity]. }
  split.
  { intros i Hi. destruct (Z.eq_dec i k) as [->|NE]; [rewrite upd_same; cbn [set_name v_sy v_sx v]; split; assumption | rewrite upd_other by exact NE; apply SHP; lia]. }
  assert (BLK : forall q, sela_blk sela arr (k + 1) (upd sels k sel) (upd vs k (set_name v name)) q ->
                  sela_blk sela arr k sels vs q \/ sel_blk sel v q \/ q = name).
  { intros q [->|[->|(i & Hi & HB)]]; [left; left; reflexivity | left; right; left; reflexivity |].
    destruct (Z.eq_dec i k) as [->|NE].
    - rewrite !upd_same in HB. destruct HB as [HB|HB]; [right; left; exact HB | right; right; exact HB].
    - rewrite !upd_other in HB by exact NE. left. right. right. exists i. split; [lia | exact HB]. }
  split; [intros q Hq; destruct (BLK q Hq) as [X|[X| ->]]; [exact (SOA q X) | exact (SOA1 q X) | exact (live_none_sub A A1 _ SUBA1 LnA1)]|].
  split; [intros q Hq; destruct (BLK q Hq) as [X|[X| ->]]; [exact (SO0 q X) | exact (SO01 q X) | exact Ln0]|].
  split.
  { intros q NQ. rewrite (LEQ2 q).
    - rewrite (SN1 q).
      + apply SON. intros p' [->|[->|(i & Hi & HB)]]; apply NQ; [left; reflexivity | right; left; reflexivity |].
        right. right. exists i. split; [lia|]. rewrite !upd_other by lia. exact HB.
      + intros p' Hp'. apply NQ. right. right. exists k. split; [lia|]. rewrite !upd_same. left. exact Hp'.
    - apply NQ. right. right. exists k. split; [lia|]. rewrite !upd_same. right. reflexivity. }
  split.
  { replace (kR - (c + (3 + h)))%Z with (kR - (c + (2 + h)) - 1)%Z by lia.
    replace (bR - (c + (3 + h)) * RB10_small)%Z with (bR - (c + (2 + h)) * RB10_small - RB10_small)%Z by lia. exact HRM2. }
  split; [rewrite (CS2 2%bv cs2); exact Q2|].
  split; [rewrite (CS2 8%bv cs8); rewrite E8; exact R8|].
  apply (hm_rest_cs r' r2 regs CS2). intros x Hx. rewrite (ER x Hx). exact (RR x Hx).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Gaps.
Variable rom : word -> option byte.

  Lemma hm_g_27b10 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x27c0c : word) m rom) (mkst regs' (0x274cc : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x27c24 /\ getr regs' 10 = Z_to_bv 64 3 /\ getr regs' 11 = Z_to_bv 64 3 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 1 /\ getr regs' 14 = Z_to_bv 64 2
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27b10 D_27b10. sn F_27b14 D_27b14. sn F_27b18 D_27b18. sn F_27b1c D_27b1c. sn F_27b20 D_27b20. sn F_27b24 D_27b24. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27b28 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x27c24 : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x27c38 /\ getr regs' 9 = getr regs 10 /\ getr regs' 11 = Z_to_bv 64 1 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 9; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27b28 D_27b28. sn F_27b2c D_27b2c. sn F_27b30 D_27b30. sn F_27b34 D_27b34. sn F_27b38 D_27b38. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27b3c : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x27c38 : word) m rom) (mkst regs' (0x277b4 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x27c50 /\ getr regs' 10 = getr regs 8 /\ getr regs' 11 = getr regs 9 /\ getr regs' 12 = Z_to_bv 64 0x10ffb /\ getr regs' 13 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27b3c D_27b3c. sn F_27b40 D_27b40. sn F_27b44 D_27b44. sn F_27b48 D_27b48. sn F_27b4c D_27b4c. sn F_27b50 D_27b50. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27b54 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x27c50 : word) m rom) (mkst regs' (0x274cc : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x27c68 /\ getr regs' 10 = Z_to_bv 64 2 /\ getr regs' 11 = Z_to_bv 64 3 /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 13 = Z_to_bv 64 1 /\ getr regs' 14 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27b54 D_27b54. sn F_27b58 D_27b58. sn F_27b5c D_27b5c. sn F_27b60 D_27b60. sn F_27b64 D_27b64. sn F_27b68 D_27b68. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27b6c : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x27c68 : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x27c7c /\ getr regs' 9 = getr regs 10 /\ getr regs' 11 = Z_to_bv 64 1 /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 13 = Z_to_bv 64 2
      /\ regs_agree (fun r => In r [1; 9; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27b6c D_27b6c. sn F_27b70 D_27b70. sn F_27b74 D_27b74. sn F_27b78 D_27b78. sn F_27b7c D_27b7c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27b80 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x27c7c : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x27c90 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 1 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 2
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27b80 D_27b80. sn F_27b84 D_27b84. sn F_27b88 D_27b88. sn F_27b8c D_27b8c. sn F_27b90 D_27b90. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27b94 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x27c90 : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x27ca4 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 1 /\ getr regs' 12 = Z_to_bv 64 2 /\ getr regs' 13 = Z_to_bv 64 2
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27b94 D_27b94. sn F_27b98 D_27b98. sn F_27b9c D_27b9c. sn F_27ba0 D_27ba0. sn F_27ba4 D_27ba4. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27ba8 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x27ca4 : word) m rom) (mkst regs' (0x277b4 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x27cbc /\ getr regs' 10 = getr regs 8 /\ getr regs' 11 = getr regs 9 /\ getr regs' 12 = Z_to_bv 64 0x10e92 /\ getr regs' 13 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27ba8 D_27ba8. sn F_27bac D_27bac. sn F_27bb0 D_27bb0. sn F_27bb4 D_27bb4. sn F_27bb8 D_27bb8. sn F_27bbc D_27bbc. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27bc0 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x27cbc : word) m rom) (mkst regs' (0x274cc : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x27cd4 /\ getr regs' 10 = Z_to_bv 64 2 /\ getr regs' 11 = Z_to_bv 64 3 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 1 /\ getr regs' 14 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27bc0 D_27bc0. sn F_27bc4 D_27bc4. sn F_27bc8 D_27bc8. sn F_27bcc D_27bcc. sn F_27bd0 D_27bd0. sn F_27bd4 D_27bd4. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27bd8 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x27cd4 : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x27ce8 /\ getr regs' 9 = getr regs 10 /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 13 = Z_to_bv 64 2
      /\ regs_agree (fun r => In r [1; 9; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27bd8 D_27bd8. sn F_27bdc D_27bdc. sn F_27be0 D_27be0. sn F_27be4 D_27be4. sn F_27be8 D_27be8. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27bec : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x27ce8 : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x27cfc /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 2
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27bec D_27bec. sn F_27bf0 D_27bf0. sn F_27bf4 D_27bf4. sn F_27bf8 D_27bf8. sn F_27bfc D_27bfc. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27c00 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x27cfc : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x27d10 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 2 /\ getr regs' 13 = Z_to_bv 64 2
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27c00 D_27c00. sn F_27c04 D_27c04. sn F_27c08 D_27c08. sn F_27c0c D_27c0c. sn F_27c10 D_27c10. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27c14 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x27d10 : word) m rom) (mkst regs' (0x277b4 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x27d28 /\ getr regs' 10 = getr regs 8 /\ getr regs' 11 = getr regs 9 /\ getr regs' 12 = Z_to_bv 64 0x112ea /\ getr regs' 13 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27c14 D_27c14. sn F_27c18 D_27c18. sn F_27c1c D_27c1c. sn F_27c20 D_27c20. sn F_27c24 D_27c24. sn F_27c28 D_27c28. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27c2c : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x27d28 : word) m rom) (mkst regs' (0x274cc : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x27d40 /\ getr regs' 10 = Z_to_bv 64 3 /\ getr regs' 11 = Z_to_bv 64 2 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 0 /\ getr regs' 14 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27c2c D_27c2c. sn F_27c30 D_27c30. sn F_27c34 D_27c34. sn F_27c38 D_27c38. sn F_27c3c D_27c3c. sn F_27c40 D_27c40. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27c44 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x27d40 : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x27d54 /\ getr regs' 9 = getr regs 10 /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 2
      /\ regs_agree (fun r => In r [1; 9; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27c44 D_27c44. sn F_27c48 D_27c48. sn F_27c4c D_27c4c. sn F_27c50 D_27c50. sn F_27c54 D_27c54. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27c58 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x27d54 : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x27d68 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 1 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 2
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27c58 D_27c58. sn F_27c5c D_27c5c. sn F_27c60 D_27c60. sn F_27c64 D_27c64. sn F_27c68 D_27c68. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27c6c : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x27d68 : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x27d7c /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 2 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 2
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27c6c D_27c6c. sn F_27c70 D_27c70. sn F_27c74 D_27c74. sn F_27c78 D_27c78. sn F_27c7c D_27c7c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27c80 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x27d7c : word) m rom) (mkst regs' (0x277b4 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x27d94 /\ getr regs' 10 = getr regs 8 /\ getr regs' 11 = getr regs 9 /\ getr regs' 12 = Z_to_bv 64 0x11187 /\ getr regs' 13 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27c80 D_27c80. sn F_27c84 D_27c84. sn F_27c88 D_27c88. sn F_27c8c D_27c8c. sn F_27c90 D_27c90. sn F_27c94 D_27c94. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27c98 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x27d94 : word) m rom) (mkst regs' (0x274cc : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x27dac /\ getr regs' 10 = Z_to_bv 64 3 /\ getr regs' 11 = Z_to_bv 64 2 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 1 /\ getr regs' 14 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27c98 D_27c98. sn F_27c9c D_27c9c. sn F_27ca0 D_27ca0. sn F_27ca4 D_27ca4. sn F_27ca8 D_27ca8. sn F_27cac D_27cac. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27cb0 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x27dac : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x27dc0 /\ getr regs' 9 = getr regs 10 /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 13 = Z_to_bv 64 2
      /\ regs_agree (fun r => In r [1; 9; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27cb0 D_27cb0. sn F_27cb4 D_27cb4. sn F_27cb8 D_27cb8. sn F_27cbc D_27cbc. sn F_27cc0 D_27cc0. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27cc4 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x27dc0 : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x27dd4 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 1 /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 13 = Z_to_bv 64 2
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27cc4 D_27cc4. sn F_27cc8 D_27cc8. sn F_27ccc D_27ccc. sn F_27cd0 D_27cd0. sn F_27cd4 D_27cd4. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27cd8 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x27dd4 : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x27de8 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 2 /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 13 = Z_to_bv 64 2
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27cd8 D_27cd8. sn F_27cdc D_27cdc. sn F_27ce0 D_27ce0. sn F_27ce4 D_27ce4. sn F_27ce8 D_27ce8. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27cec : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x27de8 : word) m rom) (mkst regs' (0x277b4 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x27e00 /\ getr regs' 10 = getr regs 8 /\ getr regs' 11 = getr regs 9 /\ getr regs' 12 = Z_to_bv 64 0x10609 /\ getr regs' 13 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27cec D_27cec. sn F_27cf0 D_27cf0. sn F_27cf4 D_27cf4. sn F_27cf8 D_27cf8. sn F_27cfc D_27cfc. sn F_27d00 D_27d00. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27d04 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x27e00 : word) m rom) (mkst regs' (0x274cc : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x27e18 /\ getr regs' 10 = Z_to_bv 64 13 /\ getr regs' 11 = Z_to_bv 64 6 /\ getr regs' 12 = Z_to_bv 64 6 /\ getr regs' 13 = Z_to_bv 64 2 /\ getr regs' 14 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27d04 D_27d04. sn F_27d08 D_27d08. sn F_27d0c D_27d0c. sn F_27d10 D_27d10. sn F_27d14 D_27d14. sn F_27d18 D_27d18. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27d1c : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x27e18 : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x27e2c /\ getr regs' 9 = getr regs 10 /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 3 /\ getr regs' 13 = Z_to_bv 64 2
      /\ regs_agree (fun r => In r [1; 9; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27d1c D_27d1c. sn F_27d20 D_27d20. sn F_27d24 D_27d24. sn F_27d28 D_27d28. sn F_27d2c D_27d2c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27d30 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x27e2c : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x27e40 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 5 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27d30 D_27d30. sn F_27d34 D_27d34. sn F_27d38 D_27d38. sn F_27d3c D_27d3c. sn F_27d40 D_27d40. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27d44 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x27e40 : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x27e54 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 4 /\ getr regs' 12 = Z_to_bv 64 2 /\ getr regs' 13 = Z_to_bv 64 2
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27d44 D_27d44. sn F_27d48 D_27d48. sn F_27d4c D_27d4c. sn F_27d50 D_27d50. sn F_27d54 D_27d54. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27d58 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x27e54 : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x27e68 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 4 /\ getr regs' 12 = Z_to_bv 64 4 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27d58 D_27d58. sn F_27d5c D_27d5c. sn F_27d60 D_27d60. sn F_27d64 D_27d64. sn F_27d68 D_27d68. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27d6c : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x27e68 : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x27e7c /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 8 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 2
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27d6c D_27d6c. sn F_27d70 D_27d70. sn F_27d74 D_27d74. sn F_27d78 D_27d78. sn F_27d7c D_27d7c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27d80 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x27e7c : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x27e90 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 8 /\ getr regs' 12 = Z_to_bv 64 3 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27d80 D_27d80. sn F_27d84 D_27d84. sn F_27d88 D_27d88. sn F_27d8c D_27d8c. sn F_27d90 D_27d90. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27d94 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x27e90 : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x27ea4 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 12 /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 13 = Z_to_bv 64 2
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27d94 D_27d94. sn F_27d98 D_27d98. sn F_27d9c D_27d9c. sn F_27da0 D_27da0. sn F_27da4 D_27da4. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27da8 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x27ea4 : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x27eb8 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 12 /\ getr regs' 12 = Z_to_bv 64 2 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27da8 D_27da8. sn F_27dac D_27dac. sn F_27db0 D_27db0. sn F_27db4 D_27db4. sn F_27db8 D_27db8. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27dbc : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x27eb8 : word) m rom) (mkst regs' (0x277b4 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x27ed0 /\ getr regs' 10 = getr regs 8 /\ getr regs' 11 = getr regs 9 /\ getr regs' 12 = Z_to_bv 64 0x11543 /\ getr regs' 13 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27dbc D_27dbc. sn F_27dc0 D_27dc0. sn F_27dc4 D_27dc4. sn F_27dc8 D_27dc8. sn F_27dcc D_27dcc. sn F_27dd0 D_27dd0. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27dd4 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x27ed0 : word) m rom) (mkst regs' (0x274cc : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x27ee8 /\ getr regs' 10 = Z_to_bv 64 4 /\ getr regs' 11 = Z_to_bv 64 4 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 1 /\ getr regs' 14 = Z_to_bv 64 2
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27dd4 D_27dd4. sn F_27dd8 D_27dd8. sn F_27ddc D_27ddc. sn F_27de0 D_27de0. sn F_27de4 D_27de4. sn F_27de8 D_27de8. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27dec : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x27ee8 : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x27efc /\ getr regs' 9 = getr regs 10 /\ getr regs' 11 = Z_to_bv 64 1 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 9; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27dec D_27dec. sn F_27df0 D_27df0. sn F_27df4 D_27df4. sn F_27df8 D_27df8. sn F_27dfc D_27dfc. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27e00 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x27efc : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x27f10 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 1 /\ getr regs' 12 = Z_to_bv 64 2 /\ getr regs' 13 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27e00 D_27e00. sn F_27e04 D_27e04. sn F_27e08 D_27e08. sn F_27e0c D_27e0c. sn F_27e10 D_27e10. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27e14 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x27f10 : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x27f24 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 2 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27e14 D_27e14. sn F_27e18 D_27e18. sn F_27e1c D_27e1c. sn F_27e20 D_27e20. sn F_27e24 D_27e24. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27e28 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x27f24 : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x27f38 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 1 /\ getr regs' 12 = Z_to_bv 64 3 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27e28 D_27e28. sn F_27e2c D_27e2c. sn F_27e30 D_27e30. sn F_27e34 D_27e34. sn F_27e38 D_27e38. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27e3c : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x27f38 : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x27f4c /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 2 /\ getr regs' 12 = Z_to_bv 64 2 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27e3c D_27e3c. sn F_27e40 D_27e40. sn F_27e44 D_27e44. sn F_27e48 D_27e48. sn F_27e4c D_27e4c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27e50 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x27f4c : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x27f60 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 2 /\ getr regs' 12 = Z_to_bv 64 3 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27e50 D_27e50. sn F_27e54 D_27e54. sn F_27e58 D_27e58. sn F_27e5c D_27e5c. sn F_27e60 D_27e60. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27e64 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x27f60 : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x27f74 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 3 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27e64 D_27e64. sn F_27e68 D_27e68. sn F_27e6c D_27e6c. sn F_27e70 D_27e70. sn F_27e74 D_27e74. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27e78 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x27f74 : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x27f88 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 3 /\ getr regs' 12 = Z_to_bv 64 2 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27e78 D_27e78. sn F_27e7c D_27e7c. sn F_27e80 D_27e80. sn F_27e84 D_27e84. sn F_27e88 D_27e88. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27e8c : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x27f88 : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x27f9c /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 3 /\ getr regs' 12 = Z_to_bv 64 3 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27e8c D_27e8c. sn F_27e90 D_27e90. sn F_27e94 D_27e94. sn F_27e98 D_27e98. sn F_27e9c D_27e9c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27ea0 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x27f9c : word) m rom) (mkst regs' (0x277b4 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x27fb4 /\ getr regs' 10 = getr regs 8 /\ getr regs' 11 = getr regs 9 /\ getr regs' 12 = Z_to_bv 64 0x10d34 /\ getr regs' 13 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27ea0 D_27ea0. sn F_27ea4 D_27ea4. sn F_27ea8 D_27ea8. sn F_27eac D_27eac. sn F_27eb0 D_27eb0. sn F_27eb4 D_27eb4. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27eb8 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x27fb4 : word) m rom) (mkst regs' (0x274cc : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x27fcc /\ getr regs' 10 = Z_to_bv 64 4 /\ getr regs' 11 = Z_to_bv 64 4 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 2 /\ getr regs' 14 = Z_to_bv 64 2
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27eb8 D_27eb8. sn F_27ebc D_27ebc. sn F_27ec0 D_27ec0. sn F_27ec4 D_27ec4. sn F_27ec8 D_27ec8. sn F_27ecc D_27ecc. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27ed0 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x27fcc : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x27fe0 /\ getr regs' 9 = getr regs 10 /\ getr regs' 11 = Z_to_bv 64 1 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 9; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27ed0 D_27ed0. sn F_27ed4 D_27ed4. sn F_27ed8 D_27ed8. sn F_27edc D_27edc. sn F_27ee0 D_27ee0. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27ee4 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x27fe0 : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x27ff4 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 1 /\ getr regs' 12 = Z_to_bv 64 2 /\ getr regs' 13 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27ee4 D_27ee4. sn F_27ee8 D_27ee8. sn F_27eec D_27eec. sn F_27ef0 D_27ef0. sn F_27ef4 D_27ef4. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27ef8 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x27ff4 : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x28008 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 2 /\ getr regs' 12 = Z_to_bv 64 2 /\ getr regs' 13 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27ef8 D_27ef8. sn F_27efc D_27efc. sn F_27f00 D_27f00. sn F_27f04 D_27f04. sn F_27f08 D_27f08. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27f0c : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x28008 : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x2801c /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 1 /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27f0c D_27f0c. sn F_27f10 D_27f10. sn F_27f14 D_27f14. sn F_27f18 D_27f18. sn F_27f1c D_27f1c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27f20 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x2801c : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x28030 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 2 /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27f20 D_27f20. sn F_27f24 D_27f24. sn F_27f28 D_27f28. sn F_27f2c D_27f2c. sn F_27f30 D_27f30. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27f34 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x28030 : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x28044 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 2 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27f34 D_27f34. sn F_27f38 D_27f38. sn F_27f3c D_27f3c. sn F_27f40 D_27f40. sn F_27f44 D_27f44. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27f48 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x28044 : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x28058 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 3 /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27f48 D_27f48. sn F_27f4c D_27f4c. sn F_27f50 D_27f50. sn F_27f54 D_27f54. sn F_27f58 D_27f58. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27f5c : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x28058 : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x2806c /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 3 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27f5c D_27f5c. sn F_27f60 D_27f60. sn F_27f64 D_27f64. sn F_27f68 D_27f68. sn F_27f6c D_27f6c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27f70 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x2806c : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x28080 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 3 /\ getr regs' 12 = Z_to_bv 64 2 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27f70 D_27f70. sn F_27f74 D_27f74. sn F_27f78 D_27f78. sn F_27f7c D_27f7c. sn F_27f80 D_27f80. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27f84 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x28080 : word) m rom) (mkst regs' (0x277b4 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x28098 /\ getr regs' 10 = getr regs 8 /\ getr regs' 11 = getr regs 9 /\ getr regs' 12 = Z_to_bv 64 0x10422 /\ getr regs' 13 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27f84 D_27f84. sn F_27f88 D_27f88. sn F_27f8c D_27f8c. sn F_27f90 D_27f90. sn F_27f94 D_27f94. sn F_27f98 D_27f98. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27f9c : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x28098 : word) m rom) (mkst regs' (0x274cc : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x280b0 /\ getr regs' 10 = Z_to_bv 64 4 /\ getr regs' 11 = Z_to_bv 64 4 /\ getr regs' 12 = Z_to_bv 64 2 /\ getr regs' 13 = Z_to_bv 64 1 /\ getr regs' 14 = Z_to_bv 64 2
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27f9c D_27f9c. sn F_27fa0 D_27fa0. sn F_27fa4 D_27fa4. sn F_27fa8 D_27fa8. sn F_27fac D_27fac. sn F_27fb0 D_27fb0. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27fb4 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x280b0 : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x280c4 /\ getr regs' 9 = getr regs 10 /\ getr regs' 11 = Z_to_bv 64 1 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 9; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27fb4 D_27fb4. sn F_27fb8 D_27fb8. sn F_27fbc D_27fbc. sn F_27fc0 D_27fc0. sn F_27fc4 D_27fc4. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27fc8 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x280c4 : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x280d8 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 2 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27fc8 D_27fc8. sn F_27fcc D_27fcc. sn F_27fd0 D_27fd0. sn F_27fd4 D_27fd4. sn F_27fd8 D_27fd8. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27fdc : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x280d8 : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x280ec /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 2 /\ getr regs' 12 = Z_to_bv 64 2 /\ getr regs' 13 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27fdc D_27fdc. sn F_27fe0 D_27fe0. sn F_27fe4 D_27fe4. sn F_27fe8 D_27fe8. sn F_27fec D_27fec. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_27ff0 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x280ec : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x28100 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_27ff0 D_27ff0. sn F_27ff4 D_27ff4. sn F_27ff8 D_27ff8. sn F_27ffc D_27ffc. sn F_28000 D_28000. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_28004 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x28100 : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x28114 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 2 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_28004 D_28004. sn F_28008 D_28008. sn F_2800c D_2800c. sn F_28010 D_28010. sn F_28014 D_28014. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_28018 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x28114 : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x28128 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 3 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_28018 D_28018. sn F_2801c D_2801c. sn F_28020 D_28020. sn F_28024 D_28024. sn F_28028 D_28028. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_2802c : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x28128 : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x2813c /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 1 /\ getr regs' 12 = Z_to_bv 64 2 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_2802c D_2802c. sn F_28030 D_28030. sn F_28034 D_28034. sn F_28038 D_28038. sn F_2803c D_2803c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_28040 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x2813c : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x28150 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 1 /\ getr regs' 12 = Z_to_bv 64 3 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_28040 D_28040. sn F_28044 D_28044. sn F_28048 D_28048. sn F_2804c D_2804c. sn F_28050 D_28050. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_28054 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x28150 : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x28164 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 2 /\ getr regs' 12 = Z_to_bv 64 3 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_28054 D_28054. sn F_28058 D_28058. sn F_2805c D_2805c. sn F_28060 D_28060. sn F_28064 D_28064. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_28068 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x28164 : word) m rom) (mkst regs' (0x277b4 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x2817c /\ getr regs' 10 = getr regs 8 /\ getr regs' 11 = getr regs 9 /\ getr regs' 12 = Z_to_bv 64 0x10f24 /\ getr regs' 13 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_28068 D_28068. sn F_2806c D_2806c. sn F_28070 D_28070. sn F_28074 D_28074. sn F_28078 D_28078. sn F_2807c D_2807c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_28080 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x2817c : word) m rom) (mkst regs' (0x274cc : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x28194 /\ getr regs' 10 = Z_to_bv 64 4 /\ getr regs' 11 = Z_to_bv 64 4 /\ getr regs' 12 = Z_to_bv 64 2 /\ getr regs' 13 = Z_to_bv 64 2 /\ getr regs' 14 = Z_to_bv 64 2
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_28080 D_28080. sn F_28084 D_28084. sn F_28088 D_28088. sn F_2808c D_2808c. sn F_28090 D_28090. sn F_28094 D_28094. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_28098 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x28194 : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x281a8 /\ getr regs' 9 = getr regs 10 /\ getr regs' 11 = Z_to_bv 64 1 /\ getr regs' 12 = Z_to_bv 64 2 /\ getr regs' 13 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 9; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_28098 D_28098. sn F_2809c D_2809c. sn F_280a0 D_280a0. sn F_280a4 D_280a4. sn F_280a8 D_280a8. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_280ac : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x281a8 : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x281bc /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 2 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_280ac D_280ac. sn F_280b0 D_280b0. sn F_280b4 D_280b4. sn F_280b8 D_280b8. sn F_280bc D_280bc. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_280c0 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x281bc : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x281d0 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 2 /\ getr regs' 12 = Z_to_bv 64 2 /\ getr regs' 13 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_280c0 D_280c0. sn F_280c4 D_280c4. sn F_280c8 D_280c8. sn F_280cc D_280cc. sn F_280d0 D_280d0. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_280d4 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x281d0 : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x281e4 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_280d4 D_280d4. sn F_280d8 D_280d8. sn F_280dc D_280dc. sn F_280e0 D_280e0. sn F_280e4 D_280e4. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_280e8 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x281e4 : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x281f8 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_280e8 D_280e8. sn F_280ec D_280ec. sn F_280f0 D_280f0. sn F_280f4 D_280f4. sn F_280f8 D_280f8. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_280fc : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x281f8 : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x2820c /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 2 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_280fc D_280fc. sn F_28100 D_28100. sn F_28104 D_28104. sn F_28108 D_28108. sn F_2810c D_2810c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_28110 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x2820c : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x28220 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 1 /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_28110 D_28110. sn F_28114 D_28114. sn F_28118 D_28118. sn F_2811c D_2811c. sn F_28120 D_28120. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_28124 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x28220 : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x28234 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 1 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_28124 D_28124. sn F_28128 D_28128. sn F_2812c D_2812c. sn F_28130 D_28130. sn F_28134 D_28134. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_28138 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x28234 : word) m rom) (mkst regs' (0x2766c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x28248 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 2 /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_28138 D_28138. sn F_2813c D_2813c. sn F_28140 D_28140. sn F_28144 D_28144. sn F_28148 D_28148. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_2814c : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x28248 : word) m rom) (mkst regs' (0x277b4 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x28260 /\ getr regs' 10 = getr regs 8 /\ getr regs' 11 = getr regs 9 /\ getr regs' 12 = Z_to_bv 64 0x10542 /\ getr regs' 13 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_2814c D_2814c. sn F_28150 D_28150. sn F_28154 D_28154. sn F_28158 D_28158. sn F_2815c D_2815c. sn F_28160 D_28160. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

End Gaps.

(* [comment removed for export] *)
Definition hm_wd_0 : list byte := map (Z_to_bv 8) [104; 109; 0; 112; 105; 120; 100; 32]%Z.
Lemma hm_lit_0 : rdn SEGS (fun _ => None) (Z_to_bv 64 0x10ffb) 8 = Some (hm_name 0 ++ [Z_to_bv 8 0]).
Proof. vm_refl_bv. Qed.
Lemma hm_litw_0 : rdn SEGS (fun _ => None) (Z_to_bv 64 (0x10ffb + 5)) 8 = Some hm_wd_0.
Proof. vm_refl_bv. Qed.
Lemma hm_stop_0 : strlen_stop (Z_to_bv 64 (bytes_le_to_Z hm_wd_0)).
Proof. unfold strlen_stop. vm_compute. reflexivity. Qed.
Lemma hm_nz_0 : Forall (fun b => b <> Z_to_bv 8 0) (hm_name 0).
Proof. repeat constructor; intros E; apply (f_equal bv_unsigned) in E; vm_compute in E; discriminate. Qed.

Definition hm_wd_1 : list byte := map (Z_to_bv 8) [101; 0; 112; 100; 101; 115; 116; 32]%Z.
Lemma hm_lit_1 : rdn SEGS (fun _ => None) (Z_to_bv 64 0x10e92) 8 = Some (hm_name 1 ++ [Z_to_bv 8 0]).
Proof. vm_refl_bv. Qed.
Lemma hm_litw_1 : rdn SEGS (fun _ => None) (Z_to_bv 64 (0x10e92 + 6)) 8 = Some hm_wd_1.
Proof. vm_refl_bv. Qed.
Lemma hm_stop_1 : strlen_stop (Z_to_bv 64 (bytes_le_to_Z hm_wd_1)).
Proof. unfold strlen_stop. vm_compute. reflexivity. Qed.
Lemma hm_nz_1 : Forall (fun b => b <> Z_to_bv 8 0) (hm_name 1).
Proof. repeat constructor; intros E; apply (f_equal bv_unsigned) in E; vm_compute in E; discriminate. Qed.

Definition hm_wd_2 : list byte := map (Z_to_bv 8) [101; 0; 69; 114; 114; 111; 114; 32]%Z.
Lemma hm_lit_2 : rdn SEGS (fun _ => None) (Z_to_bv 64 0x112ea) 8 = Some (hm_name 2 ++ [Z_to_bv 8 0]).
Proof. vm_refl_bv. Qed.
Lemma hm_litw_2 : rdn SEGS (fun _ => None) (Z_to_bv 64 (0x112ea + 6)) 8 = Some hm_wd_2.
Proof. vm_refl_bv. Qed.
Lemma hm_stop_2 : strlen_stop (Z_to_bv 64 (bytes_le_to_Z hm_wd_2)).
Proof. unfold strlen_stop. vm_compute. reflexivity. Qed.
Lemma hm_nz_2 : Forall (fun b => b <> Z_to_bv 8 0) (hm_name 2).
Proof. repeat constructor; intros E; apply (f_equal bv_unsigned) in E; vm_compute in E; discriminate. Qed.

Definition hm_wd_3 : list byte := map (Z_to_bv 8) [101; 108; 95; 51; 114; 101; 0; 97]%Z.
Lemma hm_lit_3 : rdn SEGS (fun _ => None) (Z_to_bv 64 0x11187) 8 = Some (hm_name 3 ++ [Z_to_bv 8 0]).
Proof. vm_refl_bv. Qed.
Lemma hm_litw_3 : rdn SEGS (fun _ => None) (Z_to_bv 64 (0x11187 + 1)) 8 = Some hm_wd_3.
Proof. vm_refl_bv. Qed.
Lemma hm_stop_3 : strlen_stop (Z_to_bv 64 (bytes_le_to_Z hm_wd_3)).
Proof. unfold strlen_stop. vm_compute. reflexivity. Qed.
Lemma hm_nz_3 : Forall (fun b => b <> Z_to_bv 8 0) (hm_name 3).
Proof. repeat constructor; intros E; apply (f_equal bv_unsigned) in E; vm_compute in E; discriminate. Qed.

Definition hm_wd_4 : list byte := map (Z_to_bv 8) [0; 45; 48; 88; 43; 48; 88; 32]%Z.
Lemma hm_lit_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 0x10609) 8 = Some (hm_name 4 ++ [Z_to_bv 8 0]).
Proof. vm_refl_bv. Qed.
Lemma hm_litw_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 (0x10609 + 7)) 8 = Some hm_wd_4.
Proof. vm_refl_bv. Qed.
Lemma hm_stop_4 : strlen_stop (Z_to_bv 64 (bytes_le_to_Z hm_wd_4)).
Proof. unfold strlen_stop. vm_compute. reflexivity. Qed.
Lemma hm_nz_4 : Forall (fun b => b <> Z_to_bv 8 0) (hm_name 4).
Proof. repeat constructor; intros E; apply (f_equal bv_unsigned) in E; vm_compute in E; discriminate. Qed.

Definition hm_wd_5 : list byte := map (Z_to_bv 8) [108; 49; 0; 112; 105; 120; 83; 101]%Z.
Lemma hm_lit_5 : rdn SEGS (fun _ => None) (Z_to_bv 64 0x11543) 8 = Some (hm_name 5 ++ [Z_to_bv 8 0]).
Proof. vm_refl_bv. Qed.
Lemma hm_litw_5 : rdn SEGS (fun _ => None) (Z_to_bv 64 (0x11543 + 5)) 8 = Some hm_wd_5.
Proof. vm_refl_bv. Qed.
Lemma hm_stop_5 : strlen_stop (Z_to_bv 64 (bytes_le_to_Z hm_wd_5)).
Proof. unfold strlen_stop. vm_compute. reflexivity. Qed.
Lemma hm_nz_5 : Forall (fun b => b <> Z_to_bv 8 0) (hm_name 5).
Proof. repeat constructor; intros E; apply (f_equal bv_unsigned) in E; vm_compute in E; discriminate. Qed.

Definition hm_wd_6 : list byte := map (Z_to_bv 8) [117; 108; 99; 0; 112; 105; 120; 83]%Z.
Lemma hm_lit_6 : rdn SEGS (fun _ => None) (Z_to_bv 64 0x10d34) 8 = Some (hm_name 6 ++ [Z_to_bv 8 0]).
Proof. vm_refl_bv. Qed.
Lemma hm_litw_6 : rdn SEGS (fun _ => None) (Z_to_bv 64 (0x10d34 + 4)) 8 = Some hm_wd_6.
Proof. vm_refl_bv. Qed.
Lemma hm_stop_6 : strlen_stop (Z_to_bv 64 (bytes_le_to_Z hm_wd_6)).
Proof. unfold strlen_stop. vm_compute. reflexivity. Qed.
Lemma hm_nz_6 : Forall (fun b => b <> Z_to_bv 8 0) (hm_name 6).
Proof. repeat constructor; intros E; apply (f_equal bv_unsigned) in E; vm_compute in E; discriminate. Qed.

Definition hm_wd_7 : list byte := map (Z_to_bv 8) [99; 0; 112; 105; 120; 83; 101; 116]%Z.
Lemma hm_lit_7 : rdn SEGS (fun _ => None) (Z_to_bv 64 0x10422) 8 = Some (hm_name 7 ++ [Z_to_bv 8 0]).
Proof. vm_refl_bv. Qed.
Lemma hm_litw_7 : rdn SEGS (fun _ => None) (Z_to_bv 64 (0x10422 + 6)) 8 = Some hm_wd_7.
Proof. vm_refl_bv. Qed.
Lemma hm_stop_7 : strlen_stop (Z_to_bv 64 (bytes_le_to_Z hm_wd_7)).
Proof. unfold strlen_stop. vm_compute. reflexivity. Qed.
Lemma hm_nz_7 : Forall (fun b => b <> Z_to_bv 8 0) (hm_name 7).
Proof. repeat constructor; intros E; apply (f_equal bv_unsigned) in E; vm_compute in E; discriminate. Qed.

Definition hm_wd_8 : list byte := map (Z_to_bv 8) [108; 108; 99; 0; 112; 105; 120; 67]%Z.
Lemma hm_lit_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 0x10f24) 8 = Some (hm_name 8 ++ [Z_to_bv 8 0]).
Proof. vm_refl_bv. Qed.
Lemma hm_litw_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 (0x10f24 + 4)) 8 = Some hm_wd_8.
Proof. vm_refl_bv. Qed.
Lemma hm_stop_8 : strlen_stop (Z_to_bv 64 (bytes_le_to_Z hm_wd_8)).
Proof. unfold strlen_stop. vm_compute. reflexivity. Qed.
Lemma hm_nz_8 : Forall (fun b => b <> Z_to_bv 8 0) (hm_name 8).
Proof. repeat constructor; intros E; apply (f_equal bv_unsigned) in E; vm_compute in E; discriminate. Qed.

Definition hm_wd_9 : list byte := map (Z_to_bv 8) [99; 0; 112; 105; 120; 100; 32; 110]%Z.
Lemma hm_lit_9 : rdn SEGS (fun _ => None) (Z_to_bv 64 0x10542) 8 = Some (hm_name 9 ++ [Z_to_bv 8 0]).
Proof. vm_refl_bv. Qed.
Lemma hm_litw_9 : rdn SEGS (fun _ => None) (Z_to_bv 64 (0x10542 + 6)) 8 = Some hm_wd_9.
Proof. vm_refl_bv. Qed.
Lemma hm_stop_9 : strlen_stop (Z_to_bv 64 (bytes_le_to_Z hm_wd_9)).
Proof. unfold strlen_stop. vm_compute. reflexivity. Qed.
Lemma hm_nz_9 : Forall (fun b => b <> Z_to_bv 8 0) (hm_name 9).
Proof. repeat constructor; intros E; apply (f_equal bv_unsigned) in E; vm_compute in E; discriminate. Qed.

Lemma hm_round_0 : forall C A m md (s : Z) regs (kR bR sela arr : Z) Ak mk vmk rk sels vs (S : TSet),
  Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + SELAHM_STACK <= s)%Z -> (s <= c_top C)%Z -> getr regs 4 = Z_to_bv 64 0x45480 ->
  (RK10_sela <= kR)%Z -> (RB10_sela <= bR)%Z ->
  hminv C A m md s regs kR bR sela arr 0 2 Ak mk vmk rk sels vs ->
  (forall A2 m2 vm2 r2 sels' vs', hminv C A m md s regs kR bR sela arr (0 + 1) (2 + (3 + 3)) A2 m2 vm2 r2 sels' vs' ->
     realizes SEGS (mkCfg (mkst r2 (0x27c50 : word) m2 al_rom) (with_vmmaps vm2 md)) S) ->
  realizes SEGS (mkCfg (mkst rk (0x27c0c : word) mk al_rom) (with_vmmaps vmk md)) S.
Proof.
  intros C A m md s regs kR bR sela arr Ak mk vmk rk sels vs S CK Hs16 Hlo Hhi H4 HRK HRB INV HK.
  unfold RK10_sela in HRK. unfold RB10_sela, RB10_small in HRB.
  destruct (hm_g_27b10 al_rom rk mk) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & Q14 & AG).
  apply (hm_brick_W C A m md s regs kR bR sela arr 0 2 Ak mk vmk rk sels vs 3 3 1 1 2 0x27c24 (0x27c0c : word) r' S CK Hs16 Hlo Hhi H4 INV RUN Q1 ltac:(red; apply bv_eq; reflexivity) Q10 Q11 Q12 Q13 Q14 AG
           ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold RB10_small; lia)).
  clear r' RUN Q1 Q10 Q11 Q12 Q13 Q14 AG. intros A1 m1 vm1 r1 sel arrd rows RS R10 HRM1.
  replace (Z_to_bv 64 0x27c24) with (0x27c24 : word) by (apply bv_eq; reflexivity).
  set (v := SELV 3 3 1 1 arrd 0 rows) in *.
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_27b28 al_rom r1 m1) as (r' & RUN & Q1 & Q9 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 m1 vm1 r1 1 1 1 0x27c38 (0x27c24 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite (AG 10) by (notin_lit); exact R10) ltac:(rewrite Q9; exact R10) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q9 Q11 Q12 Q13 AG X2 X8 XR R10. intros ms1 rs1 RS R9.
  replace (Z_to_bv 64 0x27c38) with (0x27c38 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_27b3c al_rom rs1 ms1) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_add_W C A m md s regs kR bR sela arr 0 2 Ak mk vmk rk sels vs sel 3 3 1 1 arrd rows A1 ms1 vm1 rs1 0x10ffb 5 0x27c50 (hm_name 0) hm_wd_0 (0x27c38 : word) r' S
           CK Hs16 Hlo Hhi H4 INV ltac:(lia) RS HRM1 ltac:(lia) ltac:(unfold RB10_small; lia) RUN Q1 ltac:(red; apply bv_eq; reflexivity) ltac:(rewrite Q10; exact X8) ltac:(rewrite Q11; exact R9) Q12 Q13
           (AG 2%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) (AG 8%bv ltac:(notin_lit)) eq_refl eq_refl eq_refl
           ltac:(lia) ltac:(unfold hm_name, hm_names; simpl; lia) ltac:(unfold hm_name, hm_names; simpl; lia) hm_lit_0 hm_nz_0 ltac:(lia) ltac:(reflexivity) ltac:(unfold hm_name, hm_names; simpl; lia) hm_litw_0 hm_stop_0).
  intros A2 m2 vm2 r2 sels' vs' INV'. replace (Z_to_bv 64 0x27c50) with (0x27c50 : word) by (apply bv_eq; reflexivity).
  exact (HK A2 m2 vm2 r2 sels' vs' INV').
Qed.

Lemma hm_round_1 : forall C A m md (s : Z) regs (kR bR sela arr : Z) Ak mk vmk rk sels vs (S : TSet),
  Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + SELAHM_STACK <= s)%Z -> (s <= c_top C)%Z -> getr regs 4 = Z_to_bv 64 0x45480 ->
  (RK10_sela <= kR)%Z -> (RB10_sela <= bR)%Z ->
  hminv C A m md s regs kR bR sela arr 1 8 Ak mk vmk rk sels vs ->
  (forall A2 m2 vm2 r2 sels' vs', hminv C A m md s regs kR bR sela arr (1 + 1) (8 + (3 + 2)) A2 m2 vm2 r2 sels' vs' ->
     realizes SEGS (mkCfg (mkst r2 (0x27cbc : word) m2 al_rom) (with_vmmaps vm2 md)) S) ->
  realizes SEGS (mkCfg (mkst rk (0x27c50 : word) mk al_rom) (with_vmmaps vmk md)) S.
Proof.
  intros C A m md s regs kR bR sela arr Ak mk vmk rk sels vs S CK Hs16 Hlo Hhi H4 HRK HRB INV HK.
  unfold RK10_sela in HRK. unfold RB10_sela, RB10_small in HRB.
  destruct (hm_g_27b54 al_rom rk mk) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & Q14 & AG).
  apply (hm_brick_W C A m md s regs kR bR sela arr 1 8 Ak mk vmk rk sels vs 2 3 0 1 1 0x27c68 (0x27c50 : word) r' S CK Hs16 Hlo Hhi H4 INV RUN Q1 ltac:(red; apply bv_eq; reflexivity) Q10 Q11 Q12 Q13 Q14 AG
           ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold RB10_small; lia)).
  clear r' RUN Q1 Q10 Q11 Q12 Q13 Q14 AG. intros A1 m1 vm1 r1 sel arrd rows RS R10 HRM1.
  replace (Z_to_bv 64 0x27c68) with (0x27c68 : word) by (apply bv_eq; reflexivity).
  set (v := SELV 2 3 0 1 arrd 0 rows) in *.
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_27b6c al_rom r1 m1) as (r' & RUN & Q1 & Q9 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 m1 vm1 r1 1 0 2 0x27c7c (0x27c68 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite (AG 10) by (notin_lit); exact R10) ltac:(rewrite Q9; exact R10) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q9 Q11 Q12 Q13 AG X2 X8 XR R10. intros ms1 rs1 RS R9.
  replace (Z_to_bv 64 0x27c7c) with (0x27c7c : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_27b80 al_rom rs1 ms1) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms1 vm1 rs1 1 1 2 0x27c90 (0x27c7c : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms2 rs2 RS R9.
  replace (Z_to_bv 64 0x27c90) with (0x27c90 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_27b94 al_rom rs2 ms2) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms2 vm1 rs2 1 2 2 0x27ca4 (0x27c90 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms3 rs3 RS R9.
  replace (Z_to_bv 64 0x27ca4) with (0x27ca4 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_27ba8 al_rom rs3 ms3) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_add_W C A m md s regs kR bR sela arr 1 8 Ak mk vmk rk sels vs sel 2 3 0 1 arrd rows A1 ms3 vm1 rs3 0x10e92 6 0x27cbc (hm_name 1) hm_wd_1 (0x27ca4 : word) r' S
           CK Hs16 Hlo Hhi H4 INV ltac:(lia) RS HRM1 ltac:(lia) ltac:(unfold RB10_small; lia) RUN Q1 ltac:(red; apply bv_eq; reflexivity) ltac:(rewrite Q10; exact X8) ltac:(rewrite Q11; exact R9) Q12 Q13
           (AG 2%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) (AG 8%bv ltac:(notin_lit)) eq_refl eq_refl eq_refl
           ltac:(lia) ltac:(unfold hm_name, hm_names; simpl; lia) ltac:(unfold hm_name, hm_names; simpl; lia) hm_lit_1 hm_nz_1 ltac:(lia) ltac:(reflexivity) ltac:(unfold hm_name, hm_names; simpl; lia) hm_litw_1 hm_stop_1).
  intros A2 m2 vm2 r2 sels' vs' INV'. replace (Z_to_bv 64 0x27cbc) with (0x27cbc : word) by (apply bv_eq; reflexivity).
  exact (HK A2 m2 vm2 r2 sels' vs' INV').
Qed.

Lemma hm_round_2 : forall C A m md (s : Z) regs (kR bR sela arr : Z) Ak mk vmk rk sels vs (S : TSet),
  Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + SELAHM_STACK <= s)%Z -> (s <= c_top C)%Z -> getr regs 4 = Z_to_bv 64 0x45480 ->
  (RK10_sela <= kR)%Z -> (RB10_sela <= bR)%Z ->
  hminv C A m md s regs kR bR sela arr 2 13 Ak mk vmk rk sels vs ->
  (forall A2 m2 vm2 r2 sels' vs', hminv C A m md s regs kR bR sela arr (2 + 1) (13 + (3 + 2)) A2 m2 vm2 r2 sels' vs' ->
     realizes SEGS (mkCfg (mkst r2 (0x27d28 : word) m2 al_rom) (with_vmmaps vm2 md)) S) ->
  realizes SEGS (mkCfg (mkst rk (0x27cbc : word) mk al_rom) (with_vmmaps vmk md)) S.
Proof.
  intros C A m md s regs kR bR sela arr Ak mk vmk rk sels vs S CK Hs16 Hlo Hhi H4 HRK HRB INV HK.
  unfold RK10_sela in HRK. unfold RB10_sela, RB10_small in HRB.
  destruct (hm_g_27bc0 al_rom rk mk) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & Q14 & AG).
  apply (hm_brick_W C A m md s regs kR bR sela arr 2 13 Ak mk vmk rk sels vs 2 3 1 1 1 0x27cd4 (0x27cbc : word) r' S CK Hs16 Hlo Hhi H4 INV RUN Q1 ltac:(red; apply bv_eq; reflexivity) Q10 Q11 Q12 Q13 Q14 AG
           ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold RB10_small; lia)).
  clear r' RUN Q1 Q10 Q11 Q12 Q13 Q14 AG. intros A1 m1 vm1 r1 sel arrd rows RS R10 HRM1.
  replace (Z_to_bv 64 0x27cd4) with (0x27cd4 : word) by (apply bv_eq; reflexivity).
  set (v := SELV 2 3 1 1 arrd 0 rows) in *.
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_27bd8 al_rom r1 m1) as (r' & RUN & Q1 & Q9 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 m1 vm1 r1 0 0 2 0x27ce8 (0x27cd4 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite (AG 10) by (notin_lit); exact R10) ltac:(rewrite Q9; exact R10) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q9 Q11 Q12 Q13 AG X2 X8 XR R10. intros ms1 rs1 RS R9.
  replace (Z_to_bv 64 0x27ce8) with (0x27ce8 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_27bec al_rom rs1 ms1) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms1 vm1 rs1 0 1 2 0x27cfc (0x27ce8 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms2 rs2 RS R9.
  replace (Z_to_bv 64 0x27cfc) with (0x27cfc : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_27c00 al_rom rs2 ms2) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms2 vm1 rs2 0 2 2 0x27d10 (0x27cfc : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms3 rs3 RS R9.
  replace (Z_to_bv 64 0x27d10) with (0x27d10 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_27c14 al_rom rs3 ms3) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_add_W C A m md s regs kR bR sela arr 2 13 Ak mk vmk rk sels vs sel 2 3 1 1 arrd rows A1 ms3 vm1 rs3 0x112ea 6 0x27d28 (hm_name 2) hm_wd_2 (0x27d10 : word) r' S
           CK Hs16 Hlo Hhi H4 INV ltac:(lia) RS HRM1 ltac:(lia) ltac:(unfold RB10_small; lia) RUN Q1 ltac:(red; apply bv_eq; reflexivity) ltac:(rewrite Q10; exact X8) ltac:(rewrite Q11; exact R9) Q12 Q13
           (AG 2%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) (AG 8%bv ltac:(notin_lit)) eq_refl eq_refl eq_refl
           ltac:(lia) ltac:(unfold hm_name, hm_names; simpl; lia) ltac:(unfold hm_name, hm_names; simpl; lia) hm_lit_2 hm_nz_2 ltac:(lia) ltac:(reflexivity) ltac:(unfold hm_name, hm_names; simpl; lia) hm_litw_2 hm_stop_2).
  intros A2 m2 vm2 r2 sels' vs' INV'. replace (Z_to_bv 64 0x27d28) with (0x27d28 : word) by (apply bv_eq; reflexivity).
  exact (HK A2 m2 vm2 r2 sels' vs' INV').
Qed.

Lemma hm_round_3 : forall C A m md (s : Z) regs (kR bR sela arr : Z) Ak mk vmk rk sels vs (S : TSet),
  Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + SELAHM_STACK <= s)%Z -> (s <= c_top C)%Z -> getr regs 4 = Z_to_bv 64 0x45480 ->
  (RK10_sela <= kR)%Z -> (RB10_sela <= bR)%Z ->
  hminv C A m md s regs kR bR sela arr 3 18 Ak mk vmk rk sels vs ->
  (forall A2 m2 vm2 r2 sels' vs', hminv C A m md s regs kR bR sela arr (3 + 1) (18 + (3 + 3)) A2 m2 vm2 r2 sels' vs' ->
     realizes SEGS (mkCfg (mkst r2 (0x27d94 : word) m2 al_rom) (with_vmmaps vm2 md)) S) ->
  realizes SEGS (mkCfg (mkst rk (0x27d28 : word) mk al_rom) (with_vmmaps vmk md)) S.
Proof.
  intros C A m md s regs kR bR sela arr Ak mk vmk rk sels vs S CK Hs16 Hlo Hhi H4 HRK HRB INV HK.
  unfold RK10_sela in HRK. unfold RB10_sela, RB10_small in HRB.
  destruct (hm_g_27c2c al_rom rk mk) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & Q14 & AG).
  apply (hm_brick_W C A m md s regs kR bR sela arr 3 18 Ak mk vmk rk sels vs 3 2 1 0 1 0x27d40 (0x27d28 : word) r' S CK Hs16 Hlo Hhi H4 INV RUN Q1 ltac:(red; apply bv_eq; reflexivity) Q10 Q11 Q12 Q13 Q14 AG
           ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold RB10_small; lia)).
  clear r' RUN Q1 Q10 Q11 Q12 Q13 Q14 AG. intros A1 m1 vm1 r1 sel arrd rows RS R10 HRM1.
  replace (Z_to_bv 64 0x27d40) with (0x27d40 : word) by (apply bv_eq; reflexivity).
  set (v := SELV 3 2 1 0 arrd 0 rows) in *.
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_27c44 al_rom r1 m1) as (r' & RUN & Q1 & Q9 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 m1 vm1 r1 0 1 2 0x27d54 (0x27d40 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite (AG 10) by (notin_lit); exact R10) ltac:(rewrite Q9; exact R10) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q9 Q11 Q12 Q13 AG X2 X8 XR R10. intros ms1 rs1 RS R9.
  replace (Z_to_bv 64 0x27d54) with (0x27d54 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_27c58 al_rom rs1 ms1) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms1 vm1 rs1 1 1 2 0x27d68 (0x27d54 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms2 rs2 RS R9.
  replace (Z_to_bv 64 0x27d68) with (0x27d68 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_27c6c al_rom rs2 ms2) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms2 vm1 rs2 2 1 2 0x27d7c (0x27d68 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms3 rs3 RS R9.
  replace (Z_to_bv 64 0x27d7c) with (0x27d7c : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_27c80 al_rom rs3 ms3) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_add_W C A m md s regs kR bR sela arr 3 18 Ak mk vmk rk sels vs sel 3 2 1 0 arrd rows A1 ms3 vm1 rs3 0x11187 1 0x27d94 (hm_name 3) hm_wd_3 (0x27d7c : word) r' S
           CK Hs16 Hlo Hhi H4 INV ltac:(lia) RS HRM1 ltac:(lia) ltac:(unfold RB10_small; lia) RUN Q1 ltac:(red; apply bv_eq; reflexivity) ltac:(rewrite Q10; exact X8) ltac:(rewrite Q11; exact R9) Q12 Q13
           (AG 2%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) (AG 8%bv ltac:(notin_lit)) eq_refl eq_refl eq_refl
           ltac:(lia) ltac:(unfold hm_name, hm_names; simpl; lia) ltac:(unfold hm_name, hm_names; simpl; lia) hm_lit_3 hm_nz_3 ltac:(lia) ltac:(reflexivity) ltac:(unfold hm_name, hm_names; simpl; lia) hm_litw_3 hm_stop_3).
  intros A2 m2 vm2 r2 sels' vs' INV'. replace (Z_to_bv 64 0x27d94) with (0x27d94 : word) by (apply bv_eq; reflexivity).
  exact (HK A2 m2 vm2 r2 sels' vs' INV').
Qed.

Lemma hm_round_4 : forall C A m md (s : Z) regs (kR bR sela arr : Z) Ak mk vmk rk sels vs (S : TSet),
  Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + SELAHM_STACK <= s)%Z -> (s <= c_top C)%Z -> getr regs 4 = Z_to_bv 64 0x45480 ->
  (RK10_sela <= kR)%Z -> (RB10_sela <= bR)%Z ->
  hminv C A m md s regs kR bR sela arr 4 24 Ak mk vmk rk sels vs ->
  (forall A2 m2 vm2 r2 sels' vs', hminv C A m md s regs kR bR sela arr (4 + 1) (24 + (3 + 3)) A2 m2 vm2 r2 sels' vs' ->
     realizes SEGS (mkCfg (mkst r2 (0x27e00 : word) m2 al_rom) (with_vmmaps vm2 md)) S) ->
  realizes SEGS (mkCfg (mkst rk (0x27d94 : word) mk al_rom) (with_vmmaps vmk md)) S.
Proof.
  intros C A m md s regs kR bR sela arr Ak mk vmk rk sels vs S CK Hs16 Hlo Hhi H4 HRK HRB INV HK.
  unfold RK10_sela in HRK. unfold RB10_sela, RB10_small in HRB.
  destruct (hm_g_27c98 al_rom rk mk) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & Q14 & AG).
  apply (hm_brick_W C A m md s regs kR bR sela arr 4 24 Ak mk vmk rk sels vs 3 2 1 1 1 0x27dac (0x27d94 : word) r' S CK Hs16 Hlo Hhi H4 INV RUN Q1 ltac:(red; apply bv_eq; reflexivity) Q10 Q11 Q12 Q13 Q14 AG
           ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold RB10_small; lia)).
  clear r' RUN Q1 Q10 Q11 Q12 Q13 Q14 AG. intros A1 m1 vm1 r1 sel arrd rows RS R10 HRM1.
  replace (Z_to_bv 64 0x27dac) with (0x27dac : word) by (apply bv_eq; reflexivity).
  set (v := SELV 3 2 1 1 arrd 0 rows) in *.
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_27cb0 al_rom r1 m1) as (r' & RUN & Q1 & Q9 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 m1 vm1 r1 0 0 2 0x27dc0 (0x27dac : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite (AG 10) by (notin_lit); exact R10) ltac:(rewrite Q9; exact R10) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q9 Q11 Q12 Q13 AG X2 X8 XR R10. intros ms1 rs1 RS R9.
  replace (Z_to_bv 64 0x27dc0) with (0x27dc0 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_27cc4 al_rom rs1 ms1) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms1 vm1 rs1 1 0 2 0x27dd4 (0x27dc0 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms2 rs2 RS R9.
  replace (Z_to_bv 64 0x27dd4) with (0x27dd4 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_27cd8 al_rom rs2 ms2) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms2 vm1 rs2 2 0 2 0x27de8 (0x27dd4 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms3 rs3 RS R9.
  replace (Z_to_bv 64 0x27de8) with (0x27de8 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_27cec al_rom rs3 ms3) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_add_W C A m md s regs kR bR sela arr 4 24 Ak mk vmk rk sels vs sel 3 2 1 1 arrd rows A1 ms3 vm1 rs3 0x10609 7 0x27e00 (hm_name 4) hm_wd_4 (0x27de8 : word) r' S
           CK Hs16 Hlo Hhi H4 INV ltac:(lia) RS HRM1 ltac:(lia) ltac:(unfold RB10_small; lia) RUN Q1 ltac:(red; apply bv_eq; reflexivity) ltac:(rewrite Q10; exact X8) ltac:(rewrite Q11; exact R9) Q12 Q13
           (AG 2%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) (AG 8%bv ltac:(notin_lit)) eq_refl eq_refl eq_refl
           ltac:(lia) ltac:(unfold hm_name, hm_names; simpl; lia) ltac:(unfold hm_name, hm_names; simpl; lia) hm_lit_4 hm_nz_4 ltac:(lia) ltac:(reflexivity) ltac:(unfold hm_name, hm_names; simpl; lia) hm_litw_4 hm_stop_4).
  intros A2 m2 vm2 r2 sels' vs' INV'. replace (Z_to_bv 64 0x27e00) with (0x27e00 : word) by (apply bv_eq; reflexivity).
  exact (HK A2 m2 vm2 r2 sels' vs' INV').
Qed.

Lemma hm_round_5 : forall C A m md (s : Z) regs (kR bR sela arr : Z) Ak mk vmk rk sels vs (S : TSet),
  Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + SELAHM_STACK <= s)%Z -> (s <= c_top C)%Z -> getr regs 4 = Z_to_bv 64 0x45480 ->
  (RK10_sela <= kR)%Z -> (RB10_sela <= bR)%Z ->
  hminv C A m md s regs kR bR sela arr 5 30 Ak mk vmk rk sels vs ->
  (forall A2 m2 vm2 r2 sels' vs', hminv C A m md s regs kR bR sela arr (5 + 1) (30 + (3 + 13)) A2 m2 vm2 r2 sels' vs' ->
     realizes SEGS (mkCfg (mkst r2 (0x27ed0 : word) m2 al_rom) (with_vmmaps vm2 md)) S) ->
  realizes SEGS (mkCfg (mkst rk (0x27e00 : word) mk al_rom) (with_vmmaps vmk md)) S.
Proof.
  intros C A m md s regs kR bR sela arr Ak mk vmk rk sels vs S CK Hs16 Hlo Hhi H4 HRK HRB INV HK.
  unfold RK10_sela in HRK. unfold RB10_sela, RB10_small in HRB.
  destruct (hm_g_27d04 al_rom rk mk) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & Q14 & AG).
  apply (hm_brick_W C A m md s regs kR bR sela arr 5 30 Ak mk vmk rk sels vs 13 6 6 2 0 0x27e18 (0x27e00 : word) r' S CK Hs16 Hlo Hhi H4 INV RUN Q1 ltac:(red; apply bv_eq; reflexivity) Q10 Q11 Q12 Q13 Q14 AG
           ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold RB10_small; lia)).
  clear r' RUN Q1 Q10 Q11 Q12 Q13 Q14 AG. intros A1 m1 vm1 r1 sel arrd rows RS R10 HRM1.
  replace (Z_to_bv 64 0x27e18) with (0x27e18 : word) by (apply bv_eq; reflexivity).
  set (v := SELV 13 6 6 2 arrd 0 rows) in *.
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_27d1c al_rom r1 m1) as (r' & RUN & Q1 & Q9 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 m1 vm1 r1 0 3 2 0x27e2c (0x27e18 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite (AG 10) by (notin_lit); exact R10) ltac:(rewrite Q9; exact R10) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q9 Q11 Q12 Q13 AG X2 X8 XR R10. intros ms1 rs1 RS R9.
  replace (Z_to_bv 64 0x27e2c) with (0x27e2c : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_27d30 al_rom rs1 ms1) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms1 vm1 rs1 0 5 1 0x27e40 (0x27e2c : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms2 rs2 RS R9.
  replace (Z_to_bv 64 0x27e40) with (0x27e40 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_27d44 al_rom rs2 ms2) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms2 vm1 rs2 4 2 2 0x27e54 (0x27e40 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms3 rs3 RS R9.
  replace (Z_to_bv 64 0x27e54) with (0x27e54 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_27d58 al_rom rs3 ms3) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms3 vm1 rs3 4 4 1 0x27e68 (0x27e54 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms4 rs4 RS R9.
  replace (Z_to_bv 64 0x27e68) with (0x27e68 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_27d6c al_rom rs4 ms4) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms4 vm1 rs4 8 1 2 0x27e7c (0x27e68 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms5 rs5 RS R9.
  replace (Z_to_bv 64 0x27e7c) with (0x27e7c : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_27d80 al_rom rs5 ms5) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms5 vm1 rs5 8 3 1 0x27e90 (0x27e7c : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms6 rs6 RS R9.
  replace (Z_to_bv 64 0x27e90) with (0x27e90 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_27d94 al_rom rs6 ms6) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms6 vm1 rs6 12 0 2 0x27ea4 (0x27e90 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms7 rs7 RS R9.
  replace (Z_to_bv 64 0x27ea4) with (0x27ea4 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_27da8 al_rom rs7 ms7) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms7 vm1 rs7 12 2 1 0x27eb8 (0x27ea4 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms8 rs8 RS R9.
  replace (Z_to_bv 64 0x27eb8) with (0x27eb8 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_27dbc al_rom rs8 ms8) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_add_W C A m md s regs kR bR sela arr 5 30 Ak mk vmk rk sels vs sel 13 6 6 2 arrd rows A1 ms8 vm1 rs8 0x11543 5 0x27ed0 (hm_name 5) hm_wd_5 (0x27eb8 : word) r' S
           CK Hs16 Hlo Hhi H4 INV ltac:(lia) RS HRM1 ltac:(lia) ltac:(unfold RB10_small; lia) RUN Q1 ltac:(red; apply bv_eq; reflexivity) ltac:(rewrite Q10; exact X8) ltac:(rewrite Q11; exact R9) Q12 Q13
           (AG 2%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) (AG 8%bv ltac:(notin_lit)) eq_refl eq_refl eq_refl
           ltac:(lia) ltac:(unfold hm_name, hm_names; simpl; lia) ltac:(unfold hm_name, hm_names; simpl; lia) hm_lit_5 hm_nz_5 ltac:(lia) ltac:(reflexivity) ltac:(unfold hm_name, hm_names; simpl; lia) hm_litw_5 hm_stop_5).
  intros A2 m2 vm2 r2 sels' vs' INV'. replace (Z_to_bv 64 0x27ed0) with (0x27ed0 : word) by (apply bv_eq; reflexivity).
  exact (HK A2 m2 vm2 r2 sels' vs' INV').
Qed.

Lemma hm_round_6 : forall C A m md (s : Z) regs (kR bR sela arr : Z) Ak mk vmk rk sels vs (S : TSet),
  Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + SELAHM_STACK <= s)%Z -> (s <= c_top C)%Z -> getr regs 4 = Z_to_bv 64 0x45480 ->
  (RK10_sela <= kR)%Z -> (RB10_sela <= bR)%Z ->
  hminv C A m md s regs kR bR sela arr 6 46 Ak mk vmk rk sels vs ->
  (forall A2 m2 vm2 r2 sels' vs', hminv C A m md s regs kR bR sela arr (6 + 1) (46 + (3 + 4)) A2 m2 vm2 r2 sels' vs' ->
     realizes SEGS (mkCfg (mkst r2 (0x27fb4 : word) m2 al_rom) (with_vmmaps vm2 md)) S) ->
  realizes SEGS (mkCfg (mkst rk (0x27ed0 : word) mk al_rom) (with_vmmaps vmk md)) S.
Proof.
  intros C A m md s regs kR bR sela arr Ak mk vmk rk sels vs S CK Hs16 Hlo Hhi H4 HRK HRB INV HK.
  unfold RK10_sela in HRK. unfold RB10_sela, RB10_small in HRB.
  destruct (hm_g_27dd4 al_rom rk mk) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & Q14 & AG).
  apply (hm_brick_W C A m md s regs kR bR sela arr 6 46 Ak mk vmk rk sels vs 4 4 1 1 2 0x27ee8 (0x27ed0 : word) r' S CK Hs16 Hlo Hhi H4 INV RUN Q1 ltac:(red; apply bv_eq; reflexivity) Q10 Q11 Q12 Q13 Q14 AG
           ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold RB10_small; lia)).
  clear r' RUN Q1 Q10 Q11 Q12 Q13 Q14 AG. intros A1 m1 vm1 r1 sel arrd rows RS R10 HRM1.
  replace (Z_to_bv 64 0x27ee8) with (0x27ee8 : word) by (apply bv_eq; reflexivity).
  set (v := SELV 4 4 1 1 arrd 0 rows) in *.
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_27dec al_rom r1 m1) as (r' & RUN & Q1 & Q9 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 m1 vm1 r1 1 1 0 0x27efc (0x27ee8 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite (AG 10) by (notin_lit); exact R10) ltac:(rewrite Q9; exact R10) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q9 Q11 Q12 Q13 AG X2 X8 XR R10. intros ms1 rs1 RS R9.
  replace (Z_to_bv 64 0x27efc) with (0x27efc : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_27e00 al_rom rs1 ms1) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms1 vm1 rs1 1 2 0 0x27f10 (0x27efc : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms2 rs2 RS R9.
  replace (Z_to_bv 64 0x27f10) with (0x27f10 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_27e14 al_rom rs2 ms2) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms2 vm1 rs2 2 1 0 0x27f24 (0x27f10 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms3 rs3 RS R9.
  replace (Z_to_bv 64 0x27f24) with (0x27f24 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_27e28 al_rom rs3 ms3) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms3 vm1 rs3 1 3 1 0x27f38 (0x27f24 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms4 rs4 RS R9.
  replace (Z_to_bv 64 0x27f38) with (0x27f38 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_27e3c al_rom rs4 ms4) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms4 vm1 rs4 2 2 1 0x27f4c (0x27f38 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms5 rs5 RS R9.
  replace (Z_to_bv 64 0x27f4c) with (0x27f4c : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_27e50 al_rom rs5 ms5) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms5 vm1 rs5 2 3 1 0x27f60 (0x27f4c : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms6 rs6 RS R9.
  replace (Z_to_bv 64 0x27f60) with (0x27f60 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_27e64 al_rom rs6 ms6) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms6 vm1 rs6 3 1 1 0x27f74 (0x27f60 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms7 rs7 RS R9.
  replace (Z_to_bv 64 0x27f74) with (0x27f74 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_27e78 al_rom rs7 ms7) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms7 vm1 rs7 3 2 1 0x27f88 (0x27f74 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms8 rs8 RS R9.
  replace (Z_to_bv 64 0x27f88) with (0x27f88 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_27e8c al_rom rs8 ms8) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms8 vm1 rs8 3 3 1 0x27f9c (0x27f88 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms9 rs9 RS R9.
  replace (Z_to_bv 64 0x27f9c) with (0x27f9c : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_27ea0 al_rom rs9 ms9) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_add_W C A m md s regs kR bR sela arr 6 46 Ak mk vmk rk sels vs sel 4 4 1 1 arrd rows A1 ms9 vm1 rs9 0x10d34 4 0x27fb4 (hm_name 6) hm_wd_6 (0x27f9c : word) r' S
           CK Hs16 Hlo Hhi H4 INV ltac:(lia) RS HRM1 ltac:(lia) ltac:(unfold RB10_small; lia) RUN Q1 ltac:(red; apply bv_eq; reflexivity) ltac:(rewrite Q10; exact X8) ltac:(rewrite Q11; exact R9) Q12 Q13
           (AG 2%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) (AG 8%bv ltac:(notin_lit)) eq_refl eq_refl eq_refl
           ltac:(lia) ltac:(unfold hm_name, hm_names; simpl; lia) ltac:(unfold hm_name, hm_names; simpl; lia) hm_lit_6 hm_nz_6 ltac:(lia) ltac:(reflexivity) ltac:(unfold hm_name, hm_names; simpl; lia) hm_litw_6 hm_stop_6).
  intros A2 m2 vm2 r2 sels' vs' INV'. replace (Z_to_bv 64 0x27fb4) with (0x27fb4 : word) by (apply bv_eq; reflexivity).
  exact (HK A2 m2 vm2 r2 sels' vs' INV').
Qed.

Lemma hm_round_7 : forall C A m md (s : Z) regs (kR bR sela arr : Z) Ak mk vmk rk sels vs (S : TSet),
  Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + SELAHM_STACK <= s)%Z -> (s <= c_top C)%Z -> getr regs 4 = Z_to_bv 64 0x45480 ->
  (RK10_sela <= kR)%Z -> (RB10_sela <= bR)%Z ->
  hminv C A m md s regs kR bR sela arr 7 53 Ak mk vmk rk sels vs ->
  (forall A2 m2 vm2 r2 sels' vs', hminv C A m md s regs kR bR sela arr (7 + 1) (53 + (3 + 4)) A2 m2 vm2 r2 sels' vs' ->
     realizes SEGS (mkCfg (mkst r2 (0x28098 : word) m2 al_rom) (with_vmmaps vm2 md)) S) ->
  realizes SEGS (mkCfg (mkst rk (0x27fb4 : word) mk al_rom) (with_vmmaps vmk md)) S.
Proof.
  intros C A m md s regs kR bR sela arr Ak mk vmk rk sels vs S CK Hs16 Hlo Hhi H4 HRK HRB INV HK.
  unfold RK10_sela in HRK. unfold RB10_sela, RB10_small in HRB.
  destruct (hm_g_27eb8 al_rom rk mk) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & Q14 & AG).
  apply (hm_brick_W C A m md s regs kR bR sela arr 7 53 Ak mk vmk rk sels vs 4 4 1 2 2 0x27fcc (0x27fb4 : word) r' S CK Hs16 Hlo Hhi H4 INV RUN Q1 ltac:(red; apply bv_eq; reflexivity) Q10 Q11 Q12 Q13 Q14 AG
           ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold RB10_small; lia)).
  clear r' RUN Q1 Q10 Q11 Q12 Q13 Q14 AG. intros A1 m1 vm1 r1 sel arrd rows RS R10 HRM1.
  replace (Z_to_bv 64 0x27fcc) with (0x27fcc : word) by (apply bv_eq; reflexivity).
  set (v := SELV 4 4 1 2 arrd 0 rows) in *.
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_27ed0 al_rom r1 m1) as (r' & RUN & Q1 & Q9 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 m1 vm1 r1 1 1 0 0x27fe0 (0x27fcc : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite (AG 10) by (notin_lit); exact R10) ltac:(rewrite Q9; exact R10) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q9 Q11 Q12 Q13 AG X2 X8 XR R10. intros ms1 rs1 RS R9.
  replace (Z_to_bv 64 0x27fe0) with (0x27fe0 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_27ee4 al_rom rs1 ms1) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms1 vm1 rs1 1 2 0 0x27ff4 (0x27fe0 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms2 rs2 RS R9.
  replace (Z_to_bv 64 0x27ff4) with (0x27ff4 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_27ef8 al_rom rs2 ms2) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms2 vm1 rs2 2 2 0 0x28008 (0x27ff4 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms3 rs3 RS R9.
  replace (Z_to_bv 64 0x28008) with (0x28008 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_27f0c al_rom rs3 ms3) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms3 vm1 rs3 1 0 1 0x2801c (0x28008 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms4 rs4 RS R9.
  replace (Z_to_bv 64 0x2801c) with (0x2801c : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_27f20 al_rom rs4 ms4) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms4 vm1 rs4 2 0 1 0x28030 (0x2801c : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms5 rs5 RS R9.
  replace (Z_to_bv 64 0x28030) with (0x28030 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_27f34 al_rom rs5 ms5) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms5 vm1 rs5 2 1 1 0x28044 (0x28030 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms6 rs6 RS R9.
  replace (Z_to_bv 64 0x28044) with (0x28044 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_27f48 al_rom rs6 ms6) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms6 vm1 rs6 3 0 1 0x28058 (0x28044 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms7 rs7 RS R9.
  replace (Z_to_bv 64 0x28058) with (0x28058 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_27f5c al_rom rs7 ms7) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms7 vm1 rs7 3 1 1 0x2806c (0x28058 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms8 rs8 RS R9.
  replace (Z_to_bv 64 0x2806c) with (0x2806c : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_27f70 al_rom rs8 ms8) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms8 vm1 rs8 3 2 1 0x28080 (0x2806c : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms9 rs9 RS R9.
  replace (Z_to_bv 64 0x28080) with (0x28080 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_27f84 al_rom rs9 ms9) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_add_W C A m md s regs kR bR sela arr 7 53 Ak mk vmk rk sels vs sel 4 4 1 2 arrd rows A1 ms9 vm1 rs9 0x10422 6 0x28098 (hm_name 7) hm_wd_7 (0x28080 : word) r' S
           CK Hs16 Hlo Hhi H4 INV ltac:(lia) RS HRM1 ltac:(lia) ltac:(unfold RB10_small; lia) RUN Q1 ltac:(red; apply bv_eq; reflexivity) ltac:(rewrite Q10; exact X8) ltac:(rewrite Q11; exact R9) Q12 Q13
           (AG 2%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) (AG 8%bv ltac:(notin_lit)) eq_refl eq_refl eq_refl
           ltac:(lia) ltac:(unfold hm_name, hm_names; simpl; lia) ltac:(unfold hm_name, hm_names; simpl; lia) hm_lit_7 hm_nz_7 ltac:(lia) ltac:(reflexivity) ltac:(unfold hm_name, hm_names; simpl; lia) hm_litw_7 hm_stop_7).
  intros A2 m2 vm2 r2 sels' vs' INV'. replace (Z_to_bv 64 0x28098) with (0x28098 : word) by (apply bv_eq; reflexivity).
  exact (HK A2 m2 vm2 r2 sels' vs' INV').
Qed.

Lemma hm_round_8 : forall C A m md (s : Z) regs (kR bR sela arr : Z) Ak mk vmk rk sels vs (S : TSet),
  Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + SELAHM_STACK <= s)%Z -> (s <= c_top C)%Z -> getr regs 4 = Z_to_bv 64 0x45480 ->
  (RK10_sela <= kR)%Z -> (RB10_sela <= bR)%Z ->
  hminv C A m md s regs kR bR sela arr 8 60 Ak mk vmk rk sels vs ->
  (forall A2 m2 vm2 r2 sels' vs', hminv C A m md s regs kR bR sela arr (8 + 1) (60 + (3 + 4)) A2 m2 vm2 r2 sels' vs' ->
     realizes SEGS (mkCfg (mkst r2 (0x2817c : word) m2 al_rom) (with_vmmaps vm2 md)) S) ->
  realizes SEGS (mkCfg (mkst rk (0x28098 : word) mk al_rom) (with_vmmaps vmk md)) S.
Proof.
  intros C A m md s regs kR bR sela arr Ak mk vmk rk sels vs S CK Hs16 Hlo Hhi H4 HRK HRB INV HK.
  unfold RK10_sela in HRK. unfold RB10_sela, RB10_small in HRB.
  destruct (hm_g_27f9c al_rom rk mk) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & Q14 & AG).
  apply (hm_brick_W C A m md s regs kR bR sela arr 8 60 Ak mk vmk rk sels vs 4 4 2 1 2 0x280b0 (0x28098 : word) r' S CK Hs16 Hlo Hhi H4 INV RUN Q1 ltac:(red; apply bv_eq; reflexivity) Q10 Q11 Q12 Q13 Q14 AG
           ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold RB10_small; lia)).
  clear r' RUN Q1 Q10 Q11 Q12 Q13 Q14 AG. intros A1 m1 vm1 r1 sel arrd rows RS R10 HRM1.
  replace (Z_to_bv 64 0x280b0) with (0x280b0 : word) by (apply bv_eq; reflexivity).
  set (v := SELV 4 4 2 1 arrd 0 rows) in *.
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_27fb4 al_rom r1 m1) as (r' & RUN & Q1 & Q9 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 m1 vm1 r1 1 1 0 0x280c4 (0x280b0 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite (AG 10) by (notin_lit); exact R10) ltac:(rewrite Q9; exact R10) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q9 Q11 Q12 Q13 AG X2 X8 XR R10. intros ms1 rs1 RS R9.
  replace (Z_to_bv 64 0x280c4) with (0x280c4 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_27fc8 al_rom rs1 ms1) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms1 vm1 rs1 2 1 0 0x280d8 (0x280c4 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms2 rs2 RS R9.
  replace (Z_to_bv 64 0x280d8) with (0x280d8 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_27fdc al_rom rs2 ms2) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms2 vm1 rs2 2 2 0 0x280ec (0x280d8 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms3 rs3 RS R9.
  replace (Z_to_bv 64 0x280ec) with (0x280ec : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_27ff0 al_rom rs3 ms3) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms3 vm1 rs3 0 1 1 0x28100 (0x280ec : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms4 rs4 RS R9.
  replace (Z_to_bv 64 0x28100) with (0x28100 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_28004 al_rom rs4 ms4) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms4 vm1 rs4 0 2 1 0x28114 (0x28100 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms5 rs5 RS R9.
  replace (Z_to_bv 64 0x28114) with (0x28114 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_28018 al_rom rs5 ms5) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms5 vm1 rs5 0 3 1 0x28128 (0x28114 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms6 rs6 RS R9.
  replace (Z_to_bv 64 0x28128) with (0x28128 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_2802c al_rom rs6 ms6) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms6 vm1 rs6 1 2 1 0x2813c (0x28128 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms7 rs7 RS R9.
  replace (Z_to_bv 64 0x2813c) with (0x2813c : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_28040 al_rom rs7 ms7) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms7 vm1 rs7 1 3 1 0x28150 (0x2813c : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms8 rs8 RS R9.
  replace (Z_to_bv 64 0x28150) with (0x28150 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_28054 al_rom rs8 ms8) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms8 vm1 rs8 2 3 1 0x28164 (0x28150 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms9 rs9 RS R9.
  replace (Z_to_bv 64 0x28164) with (0x28164 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_28068 al_rom rs9 ms9) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_add_W C A m md s regs kR bR sela arr 8 60 Ak mk vmk rk sels vs sel 4 4 2 1 arrd rows A1 ms9 vm1 rs9 0x10f24 4 0x2817c (hm_name 8) hm_wd_8 (0x28164 : word) r' S
           CK Hs16 Hlo Hhi H4 INV ltac:(lia) RS HRM1 ltac:(lia) ltac:(unfold RB10_small; lia) RUN Q1 ltac:(red; apply bv_eq; reflexivity) ltac:(rewrite Q10; exact X8) ltac:(rewrite Q11; exact R9) Q12 Q13
           (AG 2%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) (AG 8%bv ltac:(notin_lit)) eq_refl eq_refl eq_refl
           ltac:(lia) ltac:(unfold hm_name, hm_names; simpl; lia) ltac:(unfold hm_name, hm_names; simpl; lia) hm_lit_8 hm_nz_8 ltac:(lia) ltac:(reflexivity) ltac:(unfold hm_name, hm_names; simpl; lia) hm_litw_8 hm_stop_8).
  intros A2 m2 vm2 r2 sels' vs' INV'. replace (Z_to_bv 64 0x2817c) with (0x2817c : word) by (apply bv_eq; reflexivity).
  exact (HK A2 m2 vm2 r2 sels' vs' INV').
Qed.

Lemma hm_round_9 : forall C A m md (s : Z) regs (kR bR sela arr : Z) Ak mk vmk rk sels vs (S : TSet),
  Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + SELAHM_STACK <= s)%Z -> (s <= c_top C)%Z -> getr regs 4 = Z_to_bv 64 0x45480 ->
  (RK10_sela <= kR)%Z -> (RB10_sela <= bR)%Z ->
  hminv C A m md s regs kR bR sela arr 9 67 Ak mk vmk rk sels vs ->
  (forall A2 m2 vm2 r2 sels' vs', hminv C A m md s regs kR bR sela arr (9 + 1) (67 + (3 + 4)) A2 m2 vm2 r2 sels' vs' ->
     realizes SEGS (mkCfg (mkst r2 (0x28260 : word) m2 al_rom) (with_vmmaps vm2 md)) S) ->
  realizes SEGS (mkCfg (mkst rk (0x2817c : word) mk al_rom) (with_vmmaps vmk md)) S.
Proof.
  intros C A m md s regs kR bR sela arr Ak mk vmk rk sels vs S CK Hs16 Hlo Hhi H4 HRK HRB INV HK.
  unfold RK10_sela in HRK. unfold RB10_sela, RB10_small in HRB.
  destruct (hm_g_28080 al_rom rk mk) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & Q14 & AG).
  apply (hm_brick_W C A m md s regs kR bR sela arr 9 67 Ak mk vmk rk sels vs 4 4 2 2 2 0x28194 (0x2817c : word) r' S CK Hs16 Hlo Hhi H4 INV RUN Q1 ltac:(red; apply bv_eq; reflexivity) Q10 Q11 Q12 Q13 Q14 AG
           ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold RB10_small; lia)).
  clear r' RUN Q1 Q10 Q11 Q12 Q13 Q14 AG. intros A1 m1 vm1 r1 sel arrd rows RS R10 HRM1.
  replace (Z_to_bv 64 0x28194) with (0x28194 : word) by (apply bv_eq; reflexivity).
  set (v := SELV 4 4 2 2 arrd 0 rows) in *.
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_28098 al_rom r1 m1) as (r' & RUN & Q1 & Q9 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 m1 vm1 r1 1 2 0 0x281a8 (0x28194 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite (AG 10) by (notin_lit); exact R10) ltac:(rewrite Q9; exact R10) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q9 Q11 Q12 Q13 AG X2 X8 XR R10. intros ms1 rs1 RS R9.
  replace (Z_to_bv 64 0x281a8) with (0x281a8 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_280ac al_rom rs1 ms1) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms1 vm1 rs1 2 1 0 0x281bc (0x281a8 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms2 rs2 RS R9.
  replace (Z_to_bv 64 0x281bc) with (0x281bc : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_280c0 al_rom rs2 ms2) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms2 vm1 rs2 2 2 0 0x281d0 (0x281bc : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms3 rs3 RS R9.
  replace (Z_to_bv 64 0x281d0) with (0x281d0 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_280d4 al_rom rs3 ms3) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms3 vm1 rs3 0 0 1 0x281e4 (0x281d0 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms4 rs4 RS R9.
  replace (Z_to_bv 64 0x281e4) with (0x281e4 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_280e8 al_rom rs4 ms4) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms4 vm1 rs4 0 1 1 0x281f8 (0x281e4 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms5 rs5 RS R9.
  replace (Z_to_bv 64 0x281f8) with (0x281f8 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_280fc al_rom rs5 ms5) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms5 vm1 rs5 0 2 1 0x2820c (0x281f8 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms6 rs6 RS R9.
  replace (Z_to_bv 64 0x2820c) with (0x2820c : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_28110 al_rom rs6 ms6) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms6 vm1 rs6 1 0 1 0x28220 (0x2820c : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms7 rs7 RS R9.
  replace (Z_to_bv 64 0x28220) with (0x28220 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_28124 al_rom rs7 ms7) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms7 vm1 rs7 1 1 1 0x28234 (0x28220 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms8 rs8 RS R9.
  replace (Z_to_bv 64 0x28234) with (0x28234 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_28138 al_rom rs8 ms8) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms8 vm1 rs8 2 0 1 0x28248 (0x28234 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms9 rs9 RS R9.
  replace (Z_to_bv 64 0x28248) with (0x28248 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_2814c al_rom rs9 ms9) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_add_W C A m md s regs kR bR sela arr 9 67 Ak mk vmk rk sels vs sel 4 4 2 2 arrd rows A1 ms9 vm1 rs9 0x10542 6 0x28260 (hm_name 9) hm_wd_9 (0x28248 : word) r' S
           CK Hs16 Hlo Hhi H4 INV ltac:(lia) RS HRM1 ltac:(lia) ltac:(unfold RB10_small; lia) RUN Q1 ltac:(red; apply bv_eq; reflexivity) ltac:(rewrite Q10; exact X8) ltac:(rewrite Q11; exact R9) Q12 Q13
           (AG 2%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) (AG 8%bv ltac:(notin_lit)) eq_refl eq_refl eq_refl
           ltac:(lia) ltac:(unfold hm_name, hm_names; simpl; lia) ltac:(unfold hm_name, hm_names; simpl; lia) hm_lit_9 hm_nz_9 ltac:(lia) ltac:(reflexivity) ltac:(unfold hm_name, hm_names; simpl; lia) hm_litw_9 hm_stop_9).
  intros A2 m2 vm2 r2 sels' vs' INV'. replace (Z_to_bv 64 0x28260) with (0x28260 : word) by (apply bv_eq; reflexivity).
  exact (HK A2 m2 vm2 r2 sels' vs' INV').
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem selaAddHitMiss_W : selaAddHitMiss_contract.
Proof.
  intros C A m md regs s ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 kR bR HRM HRK HRB HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
  assert (HsS : (c_top C - LSTK + 32 + 32 + CALLOC_STACK <= s)%Z) by (unfold SELAHM_STACK in Hlo; lia).
  assert (HsS' : (c_top C - LSTK + 64 <= s)%Z) by (unfold CALLOC_STACK, ALLOC_STACK in HsS; lia).
  unfold PC_selaAddHitMiss. replace (Z_to_bv 64 0x27be8) with (0x27be8 : word) by (apply bv_eq; reflexivity).
  destruct (hm_sA al_rom regs m s ret ltac:(lia) ltac:(lia) (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := HMF m s ret regs).
  assert (WP1 : W C A M1 md /\ POSTM C A s m M1) by (subst M1; unfold HMF; wp_win CK).
  destruct WP1 as [HW1 PM1].
  pose proof (hmcells_HMF m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1. rewrite <- H1 in CE1.
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x45480) by (rewrite (AG1 4) by notin_lit; exact H4).
  assert (HRK2 : (2 <= kR)%Z) by (unfold RK10_sela in HRK; lia).
  assert (HRB2 : (2 * RB10_small <= bR)%Z) by (unfold RB10_sela, RB10_small in *; lia).
  apply (selaCreate_W C A M1 md r1 (s - 32) (Z_to_bv 64 0x27c04) S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity) Q4 Q10 kR bR HRM HRK2 HRB2).
  intros A1 m1 vm1 r2 sela arr HWa CSa PMa R10 SLA0 LsA LaA Ls0 La0 LEQ HRMa.
  replace (Z_to_bv 64 0x27c04) with (0x27c04 : word) by (apply bv_eq; reflexivity).
  pose proof (SLA0 (fun _ => 0%Z) (fun _ => SELV 0 0 0 0 0 0 (fun _ => 0%Z)) hm_name) as SLA.
  pose proof SLA as (_ & (Gs & TOPs & _) & _).
  destruct (hm_sB al_rom r2 m1 sela ltac:(lia) R10) as (r3 & RUN3 & P8 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
  assert (INV0 : hminv C A m md s regs kR bR sela arr 0 2 A1 m1 vm1 r3 (fun _ => 0%Z) (fun _ => SELV 0 0 0 0 0 0 (fun _ => 0%Z))).
  { split; [exact HWa|].
    split; [eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]|].
    split; [apply (hmcells_FRM C M1 m1 s _ _ _ CK (proj1 PMa) ltac:(lia) ltac:(lia)); exact CE1|].
    split; [exact SLA|].
    split; [intros i Hi; lia|].
    split; [intros p [->|[->|(i & Hi & _)]]; [exact LsA | exact LaA | lia]|].
    split; [intros p [->|[->|(i & Hi & _)]]; [exact Ls0 | exact La0 | lia]|].
    split; [intros q NQ; apply LEQ; apply NQ; [left; reflexivity | right; left; reflexivity]|].
    split; [exact HRMa|].
    split; [rewrite (AG3 2) by notin_lit; rewrite (CSa 2%bv cs2); exact Q2|].
    split; [exact P8|].
    apply (hm_rest_agree _ r2 r3 regs AG3); [notin_rest|]. apply (hm_rest_cs r1 r2 regs CSa). apply (hm_rest_agree _ regs r1 regs AG1); [notin_rest|]. intros x _. reflexivity. }
  clear SLA0 SLA RUN1 RUN3.
  apply (hm_round_0 C A m md s regs kR bR sela arr A1 m1 vm1 r3 _ _ S CK Hs16 Hlo Hhi H4 HRK HRB INV0). clear INV0. intros Aa ma vma ra sa va INVa.
  apply (hm_round_1 C A m md s regs kR bR sela arr Aa ma vma ra sa va S CK Hs16 Hlo Hhi H4 HRK HRB INVa). clear INVa. intros Ab mb vmb rb sb vb INVb.
  apply (hm_round_2 C A m md s regs kR bR sela arr Ab mb vmb rb sb vb S CK Hs16 Hlo Hhi H4 HRK HRB INVb). clear INVb. intros Ac mc vmc rc sc vc INVc.
  apply (hm_round_3 C A m md s regs kR bR sela arr Ac mc vmc rc sc vc S CK Hs16 Hlo Hhi H4 HRK HRB INVc). clear INVc. intros Ad md' vmd rd sd vd INVd.
  apply (hm_round_4 C A m md s regs kR bR sela arr Ad md' vmd rd sd vd S CK Hs16 Hlo Hhi H4 HRK HRB INVd). clear INVd. intros Ae me vme re se ve INVe.
  apply (hm_round_5 C A m md s regs kR bR sela arr Ae me vme re se ve S CK Hs16 Hlo Hhi H4 HRK HRB INVe). clear INVe. intros Af mf vmf rf sf vf INVf.
  apply (hm_round_6 C A m md s regs kR bR sela arr Af mf vmf rf sf vf S CK Hs16 Hlo Hhi H4 HRK HRB INVf). clear INVf. intros Ag mg vmg rg sg vg INVg.
  apply (hm_round_7 C A m md s regs kR bR sela arr Ag mg vmg rg sg vg S CK Hs16 Hlo Hhi H4 HRK HRB INVg). clear INVg. intros Ah mh vmh rh sh vh INVh.
  apply (hm_round_8 C A m md s regs kR bR sela arr Ah mh vmh rh sh vh S CK Hs16 Hlo Hhi H4 HRK HRB INVh). clear INVh. intros Ai mi vmi ri si vi INVi.
  apply (hm_round_9 C A m md s regs kR bR sela arr Ai mi vmi ri si vi S CK Hs16 Hlo Hhi H4 HRK HRB INVi). clear INVi. intros Az mz vmz rz sz vz INVz.
  destruct INVz as (HWz & PMz & CEz & SLAz & SHPz & SOAz & SO0z & SONz & HRMz & R2z & R8z & RRz).
  destruct (hm_sZ al_rom rz mz s sela (getr regs 1) (getr regs 8) (getr regs 9) ltac:(lia) ltac:(lia) ltac:(rewrite H1; exact Hret) CEz R2z R8z)
    as (rf' & RUNz & Z2 & Z1 & Z10 & Z8 & Z9 & AGz).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWz)) | exact (mp_lazy _ (w_pure _ _ _ _ HWz)) | exact RUNz |].
  rewrite H1. apply (HK Az mz vmz rf' sela arr sz vz HWz).
  - assert (REST : forall x, In x hm_rest -> getr rf' x = getr regs x) by (apply (hm_rest_agree _ rz rf' regs AGz); [notin_rest | exact RRz]).
    apply cs_kept_intro; first [ rewrite Z2; symmetry; exact H2 | exact Z8 | exact Z9 | apply REST; unfold hm_rest; in_lit ].
  - exact PMz.
  - exact Z10.
  - split; [exact SLAz | exact SHPz].
  - exact SOAz.
  - exact SO0z.
  - exact SONz.
  - exact HRMz.
Qed.

End SelHM.
