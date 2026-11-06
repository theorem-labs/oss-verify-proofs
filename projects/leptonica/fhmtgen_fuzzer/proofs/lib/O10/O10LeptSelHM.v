(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.fhmtgen_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 LeptRecs LeptSlots LeptSel.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.O10 Require Import O10LeptStderr O10LeptBase.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.O10 Require Import O10CL7a.
Import O10CL7a.O10LeptSel_iface.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.O10 Require Import O10_code_fhFG.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.O10 Require Import O10CL8a.
Import O10CL8a.O10LeptSelSegs.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.O10 Require Import O10LeptSelCreate O10LeptSelBrick.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoom10.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section SelHM.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LL16} {P16 : O10Pins}.
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
      msteps SEGS (mkst regs (0x208ec : word) m rom) (mkst regs' (0x1fd90 : word) (HMF m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 1 = Z_to_bv 64 0x20908 /\ getr regs' 10 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 2; 8]%list) regs regs'.
  Proof.
    intros regs m s ret Hs Hs64 SOK H2 H1 H10. eexists. split.
    - zv F_207f0 D_207f0 (Z_to_bv 64 (s - 32)).
      stepST F_207f4 D_207f4 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_207f8 D_207f8 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_207fc D_207fc (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      sn F_20800 D_20800.
      stepb_ft F_20804 D_20804 ltac:(condZ).
      sn F_20808 D_20808.
      unfold HMF. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma hm_sB : forall regs m (sela : Z),
    (1 <= sela < 2 ^ 64)%Z -> getr regs 10 = Z_to_bv 64 sela ->
    exists regs',
      msteps SEGS (mkst regs (0x20908 : word) m rom) (mkst regs' (0x20910 : word) m rom)
      /\ getr regs' 8 = Z_to_bv 64 sela /\ regs_agree (fun r => In r [8]%list) regs regs'.
  Proof.
    intros regs m sela Hs H10. eexists. split.
    - sn F_2080c D_2080c. stepb_ft F_20810 D_20810 ltac:(condZ). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma hm_sZ : forall regs m (s sela : Z) (ret s0v s1v : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> hmcells m s ret s0v s1v ->
    getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 8 = Z_to_bv 64 sela ->
    exists regs',
      msteps SEGS (mkst regs (0x20f64 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 sela /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10]%list) regs regs'.
  Proof.
    intros regs m s sela ret s0v s1v Hs Hs64 Hret (C1 & C2 & C3) H2 H8. eexists. split.
    - sn F_20e68 D_20e68.
      stepLD8 F_20e6c D_20e6c ret. stepLD8 F_20e70 D_20e70 s0v. stepLD8 F_20e74 D_20e74 s1v.
      zv F_20e78 D_20e78 (Z_to_bv 64 s).
      stepret F_20e7c D_20e7c ret ltac:(bveq).
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
  Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + SELAHM_STACK <= s)%Z -> (s <= c_top C)%Z -> getr regs 4 = Z_to_bv 64 0x3d100 ->
  hminv C A m md s regs kR bR sela arr k c Ak mk vmk rk sels vs ->
  msteps SEGS (mkst rk pca mk al_rom) (mkst r' (0x2031c : word) mk al_rom) ->
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
  assert (Q4 : getr r' 4 = Z_to_bv 64 0x3d100) by (rewrite (AG 4) by notin_lit; rewrite (RR 4%bv) by (unfold hm_rest; in_lit); exact H4).
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
  msteps SEGS (mkst r1 pca m1 al_rom) (mkst r' (0x20454 : word) m1 al_rom) ->
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
  Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + SELAHM_STACK <= s)%Z -> (s <= c_top C)%Z -> getr regs 4 = Z_to_bv 64 0x3d100 ->
  hminv C A m md s regs kR bR sela arr k c Ak mk vmk rk sels vs -> (0 <= k < 50)%Z ->
  hmrs C Ak mk md s regs sela sel (SELV h w cy cx arrd 0 rows) A1 m1 vm1 r1 ->
  aroom A1 vm1 (kR - (c + (2 + h))) (bR - (c + (2 + h)) * RB10_small) -> (c + (2 + h) + 1 <= kR)%Z -> ((c + (2 + h) + 1) * RB10_small <= bR)%Z ->
  msteps SEGS (mkst r1 pca m1 al_rom) (mkst r' (0x20554 : word) m1 al_rom) ->
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
  assert (Q4 : getr r' 4 = Z_to_bv 64 0x3d100) by (rewrite (ER 4%bv) by (unfold hm_rest; in_lit); rewrite (RR 4%bv) by (unfold hm_rest; in_lit); exact H4).
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

  Lemma hm_g_20814 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20910 : word) m rom) (mkst regs' (0x2031c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20928 /\ getr regs' 10 = Z_to_bv 64 3 /\ getr regs' 11 = Z_to_bv 64 3 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 1 /\ getr regs' 14 = Z_to_bv 64 2
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20814 D_20814. sn F_20818 D_20818. sn F_2081c D_2081c. sn F_20820 D_20820. sn F_20824 D_20824. sn F_20828 D_20828. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_2082c : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20928 : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x2093c /\ getr regs' 9 = getr regs 10 /\ getr regs' 11 = Z_to_bv 64 1 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 9; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_2082c D_2082c. sn F_20830 D_20830. sn F_20834 D_20834. sn F_20838 D_20838. sn F_2083c D_2083c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20840 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x2093c : word) m rom) (mkst regs' (0x20554 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20954 /\ getr regs' 10 = getr regs 8 /\ getr regs' 11 = getr regs 9 /\ getr regs' 12 = Z_to_bv 64 0x10ffb /\ getr regs' 13 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20840 D_20840. sn F_20844 D_20844. sn F_20848 D_20848. sn F_2084c D_2084c. sn F_20850 D_20850. sn F_20854 D_20854. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20858 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20954 : word) m rom) (mkst regs' (0x2031c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x2096c /\ getr regs' 10 = Z_to_bv 64 2 /\ getr regs' 11 = Z_to_bv 64 3 /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 13 = Z_to_bv 64 1 /\ getr regs' 14 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20858 D_20858. sn F_2085c D_2085c. sn F_20860 D_20860. sn F_20864 D_20864. sn F_20868 D_20868. sn F_2086c D_2086c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20870 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x2096c : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20980 /\ getr regs' 9 = getr regs 10 /\ getr regs' 11 = Z_to_bv 64 1 /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 13 = Z_to_bv 64 2
      /\ regs_agree (fun r => In r [1; 9; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20870 D_20870. sn F_20874 D_20874. sn F_20878 D_20878. sn F_2087c D_2087c. sn F_20880 D_20880. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20884 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20980 : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20994 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 1 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 2
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20884 D_20884. sn F_20888 D_20888. sn F_2088c D_2088c. sn F_20890 D_20890. sn F_20894 D_20894. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20898 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20994 : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x209a8 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 1 /\ getr regs' 12 = Z_to_bv 64 2 /\ getr regs' 13 = Z_to_bv 64 2
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20898 D_20898. sn F_2089c D_2089c. sn F_208a0 D_208a0. sn F_208a4 D_208a4. sn F_208a8 D_208a8. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_208ac : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x209a8 : word) m rom) (mkst regs' (0x20554 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x209c0 /\ getr regs' 10 = getr regs 8 /\ getr regs' 11 = getr regs 9 /\ getr regs' 12 = Z_to_bv 64 0x10e92 /\ getr regs' 13 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_208ac D_208ac. sn F_208b0 D_208b0. sn F_208b4 D_208b4. sn F_208b8 D_208b8. sn F_208bc D_208bc. sn F_208c0 D_208c0. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_208c4 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x209c0 : word) m rom) (mkst regs' (0x2031c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x209d8 /\ getr regs' 10 = Z_to_bv 64 2 /\ getr regs' 11 = Z_to_bv 64 3 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 1 /\ getr regs' 14 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_208c4 D_208c4. sn F_208c8 D_208c8. sn F_208cc D_208cc. sn F_208d0 D_208d0. sn F_208d4 D_208d4. sn F_208d8 D_208d8. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_208dc : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x209d8 : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x209ec /\ getr regs' 9 = getr regs 10 /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 13 = Z_to_bv 64 2
      /\ regs_agree (fun r => In r [1; 9; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_208dc D_208dc. sn F_208e0 D_208e0. sn F_208e4 D_208e4. sn F_208e8 D_208e8. sn F_208ec D_208ec. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_208f0 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x209ec : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20a00 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 2
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_208f0 D_208f0. sn F_208f4 D_208f4. sn F_208f8 D_208f8. sn F_208fc D_208fc. sn F_20900 D_20900. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20904 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20a00 : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20a14 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 2 /\ getr regs' 13 = Z_to_bv 64 2
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20904 D_20904. sn F_20908 D_20908. sn F_2090c D_2090c. sn F_20910 D_20910. sn F_20914 D_20914. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20918 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20a14 : word) m rom) (mkst regs' (0x20554 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20a2c /\ getr regs' 10 = getr regs 8 /\ getr regs' 11 = getr regs 9 /\ getr regs' 12 = Z_to_bv 64 0x112ea /\ getr regs' 13 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20918 D_20918. sn F_2091c D_2091c. sn F_20920 D_20920. sn F_20924 D_20924. sn F_20928 D_20928. sn F_2092c D_2092c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20930 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20a2c : word) m rom) (mkst regs' (0x2031c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20a44 /\ getr regs' 10 = Z_to_bv 64 3 /\ getr regs' 11 = Z_to_bv 64 2 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 0 /\ getr regs' 14 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20930 D_20930. sn F_20934 D_20934. sn F_20938 D_20938. sn F_2093c D_2093c. sn F_20940 D_20940. sn F_20944 D_20944. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20948 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20a44 : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20a58 /\ getr regs' 9 = getr regs 10 /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 2
      /\ regs_agree (fun r => In r [1; 9; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20948 D_20948. sn F_2094c D_2094c. sn F_20950 D_20950. sn F_20954 D_20954. sn F_20958 D_20958. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_2095c : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20a58 : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20a6c /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 1 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 2
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_2095c D_2095c. sn F_20960 D_20960. sn F_20964 D_20964. sn F_20968 D_20968. sn F_2096c D_2096c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20970 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20a6c : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20a80 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 2 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 2
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20970 D_20970. sn F_20974 D_20974. sn F_20978 D_20978. sn F_2097c D_2097c. sn F_20980 D_20980. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20984 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20a80 : word) m rom) (mkst regs' (0x20554 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20a98 /\ getr regs' 10 = getr regs 8 /\ getr regs' 11 = getr regs 9 /\ getr regs' 12 = Z_to_bv 64 0x11187 /\ getr regs' 13 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20984 D_20984. sn F_20988 D_20988. sn F_2098c D_2098c. sn F_20990 D_20990. sn F_20994 D_20994. sn F_20998 D_20998. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_2099c : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20a98 : word) m rom) (mkst regs' (0x2031c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20ab0 /\ getr regs' 10 = Z_to_bv 64 3 /\ getr regs' 11 = Z_to_bv 64 2 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 1 /\ getr regs' 14 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_2099c D_2099c. sn F_209a0 D_209a0. sn F_209a4 D_209a4. sn F_209a8 D_209a8. sn F_209ac D_209ac. sn F_209b0 D_209b0. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_209b4 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20ab0 : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20ac4 /\ getr regs' 9 = getr regs 10 /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 13 = Z_to_bv 64 2
      /\ regs_agree (fun r => In r [1; 9; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_209b4 D_209b4. sn F_209b8 D_209b8. sn F_209bc D_209bc. sn F_209c0 D_209c0. sn F_209c4 D_209c4. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_209c8 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20ac4 : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20ad8 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 1 /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 13 = Z_to_bv 64 2
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_209c8 D_209c8. sn F_209cc D_209cc. sn F_209d0 D_209d0. sn F_209d4 D_209d4. sn F_209d8 D_209d8. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_209dc : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20ad8 : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20aec /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 2 /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 13 = Z_to_bv 64 2
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_209dc D_209dc. sn F_209e0 D_209e0. sn F_209e4 D_209e4. sn F_209e8 D_209e8. sn F_209ec D_209ec. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_209f0 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20aec : word) m rom) (mkst regs' (0x20554 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20b04 /\ getr regs' 10 = getr regs 8 /\ getr regs' 11 = getr regs 9 /\ getr regs' 12 = Z_to_bv 64 0x10609 /\ getr regs' 13 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_209f0 D_209f0. sn F_209f4 D_209f4. sn F_209f8 D_209f8. sn F_209fc D_209fc. sn F_20a00 D_20a00. sn F_20a04 D_20a04. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20a08 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20b04 : word) m rom) (mkst regs' (0x2031c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20b1c /\ getr regs' 10 = Z_to_bv 64 13 /\ getr regs' 11 = Z_to_bv 64 6 /\ getr regs' 12 = Z_to_bv 64 6 /\ getr regs' 13 = Z_to_bv 64 2 /\ getr regs' 14 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20a08 D_20a08. sn F_20a0c D_20a0c. sn F_20a10 D_20a10. sn F_20a14 D_20a14. sn F_20a18 D_20a18. sn F_20a1c D_20a1c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20a20 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20b1c : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20b30 /\ getr regs' 9 = getr regs 10 /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 3 /\ getr regs' 13 = Z_to_bv 64 2
      /\ regs_agree (fun r => In r [1; 9; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20a20 D_20a20. sn F_20a24 D_20a24. sn F_20a28 D_20a28. sn F_20a2c D_20a2c. sn F_20a30 D_20a30. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20a34 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20b30 : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20b44 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 5 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20a34 D_20a34. sn F_20a38 D_20a38. sn F_20a3c D_20a3c. sn F_20a40 D_20a40. sn F_20a44 D_20a44. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20a48 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20b44 : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20b58 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 4 /\ getr regs' 12 = Z_to_bv 64 2 /\ getr regs' 13 = Z_to_bv 64 2
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20a48 D_20a48. sn F_20a4c D_20a4c. sn F_20a50 D_20a50. sn F_20a54 D_20a54. sn F_20a58 D_20a58. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20a5c : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20b58 : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20b6c /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 4 /\ getr regs' 12 = Z_to_bv 64 4 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20a5c D_20a5c. sn F_20a60 D_20a60. sn F_20a64 D_20a64. sn F_20a68 D_20a68. sn F_20a6c D_20a6c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20a70 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20b6c : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20b80 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 8 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 2
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20a70 D_20a70. sn F_20a74 D_20a74. sn F_20a78 D_20a78. sn F_20a7c D_20a7c. sn F_20a80 D_20a80. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20a84 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20b80 : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20b94 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 8 /\ getr regs' 12 = Z_to_bv 64 3 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20a84 D_20a84. sn F_20a88 D_20a88. sn F_20a8c D_20a8c. sn F_20a90 D_20a90. sn F_20a94 D_20a94. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20a98 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20b94 : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20ba8 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 12 /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 13 = Z_to_bv 64 2
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20a98 D_20a98. sn F_20a9c D_20a9c. sn F_20aa0 D_20aa0. sn F_20aa4 D_20aa4. sn F_20aa8 D_20aa8. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20aac : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20ba8 : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20bbc /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 12 /\ getr regs' 12 = Z_to_bv 64 2 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20aac D_20aac. sn F_20ab0 D_20ab0. sn F_20ab4 D_20ab4. sn F_20ab8 D_20ab8. sn F_20abc D_20abc. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20ac0 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20bbc : word) m rom) (mkst regs' (0x20554 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20bd4 /\ getr regs' 10 = getr regs 8 /\ getr regs' 11 = getr regs 9 /\ getr regs' 12 = Z_to_bv 64 0x11543 /\ getr regs' 13 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20ac0 D_20ac0. sn F_20ac4 D_20ac4. sn F_20ac8 D_20ac8. sn F_20acc D_20acc. sn F_20ad0 D_20ad0. sn F_20ad4 D_20ad4. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20ad8 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20bd4 : word) m rom) (mkst regs' (0x2031c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20bec /\ getr regs' 10 = Z_to_bv 64 4 /\ getr regs' 11 = Z_to_bv 64 4 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 1 /\ getr regs' 14 = Z_to_bv 64 2
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20ad8 D_20ad8. sn F_20adc D_20adc. sn F_20ae0 D_20ae0. sn F_20ae4 D_20ae4. sn F_20ae8 D_20ae8. sn F_20aec D_20aec. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20af0 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20bec : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20c00 /\ getr regs' 9 = getr regs 10 /\ getr regs' 11 = Z_to_bv 64 1 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 9; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20af0 D_20af0. sn F_20af4 D_20af4. sn F_20af8 D_20af8. sn F_20afc D_20afc. sn F_20b00 D_20b00. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20b04 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20c00 : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20c14 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 1 /\ getr regs' 12 = Z_to_bv 64 2 /\ getr regs' 13 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20b04 D_20b04. sn F_20b08 D_20b08. sn F_20b0c D_20b0c. sn F_20b10 D_20b10. sn F_20b14 D_20b14. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20b18 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20c14 : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20c28 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 2 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20b18 D_20b18. sn F_20b1c D_20b1c. sn F_20b20 D_20b20. sn F_20b24 D_20b24. sn F_20b28 D_20b28. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20b2c : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20c28 : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20c3c /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 1 /\ getr regs' 12 = Z_to_bv 64 3 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20b2c D_20b2c. sn F_20b30 D_20b30. sn F_20b34 D_20b34. sn F_20b38 D_20b38. sn F_20b3c D_20b3c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20b40 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20c3c : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20c50 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 2 /\ getr regs' 12 = Z_to_bv 64 2 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20b40 D_20b40. sn F_20b44 D_20b44. sn F_20b48 D_20b48. sn F_20b4c D_20b4c. sn F_20b50 D_20b50. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20b54 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20c50 : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20c64 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 2 /\ getr regs' 12 = Z_to_bv 64 3 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20b54 D_20b54. sn F_20b58 D_20b58. sn F_20b5c D_20b5c. sn F_20b60 D_20b60. sn F_20b64 D_20b64. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20b68 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20c64 : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20c78 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 3 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20b68 D_20b68. sn F_20b6c D_20b6c. sn F_20b70 D_20b70. sn F_20b74 D_20b74. sn F_20b78 D_20b78. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20b7c : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20c78 : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20c8c /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 3 /\ getr regs' 12 = Z_to_bv 64 2 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20b7c D_20b7c. sn F_20b80 D_20b80. sn F_20b84 D_20b84. sn F_20b88 D_20b88. sn F_20b8c D_20b8c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20b90 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20c8c : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20ca0 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 3 /\ getr regs' 12 = Z_to_bv 64 3 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20b90 D_20b90. sn F_20b94 D_20b94. sn F_20b98 D_20b98. sn F_20b9c D_20b9c. sn F_20ba0 D_20ba0. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20ba4 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20ca0 : word) m rom) (mkst regs' (0x20554 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20cb8 /\ getr regs' 10 = getr regs 8 /\ getr regs' 11 = getr regs 9 /\ getr regs' 12 = Z_to_bv 64 0x10d34 /\ getr regs' 13 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20ba4 D_20ba4. sn F_20ba8 D_20ba8. sn F_20bac D_20bac. sn F_20bb0 D_20bb0. sn F_20bb4 D_20bb4. sn F_20bb8 D_20bb8. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20bbc : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20cb8 : word) m rom) (mkst regs' (0x2031c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20cd0 /\ getr regs' 10 = Z_to_bv 64 4 /\ getr regs' 11 = Z_to_bv 64 4 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 2 /\ getr regs' 14 = Z_to_bv 64 2
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20bbc D_20bbc. sn F_20bc0 D_20bc0. sn F_20bc4 D_20bc4. sn F_20bc8 D_20bc8. sn F_20bcc D_20bcc. sn F_20bd0 D_20bd0. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20bd4 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20cd0 : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20ce4 /\ getr regs' 9 = getr regs 10 /\ getr regs' 11 = Z_to_bv 64 1 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 9; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20bd4 D_20bd4. sn F_20bd8 D_20bd8. sn F_20bdc D_20bdc. sn F_20be0 D_20be0. sn F_20be4 D_20be4. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20be8 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20ce4 : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20cf8 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 1 /\ getr regs' 12 = Z_to_bv 64 2 /\ getr regs' 13 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20be8 D_20be8. sn F_20bec D_20bec. sn F_20bf0 D_20bf0. sn F_20bf4 D_20bf4. sn F_20bf8 D_20bf8. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20bfc : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20cf8 : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20d0c /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 2 /\ getr regs' 12 = Z_to_bv 64 2 /\ getr regs' 13 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20bfc D_20bfc. sn F_20c00 D_20c00. sn F_20c04 D_20c04. sn F_20c08 D_20c08. sn F_20c0c D_20c0c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20c10 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20d0c : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20d20 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 1 /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20c10 D_20c10. sn F_20c14 D_20c14. sn F_20c18 D_20c18. sn F_20c1c D_20c1c. sn F_20c20 D_20c20. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20c24 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20d20 : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20d34 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 2 /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20c24 D_20c24. sn F_20c28 D_20c28. sn F_20c2c D_20c2c. sn F_20c30 D_20c30. sn F_20c34 D_20c34. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20c38 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20d34 : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20d48 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 2 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20c38 D_20c38. sn F_20c3c D_20c3c. sn F_20c40 D_20c40. sn F_20c44 D_20c44. sn F_20c48 D_20c48. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20c4c : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20d48 : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20d5c /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 3 /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20c4c D_20c4c. sn F_20c50 D_20c50. sn F_20c54 D_20c54. sn F_20c58 D_20c58. sn F_20c5c D_20c5c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20c60 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20d5c : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20d70 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 3 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20c60 D_20c60. sn F_20c64 D_20c64. sn F_20c68 D_20c68. sn F_20c6c D_20c6c. sn F_20c70 D_20c70. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20c74 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20d70 : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20d84 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 3 /\ getr regs' 12 = Z_to_bv 64 2 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20c74 D_20c74. sn F_20c78 D_20c78. sn F_20c7c D_20c7c. sn F_20c80 D_20c80. sn F_20c84 D_20c84. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20c88 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20d84 : word) m rom) (mkst regs' (0x20554 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20d9c /\ getr regs' 10 = getr regs 8 /\ getr regs' 11 = getr regs 9 /\ getr regs' 12 = Z_to_bv 64 0x10422 /\ getr regs' 13 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20c88 D_20c88. sn F_20c8c D_20c8c. sn F_20c90 D_20c90. sn F_20c94 D_20c94. sn F_20c98 D_20c98. sn F_20c9c D_20c9c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20ca0 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20d9c : word) m rom) (mkst regs' (0x2031c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20db4 /\ getr regs' 10 = Z_to_bv 64 4 /\ getr regs' 11 = Z_to_bv 64 4 /\ getr regs' 12 = Z_to_bv 64 2 /\ getr regs' 13 = Z_to_bv 64 1 /\ getr regs' 14 = Z_to_bv 64 2
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20ca0 D_20ca0. sn F_20ca4 D_20ca4. sn F_20ca8 D_20ca8. sn F_20cac D_20cac. sn F_20cb0 D_20cb0. sn F_20cb4 D_20cb4. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20cb8 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20db4 : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20dc8 /\ getr regs' 9 = getr regs 10 /\ getr regs' 11 = Z_to_bv 64 1 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 9; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20cb8 D_20cb8. sn F_20cbc D_20cbc. sn F_20cc0 D_20cc0. sn F_20cc4 D_20cc4. sn F_20cc8 D_20cc8. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20ccc : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20dc8 : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20ddc /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 2 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20ccc D_20ccc. sn F_20cd0 D_20cd0. sn F_20cd4 D_20cd4. sn F_20cd8 D_20cd8. sn F_20cdc D_20cdc. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20ce0 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20ddc : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20df0 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 2 /\ getr regs' 12 = Z_to_bv 64 2 /\ getr regs' 13 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20ce0 D_20ce0. sn F_20ce4 D_20ce4. sn F_20ce8 D_20ce8. sn F_20cec D_20cec. sn F_20cf0 D_20cf0. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20cf4 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20df0 : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20e04 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20cf4 D_20cf4. sn F_20cf8 D_20cf8. sn F_20cfc D_20cfc. sn F_20d00 D_20d00. sn F_20d04 D_20d04. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20d08 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20e04 : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20e18 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 2 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20d08 D_20d08. sn F_20d0c D_20d0c. sn F_20d10 D_20d10. sn F_20d14 D_20d14. sn F_20d18 D_20d18. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20d1c : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20e18 : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20e2c /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 3 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20d1c D_20d1c. sn F_20d20 D_20d20. sn F_20d24 D_20d24. sn F_20d28 D_20d28. sn F_20d2c D_20d2c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20d30 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20e2c : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20e40 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 1 /\ getr regs' 12 = Z_to_bv 64 2 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20d30 D_20d30. sn F_20d34 D_20d34. sn F_20d38 D_20d38. sn F_20d3c D_20d3c. sn F_20d40 D_20d40. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20d44 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20e40 : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20e54 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 1 /\ getr regs' 12 = Z_to_bv 64 3 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20d44 D_20d44. sn F_20d48 D_20d48. sn F_20d4c D_20d4c. sn F_20d50 D_20d50. sn F_20d54 D_20d54. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20d58 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20e54 : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20e68 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 2 /\ getr regs' 12 = Z_to_bv 64 3 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20d58 D_20d58. sn F_20d5c D_20d5c. sn F_20d60 D_20d60. sn F_20d64 D_20d64. sn F_20d68 D_20d68. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20d6c : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20e68 : word) m rom) (mkst regs' (0x20554 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20e80 /\ getr regs' 10 = getr regs 8 /\ getr regs' 11 = getr regs 9 /\ getr regs' 12 = Z_to_bv 64 0x10f24 /\ getr regs' 13 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20d6c D_20d6c. sn F_20d70 D_20d70. sn F_20d74 D_20d74. sn F_20d78 D_20d78. sn F_20d7c D_20d7c. sn F_20d80 D_20d80. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20d84 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20e80 : word) m rom) (mkst regs' (0x2031c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20e98 /\ getr regs' 10 = Z_to_bv 64 4 /\ getr regs' 11 = Z_to_bv 64 4 /\ getr regs' 12 = Z_to_bv 64 2 /\ getr regs' 13 = Z_to_bv 64 2 /\ getr regs' 14 = Z_to_bv 64 2
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20d84 D_20d84. sn F_20d88 D_20d88. sn F_20d8c D_20d8c. sn F_20d90 D_20d90. sn F_20d94 D_20d94. sn F_20d98 D_20d98. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20d9c : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20e98 : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20eac /\ getr regs' 9 = getr regs 10 /\ getr regs' 11 = Z_to_bv 64 1 /\ getr regs' 12 = Z_to_bv 64 2 /\ getr regs' 13 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 9; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20d9c D_20d9c. sn F_20da0 D_20da0. sn F_20da4 D_20da4. sn F_20da8 D_20da8. sn F_20dac D_20dac. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20db0 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20eac : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20ec0 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 2 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20db0 D_20db0. sn F_20db4 D_20db4. sn F_20db8 D_20db8. sn F_20dbc D_20dbc. sn F_20dc0 D_20dc0. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20dc4 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20ec0 : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20ed4 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 2 /\ getr regs' 12 = Z_to_bv 64 2 /\ getr regs' 13 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20dc4 D_20dc4. sn F_20dc8 D_20dc8. sn F_20dcc D_20dcc. sn F_20dd0 D_20dd0. sn F_20dd4 D_20dd4. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20dd8 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20ed4 : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20ee8 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20dd8 D_20dd8. sn F_20ddc D_20ddc. sn F_20de0 D_20de0. sn F_20de4 D_20de4. sn F_20de8 D_20de8. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20dec : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20ee8 : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20efc /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20dec D_20dec. sn F_20df0 D_20df0. sn F_20df4 D_20df4. sn F_20df8 D_20df8. sn F_20dfc D_20dfc. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20e00 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20efc : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20f10 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 2 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20e00 D_20e00. sn F_20e04 D_20e04. sn F_20e08 D_20e08. sn F_20e0c D_20e0c. sn F_20e10 D_20e10. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20e14 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20f10 : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20f24 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 1 /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20e14 D_20e14. sn F_20e18 D_20e18. sn F_20e1c D_20e1c. sn F_20e20 D_20e20. sn F_20e24 D_20e24. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20e28 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20f24 : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20f38 /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 1 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20e28 D_20e28. sn F_20e2c D_20e2c. sn F_20e30 D_20e30. sn F_20e34 D_20e34. sn F_20e38 D_20e38. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20e3c : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20f38 : word) m rom) (mkst regs' (0x20454 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20f4c /\ getr regs' 10 = getr regs 9 /\ getr regs' 11 = Z_to_bv 64 2 /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 13 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20e3c D_20e3c. sn F_20e40 D_20e40. sn F_20e44 D_20e44. sn F_20e48 D_20e48. sn F_20e4c D_20e4c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
  Qed.

  Lemma hm_g_20e50 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x20f4c : word) m rom) (mkst regs' (0x20554 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x20f64 /\ getr regs' 10 = getr regs 8 /\ getr regs' 11 = getr regs 9 /\ getr regs' 12 = Z_to_bv 64 0x10542 /\ getr regs' 13 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_20e50 D_20e50. sn F_20e54 D_20e54. sn F_20e58 D_20e58. sn F_20e5c D_20e5c. sn F_20e60 D_20e60. sn F_20e64 D_20e64. apply mst_refl.
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
  Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + SELAHM_STACK <= s)%Z -> (s <= c_top C)%Z -> getr regs 4 = Z_to_bv 64 0x3d100 ->
  (RK10_sela <= kR)%Z -> (RB10_sela <= bR)%Z ->
  hminv C A m md s regs kR bR sela arr 0 2 Ak mk vmk rk sels vs ->
  (forall A2 m2 vm2 r2 sels' vs', hminv C A m md s regs kR bR sela arr (0 + 1) (2 + (3 + 3)) A2 m2 vm2 r2 sels' vs' ->
     realizes SEGS (mkCfg (mkst r2 (0x20954 : word) m2 al_rom) (with_vmmaps vm2 md)) S) ->
  realizes SEGS (mkCfg (mkst rk (0x20910 : word) mk al_rom) (with_vmmaps vmk md)) S.
Proof.
  intros C A m md s regs kR bR sela arr Ak mk vmk rk sels vs S CK Hs16 Hlo Hhi H4 HRK HRB INV HK.
  unfold RK10_sela in HRK. unfold RB10_sela, RB10_small in HRB.
  destruct (hm_g_20814 al_rom rk mk) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & Q14 & AG).
  apply (hm_brick_W C A m md s regs kR bR sela arr 0 2 Ak mk vmk rk sels vs 3 3 1 1 2 0x20928 (0x20910 : word) r' S CK Hs16 Hlo Hhi H4 INV RUN Q1 ltac:(red; apply bv_eq; reflexivity) Q10 Q11 Q12 Q13 Q14 AG
           ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold RB10_small; lia)).
  clear r' RUN Q1 Q10 Q11 Q12 Q13 Q14 AG. intros A1 m1 vm1 r1 sel arrd rows RS R10 HRM1.
  replace (Z_to_bv 64 0x20928) with (0x20928 : word) by (apply bv_eq; reflexivity).
  set (v := SELV 3 3 1 1 arrd 0 rows) in *.
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_2082c al_rom r1 m1) as (r' & RUN & Q1 & Q9 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 m1 vm1 r1 1 1 1 0x2093c (0x20928 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite (AG 10) by (notin_lit); exact R10) ltac:(rewrite Q9; exact R10) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q9 Q11 Q12 Q13 AG X2 X8 XR R10. intros ms1 rs1 RS R9.
  replace (Z_to_bv 64 0x2093c) with (0x2093c : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20840 al_rom rs1 ms1) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_add_W C A m md s regs kR bR sela arr 0 2 Ak mk vmk rk sels vs sel 3 3 1 1 arrd rows A1 ms1 vm1 rs1 0x10ffb 5 0x20954 (hm_name 0) hm_wd_0 (0x2093c : word) r' S
           CK Hs16 Hlo Hhi H4 INV ltac:(lia) RS HRM1 ltac:(lia) ltac:(unfold RB10_small; lia) RUN Q1 ltac:(red; apply bv_eq; reflexivity) ltac:(rewrite Q10; exact X8) ltac:(rewrite Q11; exact R9) Q12 Q13
           (AG 2%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) (AG 8%bv ltac:(notin_lit)) eq_refl eq_refl eq_refl
           ltac:(lia) ltac:(unfold hm_name, hm_names; simpl; lia) ltac:(unfold hm_name, hm_names; simpl; lia) hm_lit_0 hm_nz_0 ltac:(lia) ltac:(reflexivity) ltac:(unfold hm_name, hm_names; simpl; lia) hm_litw_0 hm_stop_0).
  intros A2 m2 vm2 r2 sels' vs' INV'. replace (Z_to_bv 64 0x20954) with (0x20954 : word) by (apply bv_eq; reflexivity).
  exact (HK A2 m2 vm2 r2 sels' vs' INV').
Qed.

Lemma hm_round_1 : forall C A m md (s : Z) regs (kR bR sela arr : Z) Ak mk vmk rk sels vs (S : TSet),
  Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + SELAHM_STACK <= s)%Z -> (s <= c_top C)%Z -> getr regs 4 = Z_to_bv 64 0x3d100 ->
  (RK10_sela <= kR)%Z -> (RB10_sela <= bR)%Z ->
  hminv C A m md s regs kR bR sela arr 1 8 Ak mk vmk rk sels vs ->
  (forall A2 m2 vm2 r2 sels' vs', hminv C A m md s regs kR bR sela arr (1 + 1) (8 + (3 + 2)) A2 m2 vm2 r2 sels' vs' ->
     realizes SEGS (mkCfg (mkst r2 (0x209c0 : word) m2 al_rom) (with_vmmaps vm2 md)) S) ->
  realizes SEGS (mkCfg (mkst rk (0x20954 : word) mk al_rom) (with_vmmaps vmk md)) S.
Proof.
  intros C A m md s regs kR bR sela arr Ak mk vmk rk sels vs S CK Hs16 Hlo Hhi H4 HRK HRB INV HK.
  unfold RK10_sela in HRK. unfold RB10_sela, RB10_small in HRB.
  destruct (hm_g_20858 al_rom rk mk) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & Q14 & AG).
  apply (hm_brick_W C A m md s regs kR bR sela arr 1 8 Ak mk vmk rk sels vs 2 3 0 1 1 0x2096c (0x20954 : word) r' S CK Hs16 Hlo Hhi H4 INV RUN Q1 ltac:(red; apply bv_eq; reflexivity) Q10 Q11 Q12 Q13 Q14 AG
           ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold RB10_small; lia)).
  clear r' RUN Q1 Q10 Q11 Q12 Q13 Q14 AG. intros A1 m1 vm1 r1 sel arrd rows RS R10 HRM1.
  replace (Z_to_bv 64 0x2096c) with (0x2096c : word) by (apply bv_eq; reflexivity).
  set (v := SELV 2 3 0 1 arrd 0 rows) in *.
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20870 al_rom r1 m1) as (r' & RUN & Q1 & Q9 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 m1 vm1 r1 1 0 2 0x20980 (0x2096c : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite (AG 10) by (notin_lit); exact R10) ltac:(rewrite Q9; exact R10) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q9 Q11 Q12 Q13 AG X2 X8 XR R10. intros ms1 rs1 RS R9.
  replace (Z_to_bv 64 0x20980) with (0x20980 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20884 al_rom rs1 ms1) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms1 vm1 rs1 1 1 2 0x20994 (0x20980 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms2 rs2 RS R9.
  replace (Z_to_bv 64 0x20994) with (0x20994 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20898 al_rom rs2 ms2) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms2 vm1 rs2 1 2 2 0x209a8 (0x20994 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms3 rs3 RS R9.
  replace (Z_to_bv 64 0x209a8) with (0x209a8 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_208ac al_rom rs3 ms3) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_add_W C A m md s regs kR bR sela arr 1 8 Ak mk vmk rk sels vs sel 2 3 0 1 arrd rows A1 ms3 vm1 rs3 0x10e92 6 0x209c0 (hm_name 1) hm_wd_1 (0x209a8 : word) r' S
           CK Hs16 Hlo Hhi H4 INV ltac:(lia) RS HRM1 ltac:(lia) ltac:(unfold RB10_small; lia) RUN Q1 ltac:(red; apply bv_eq; reflexivity) ltac:(rewrite Q10; exact X8) ltac:(rewrite Q11; exact R9) Q12 Q13
           (AG 2%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) (AG 8%bv ltac:(notin_lit)) eq_refl eq_refl eq_refl
           ltac:(lia) ltac:(unfold hm_name, hm_names; simpl; lia) ltac:(unfold hm_name, hm_names; simpl; lia) hm_lit_1 hm_nz_1 ltac:(lia) ltac:(reflexivity) ltac:(unfold hm_name, hm_names; simpl; lia) hm_litw_1 hm_stop_1).
  intros A2 m2 vm2 r2 sels' vs' INV'. replace (Z_to_bv 64 0x209c0) with (0x209c0 : word) by (apply bv_eq; reflexivity).
  exact (HK A2 m2 vm2 r2 sels' vs' INV').
Qed.

Lemma hm_round_2 : forall C A m md (s : Z) regs (kR bR sela arr : Z) Ak mk vmk rk sels vs (S : TSet),
  Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + SELAHM_STACK <= s)%Z -> (s <= c_top C)%Z -> getr regs 4 = Z_to_bv 64 0x3d100 ->
  (RK10_sela <= kR)%Z -> (RB10_sela <= bR)%Z ->
  hminv C A m md s regs kR bR sela arr 2 13 Ak mk vmk rk sels vs ->
  (forall A2 m2 vm2 r2 sels' vs', hminv C A m md s regs kR bR sela arr (2 + 1) (13 + (3 + 2)) A2 m2 vm2 r2 sels' vs' ->
     realizes SEGS (mkCfg (mkst r2 (0x20a2c : word) m2 al_rom) (with_vmmaps vm2 md)) S) ->
  realizes SEGS (mkCfg (mkst rk (0x209c0 : word) mk al_rom) (with_vmmaps vmk md)) S.
Proof.
  intros C A m md s regs kR bR sela arr Ak mk vmk rk sels vs S CK Hs16 Hlo Hhi H4 HRK HRB INV HK.
  unfold RK10_sela in HRK. unfold RB10_sela, RB10_small in HRB.
  destruct (hm_g_208c4 al_rom rk mk) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & Q14 & AG).
  apply (hm_brick_W C A m md s regs kR bR sela arr 2 13 Ak mk vmk rk sels vs 2 3 1 1 1 0x209d8 (0x209c0 : word) r' S CK Hs16 Hlo Hhi H4 INV RUN Q1 ltac:(red; apply bv_eq; reflexivity) Q10 Q11 Q12 Q13 Q14 AG
           ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold RB10_small; lia)).
  clear r' RUN Q1 Q10 Q11 Q12 Q13 Q14 AG. intros A1 m1 vm1 r1 sel arrd rows RS R10 HRM1.
  replace (Z_to_bv 64 0x209d8) with (0x209d8 : word) by (apply bv_eq; reflexivity).
  set (v := SELV 2 3 1 1 arrd 0 rows) in *.
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_208dc al_rom r1 m1) as (r' & RUN & Q1 & Q9 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 m1 vm1 r1 0 0 2 0x209ec (0x209d8 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite (AG 10) by (notin_lit); exact R10) ltac:(rewrite Q9; exact R10) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q9 Q11 Q12 Q13 AG X2 X8 XR R10. intros ms1 rs1 RS R9.
  replace (Z_to_bv 64 0x209ec) with (0x209ec : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_208f0 al_rom rs1 ms1) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms1 vm1 rs1 0 1 2 0x20a00 (0x209ec : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms2 rs2 RS R9.
  replace (Z_to_bv 64 0x20a00) with (0x20a00 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20904 al_rom rs2 ms2) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms2 vm1 rs2 0 2 2 0x20a14 (0x20a00 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms3 rs3 RS R9.
  replace (Z_to_bv 64 0x20a14) with (0x20a14 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20918 al_rom rs3 ms3) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_add_W C A m md s regs kR bR sela arr 2 13 Ak mk vmk rk sels vs sel 2 3 1 1 arrd rows A1 ms3 vm1 rs3 0x112ea 6 0x20a2c (hm_name 2) hm_wd_2 (0x20a14 : word) r' S
           CK Hs16 Hlo Hhi H4 INV ltac:(lia) RS HRM1 ltac:(lia) ltac:(unfold RB10_small; lia) RUN Q1 ltac:(red; apply bv_eq; reflexivity) ltac:(rewrite Q10; exact X8) ltac:(rewrite Q11; exact R9) Q12 Q13
           (AG 2%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) (AG 8%bv ltac:(notin_lit)) eq_refl eq_refl eq_refl
           ltac:(lia) ltac:(unfold hm_name, hm_names; simpl; lia) ltac:(unfold hm_name, hm_names; simpl; lia) hm_lit_2 hm_nz_2 ltac:(lia) ltac:(reflexivity) ltac:(unfold hm_name, hm_names; simpl; lia) hm_litw_2 hm_stop_2).
  intros A2 m2 vm2 r2 sels' vs' INV'. replace (Z_to_bv 64 0x20a2c) with (0x20a2c : word) by (apply bv_eq; reflexivity).
  exact (HK A2 m2 vm2 r2 sels' vs' INV').
Qed.

Lemma hm_round_3 : forall C A m md (s : Z) regs (kR bR sela arr : Z) Ak mk vmk rk sels vs (S : TSet),
  Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + SELAHM_STACK <= s)%Z -> (s <= c_top C)%Z -> getr regs 4 = Z_to_bv 64 0x3d100 ->
  (RK10_sela <= kR)%Z -> (RB10_sela <= bR)%Z ->
  hminv C A m md s regs kR bR sela arr 3 18 Ak mk vmk rk sels vs ->
  (forall A2 m2 vm2 r2 sels' vs', hminv C A m md s regs kR bR sela arr (3 + 1) (18 + (3 + 3)) A2 m2 vm2 r2 sels' vs' ->
     realizes SEGS (mkCfg (mkst r2 (0x20a98 : word) m2 al_rom) (with_vmmaps vm2 md)) S) ->
  realizes SEGS (mkCfg (mkst rk (0x20a2c : word) mk al_rom) (with_vmmaps vmk md)) S.
Proof.
  intros C A m md s regs kR bR sela arr Ak mk vmk rk sels vs S CK Hs16 Hlo Hhi H4 HRK HRB INV HK.
  unfold RK10_sela in HRK. unfold RB10_sela, RB10_small in HRB.
  destruct (hm_g_20930 al_rom rk mk) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & Q14 & AG).
  apply (hm_brick_W C A m md s regs kR bR sela arr 3 18 Ak mk vmk rk sels vs 3 2 1 0 1 0x20a44 (0x20a2c : word) r' S CK Hs16 Hlo Hhi H4 INV RUN Q1 ltac:(red; apply bv_eq; reflexivity) Q10 Q11 Q12 Q13 Q14 AG
           ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold RB10_small; lia)).
  clear r' RUN Q1 Q10 Q11 Q12 Q13 Q14 AG. intros A1 m1 vm1 r1 sel arrd rows RS R10 HRM1.
  replace (Z_to_bv 64 0x20a44) with (0x20a44 : word) by (apply bv_eq; reflexivity).
  set (v := SELV 3 2 1 0 arrd 0 rows) in *.
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20948 al_rom r1 m1) as (r' & RUN & Q1 & Q9 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 m1 vm1 r1 0 1 2 0x20a58 (0x20a44 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite (AG 10) by (notin_lit); exact R10) ltac:(rewrite Q9; exact R10) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q9 Q11 Q12 Q13 AG X2 X8 XR R10. intros ms1 rs1 RS R9.
  replace (Z_to_bv 64 0x20a58) with (0x20a58 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_2095c al_rom rs1 ms1) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms1 vm1 rs1 1 1 2 0x20a6c (0x20a58 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms2 rs2 RS R9.
  replace (Z_to_bv 64 0x20a6c) with (0x20a6c : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20970 al_rom rs2 ms2) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms2 vm1 rs2 2 1 2 0x20a80 (0x20a6c : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms3 rs3 RS R9.
  replace (Z_to_bv 64 0x20a80) with (0x20a80 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20984 al_rom rs3 ms3) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_add_W C A m md s regs kR bR sela arr 3 18 Ak mk vmk rk sels vs sel 3 2 1 0 arrd rows A1 ms3 vm1 rs3 0x11187 1 0x20a98 (hm_name 3) hm_wd_3 (0x20a80 : word) r' S
           CK Hs16 Hlo Hhi H4 INV ltac:(lia) RS HRM1 ltac:(lia) ltac:(unfold RB10_small; lia) RUN Q1 ltac:(red; apply bv_eq; reflexivity) ltac:(rewrite Q10; exact X8) ltac:(rewrite Q11; exact R9) Q12 Q13
           (AG 2%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) (AG 8%bv ltac:(notin_lit)) eq_refl eq_refl eq_refl
           ltac:(lia) ltac:(unfold hm_name, hm_names; simpl; lia) ltac:(unfold hm_name, hm_names; simpl; lia) hm_lit_3 hm_nz_3 ltac:(lia) ltac:(reflexivity) ltac:(unfold hm_name, hm_names; simpl; lia) hm_litw_3 hm_stop_3).
  intros A2 m2 vm2 r2 sels' vs' INV'. replace (Z_to_bv 64 0x20a98) with (0x20a98 : word) by (apply bv_eq; reflexivity).
  exact (HK A2 m2 vm2 r2 sels' vs' INV').
Qed.

Lemma hm_round_4 : forall C A m md (s : Z) regs (kR bR sela arr : Z) Ak mk vmk rk sels vs (S : TSet),
  Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + SELAHM_STACK <= s)%Z -> (s <= c_top C)%Z -> getr regs 4 = Z_to_bv 64 0x3d100 ->
  (RK10_sela <= kR)%Z -> (RB10_sela <= bR)%Z ->
  hminv C A m md s regs kR bR sela arr 4 24 Ak mk vmk rk sels vs ->
  (forall A2 m2 vm2 r2 sels' vs', hminv C A m md s regs kR bR sela arr (4 + 1) (24 + (3 + 3)) A2 m2 vm2 r2 sels' vs' ->
     realizes SEGS (mkCfg (mkst r2 (0x20b04 : word) m2 al_rom) (with_vmmaps vm2 md)) S) ->
  realizes SEGS (mkCfg (mkst rk (0x20a98 : word) mk al_rom) (with_vmmaps vmk md)) S.
Proof.
  intros C A m md s regs kR bR sela arr Ak mk vmk rk sels vs S CK Hs16 Hlo Hhi H4 HRK HRB INV HK.
  unfold RK10_sela in HRK. unfold RB10_sela, RB10_small in HRB.
  destruct (hm_g_2099c al_rom rk mk) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & Q14 & AG).
  apply (hm_brick_W C A m md s regs kR bR sela arr 4 24 Ak mk vmk rk sels vs 3 2 1 1 1 0x20ab0 (0x20a98 : word) r' S CK Hs16 Hlo Hhi H4 INV RUN Q1 ltac:(red; apply bv_eq; reflexivity) Q10 Q11 Q12 Q13 Q14 AG
           ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold RB10_small; lia)).
  clear r' RUN Q1 Q10 Q11 Q12 Q13 Q14 AG. intros A1 m1 vm1 r1 sel arrd rows RS R10 HRM1.
  replace (Z_to_bv 64 0x20ab0) with (0x20ab0 : word) by (apply bv_eq; reflexivity).
  set (v := SELV 3 2 1 1 arrd 0 rows) in *.
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_209b4 al_rom r1 m1) as (r' & RUN & Q1 & Q9 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 m1 vm1 r1 0 0 2 0x20ac4 (0x20ab0 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite (AG 10) by (notin_lit); exact R10) ltac:(rewrite Q9; exact R10) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q9 Q11 Q12 Q13 AG X2 X8 XR R10. intros ms1 rs1 RS R9.
  replace (Z_to_bv 64 0x20ac4) with (0x20ac4 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_209c8 al_rom rs1 ms1) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms1 vm1 rs1 1 0 2 0x20ad8 (0x20ac4 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms2 rs2 RS R9.
  replace (Z_to_bv 64 0x20ad8) with (0x20ad8 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_209dc al_rom rs2 ms2) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms2 vm1 rs2 2 0 2 0x20aec (0x20ad8 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms3 rs3 RS R9.
  replace (Z_to_bv 64 0x20aec) with (0x20aec : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_209f0 al_rom rs3 ms3) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_add_W C A m md s regs kR bR sela arr 4 24 Ak mk vmk rk sels vs sel 3 2 1 1 arrd rows A1 ms3 vm1 rs3 0x10609 7 0x20b04 (hm_name 4) hm_wd_4 (0x20aec : word) r' S
           CK Hs16 Hlo Hhi H4 INV ltac:(lia) RS HRM1 ltac:(lia) ltac:(unfold RB10_small; lia) RUN Q1 ltac:(red; apply bv_eq; reflexivity) ltac:(rewrite Q10; exact X8) ltac:(rewrite Q11; exact R9) Q12 Q13
           (AG 2%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) (AG 8%bv ltac:(notin_lit)) eq_refl eq_refl eq_refl
           ltac:(lia) ltac:(unfold hm_name, hm_names; simpl; lia) ltac:(unfold hm_name, hm_names; simpl; lia) hm_lit_4 hm_nz_4 ltac:(lia) ltac:(reflexivity) ltac:(unfold hm_name, hm_names; simpl; lia) hm_litw_4 hm_stop_4).
  intros A2 m2 vm2 r2 sels' vs' INV'. replace (Z_to_bv 64 0x20b04) with (0x20b04 : word) by (apply bv_eq; reflexivity).
  exact (HK A2 m2 vm2 r2 sels' vs' INV').
Qed.

Lemma hm_round_5 : forall C A m md (s : Z) regs (kR bR sela arr : Z) Ak mk vmk rk sels vs (S : TSet),
  Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + SELAHM_STACK <= s)%Z -> (s <= c_top C)%Z -> getr regs 4 = Z_to_bv 64 0x3d100 ->
  (RK10_sela <= kR)%Z -> (RB10_sela <= bR)%Z ->
  hminv C A m md s regs kR bR sela arr 5 30 Ak mk vmk rk sels vs ->
  (forall A2 m2 vm2 r2 sels' vs', hminv C A m md s regs kR bR sela arr (5 + 1) (30 + (3 + 13)) A2 m2 vm2 r2 sels' vs' ->
     realizes SEGS (mkCfg (mkst r2 (0x20bd4 : word) m2 al_rom) (with_vmmaps vm2 md)) S) ->
  realizes SEGS (mkCfg (mkst rk (0x20b04 : word) mk al_rom) (with_vmmaps vmk md)) S.
Proof.
  intros C A m md s regs kR bR sela arr Ak mk vmk rk sels vs S CK Hs16 Hlo Hhi H4 HRK HRB INV HK.
  unfold RK10_sela in HRK. unfold RB10_sela, RB10_small in HRB.
  destruct (hm_g_20a08 al_rom rk mk) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & Q14 & AG).
  apply (hm_brick_W C A m md s regs kR bR sela arr 5 30 Ak mk vmk rk sels vs 13 6 6 2 0 0x20b1c (0x20b04 : word) r' S CK Hs16 Hlo Hhi H4 INV RUN Q1 ltac:(red; apply bv_eq; reflexivity) Q10 Q11 Q12 Q13 Q14 AG
           ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold RB10_small; lia)).
  clear r' RUN Q1 Q10 Q11 Q12 Q13 Q14 AG. intros A1 m1 vm1 r1 sel arrd rows RS R10 HRM1.
  replace (Z_to_bv 64 0x20b1c) with (0x20b1c : word) by (apply bv_eq; reflexivity).
  set (v := SELV 13 6 6 2 arrd 0 rows) in *.
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20a20 al_rom r1 m1) as (r' & RUN & Q1 & Q9 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 m1 vm1 r1 0 3 2 0x20b30 (0x20b1c : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite (AG 10) by (notin_lit); exact R10) ltac:(rewrite Q9; exact R10) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q9 Q11 Q12 Q13 AG X2 X8 XR R10. intros ms1 rs1 RS R9.
  replace (Z_to_bv 64 0x20b30) with (0x20b30 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20a34 al_rom rs1 ms1) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms1 vm1 rs1 0 5 1 0x20b44 (0x20b30 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms2 rs2 RS R9.
  replace (Z_to_bv 64 0x20b44) with (0x20b44 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20a48 al_rom rs2 ms2) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms2 vm1 rs2 4 2 2 0x20b58 (0x20b44 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms3 rs3 RS R9.
  replace (Z_to_bv 64 0x20b58) with (0x20b58 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20a5c al_rom rs3 ms3) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms3 vm1 rs3 4 4 1 0x20b6c (0x20b58 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms4 rs4 RS R9.
  replace (Z_to_bv 64 0x20b6c) with (0x20b6c : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20a70 al_rom rs4 ms4) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms4 vm1 rs4 8 1 2 0x20b80 (0x20b6c : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms5 rs5 RS R9.
  replace (Z_to_bv 64 0x20b80) with (0x20b80 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20a84 al_rom rs5 ms5) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms5 vm1 rs5 8 3 1 0x20b94 (0x20b80 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms6 rs6 RS R9.
  replace (Z_to_bv 64 0x20b94) with (0x20b94 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20a98 al_rom rs6 ms6) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms6 vm1 rs6 12 0 2 0x20ba8 (0x20b94 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms7 rs7 RS R9.
  replace (Z_to_bv 64 0x20ba8) with (0x20ba8 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20aac al_rom rs7 ms7) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms7 vm1 rs7 12 2 1 0x20bbc (0x20ba8 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms8 rs8 RS R9.
  replace (Z_to_bv 64 0x20bbc) with (0x20bbc : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20ac0 al_rom rs8 ms8) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_add_W C A m md s regs kR bR sela arr 5 30 Ak mk vmk rk sels vs sel 13 6 6 2 arrd rows A1 ms8 vm1 rs8 0x11543 5 0x20bd4 (hm_name 5) hm_wd_5 (0x20bbc : word) r' S
           CK Hs16 Hlo Hhi H4 INV ltac:(lia) RS HRM1 ltac:(lia) ltac:(unfold RB10_small; lia) RUN Q1 ltac:(red; apply bv_eq; reflexivity) ltac:(rewrite Q10; exact X8) ltac:(rewrite Q11; exact R9) Q12 Q13
           (AG 2%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) (AG 8%bv ltac:(notin_lit)) eq_refl eq_refl eq_refl
           ltac:(lia) ltac:(unfold hm_name, hm_names; simpl; lia) ltac:(unfold hm_name, hm_names; simpl; lia) hm_lit_5 hm_nz_5 ltac:(lia) ltac:(reflexivity) ltac:(unfold hm_name, hm_names; simpl; lia) hm_litw_5 hm_stop_5).
  intros A2 m2 vm2 r2 sels' vs' INV'. replace (Z_to_bv 64 0x20bd4) with (0x20bd4 : word) by (apply bv_eq; reflexivity).
  exact (HK A2 m2 vm2 r2 sels' vs' INV').
Qed.

Lemma hm_round_6 : forall C A m md (s : Z) regs (kR bR sela arr : Z) Ak mk vmk rk sels vs (S : TSet),
  Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + SELAHM_STACK <= s)%Z -> (s <= c_top C)%Z -> getr regs 4 = Z_to_bv 64 0x3d100 ->
  (RK10_sela <= kR)%Z -> (RB10_sela <= bR)%Z ->
  hminv C A m md s regs kR bR sela arr 6 46 Ak mk vmk rk sels vs ->
  (forall A2 m2 vm2 r2 sels' vs', hminv C A m md s regs kR bR sela arr (6 + 1) (46 + (3 + 4)) A2 m2 vm2 r2 sels' vs' ->
     realizes SEGS (mkCfg (mkst r2 (0x20cb8 : word) m2 al_rom) (with_vmmaps vm2 md)) S) ->
  realizes SEGS (mkCfg (mkst rk (0x20bd4 : word) mk al_rom) (with_vmmaps vmk md)) S.
Proof.
  intros C A m md s regs kR bR sela arr Ak mk vmk rk sels vs S CK Hs16 Hlo Hhi H4 HRK HRB INV HK.
  unfold RK10_sela in HRK. unfold RB10_sela, RB10_small in HRB.
  destruct (hm_g_20ad8 al_rom rk mk) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & Q14 & AG).
  apply (hm_brick_W C A m md s regs kR bR sela arr 6 46 Ak mk vmk rk sels vs 4 4 1 1 2 0x20bec (0x20bd4 : word) r' S CK Hs16 Hlo Hhi H4 INV RUN Q1 ltac:(red; apply bv_eq; reflexivity) Q10 Q11 Q12 Q13 Q14 AG
           ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold RB10_small; lia)).
  clear r' RUN Q1 Q10 Q11 Q12 Q13 Q14 AG. intros A1 m1 vm1 r1 sel arrd rows RS R10 HRM1.
  replace (Z_to_bv 64 0x20bec) with (0x20bec : word) by (apply bv_eq; reflexivity).
  set (v := SELV 4 4 1 1 arrd 0 rows) in *.
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20af0 al_rom r1 m1) as (r' & RUN & Q1 & Q9 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 m1 vm1 r1 1 1 0 0x20c00 (0x20bec : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite (AG 10) by (notin_lit); exact R10) ltac:(rewrite Q9; exact R10) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q9 Q11 Q12 Q13 AG X2 X8 XR R10. intros ms1 rs1 RS R9.
  replace (Z_to_bv 64 0x20c00) with (0x20c00 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20b04 al_rom rs1 ms1) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms1 vm1 rs1 1 2 0 0x20c14 (0x20c00 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms2 rs2 RS R9.
  replace (Z_to_bv 64 0x20c14) with (0x20c14 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20b18 al_rom rs2 ms2) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms2 vm1 rs2 2 1 0 0x20c28 (0x20c14 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms3 rs3 RS R9.
  replace (Z_to_bv 64 0x20c28) with (0x20c28 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20b2c al_rom rs3 ms3) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms3 vm1 rs3 1 3 1 0x20c3c (0x20c28 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms4 rs4 RS R9.
  replace (Z_to_bv 64 0x20c3c) with (0x20c3c : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20b40 al_rom rs4 ms4) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms4 vm1 rs4 2 2 1 0x20c50 (0x20c3c : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms5 rs5 RS R9.
  replace (Z_to_bv 64 0x20c50) with (0x20c50 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20b54 al_rom rs5 ms5) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms5 vm1 rs5 2 3 1 0x20c64 (0x20c50 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms6 rs6 RS R9.
  replace (Z_to_bv 64 0x20c64) with (0x20c64 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20b68 al_rom rs6 ms6) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms6 vm1 rs6 3 1 1 0x20c78 (0x20c64 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms7 rs7 RS R9.
  replace (Z_to_bv 64 0x20c78) with (0x20c78 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20b7c al_rom rs7 ms7) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms7 vm1 rs7 3 2 1 0x20c8c (0x20c78 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms8 rs8 RS R9.
  replace (Z_to_bv 64 0x20c8c) with (0x20c8c : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20b90 al_rom rs8 ms8) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms8 vm1 rs8 3 3 1 0x20ca0 (0x20c8c : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms9 rs9 RS R9.
  replace (Z_to_bv 64 0x20ca0) with (0x20ca0 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20ba4 al_rom rs9 ms9) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_add_W C A m md s regs kR bR sela arr 6 46 Ak mk vmk rk sels vs sel 4 4 1 1 arrd rows A1 ms9 vm1 rs9 0x10d34 4 0x20cb8 (hm_name 6) hm_wd_6 (0x20ca0 : word) r' S
           CK Hs16 Hlo Hhi H4 INV ltac:(lia) RS HRM1 ltac:(lia) ltac:(unfold RB10_small; lia) RUN Q1 ltac:(red; apply bv_eq; reflexivity) ltac:(rewrite Q10; exact X8) ltac:(rewrite Q11; exact R9) Q12 Q13
           (AG 2%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) (AG 8%bv ltac:(notin_lit)) eq_refl eq_refl eq_refl
           ltac:(lia) ltac:(unfold hm_name, hm_names; simpl; lia) ltac:(unfold hm_name, hm_names; simpl; lia) hm_lit_6 hm_nz_6 ltac:(lia) ltac:(reflexivity) ltac:(unfold hm_name, hm_names; simpl; lia) hm_litw_6 hm_stop_6).
  intros A2 m2 vm2 r2 sels' vs' INV'. replace (Z_to_bv 64 0x20cb8) with (0x20cb8 : word) by (apply bv_eq; reflexivity).
  exact (HK A2 m2 vm2 r2 sels' vs' INV').
Qed.

Lemma hm_round_7 : forall C A m md (s : Z) regs (kR bR sela arr : Z) Ak mk vmk rk sels vs (S : TSet),
  Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + SELAHM_STACK <= s)%Z -> (s <= c_top C)%Z -> getr regs 4 = Z_to_bv 64 0x3d100 ->
  (RK10_sela <= kR)%Z -> (RB10_sela <= bR)%Z ->
  hminv C A m md s regs kR bR sela arr 7 53 Ak mk vmk rk sels vs ->
  (forall A2 m2 vm2 r2 sels' vs', hminv C A m md s regs kR bR sela arr (7 + 1) (53 + (3 + 4)) A2 m2 vm2 r2 sels' vs' ->
     realizes SEGS (mkCfg (mkst r2 (0x20d9c : word) m2 al_rom) (with_vmmaps vm2 md)) S) ->
  realizes SEGS (mkCfg (mkst rk (0x20cb8 : word) mk al_rom) (with_vmmaps vmk md)) S.
Proof.
  intros C A m md s regs kR bR sela arr Ak mk vmk rk sels vs S CK Hs16 Hlo Hhi H4 HRK HRB INV HK.
  unfold RK10_sela in HRK. unfold RB10_sela, RB10_small in HRB.
  destruct (hm_g_20bbc al_rom rk mk) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & Q14 & AG).
  apply (hm_brick_W C A m md s regs kR bR sela arr 7 53 Ak mk vmk rk sels vs 4 4 1 2 2 0x20cd0 (0x20cb8 : word) r' S CK Hs16 Hlo Hhi H4 INV RUN Q1 ltac:(red; apply bv_eq; reflexivity) Q10 Q11 Q12 Q13 Q14 AG
           ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold RB10_small; lia)).
  clear r' RUN Q1 Q10 Q11 Q12 Q13 Q14 AG. intros A1 m1 vm1 r1 sel arrd rows RS R10 HRM1.
  replace (Z_to_bv 64 0x20cd0) with (0x20cd0 : word) by (apply bv_eq; reflexivity).
  set (v := SELV 4 4 1 2 arrd 0 rows) in *.
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20bd4 al_rom r1 m1) as (r' & RUN & Q1 & Q9 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 m1 vm1 r1 1 1 0 0x20ce4 (0x20cd0 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite (AG 10) by (notin_lit); exact R10) ltac:(rewrite Q9; exact R10) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q9 Q11 Q12 Q13 AG X2 X8 XR R10. intros ms1 rs1 RS R9.
  replace (Z_to_bv 64 0x20ce4) with (0x20ce4 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20be8 al_rom rs1 ms1) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms1 vm1 rs1 1 2 0 0x20cf8 (0x20ce4 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms2 rs2 RS R9.
  replace (Z_to_bv 64 0x20cf8) with (0x20cf8 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20bfc al_rom rs2 ms2) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms2 vm1 rs2 2 2 0 0x20d0c (0x20cf8 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms3 rs3 RS R9.
  replace (Z_to_bv 64 0x20d0c) with (0x20d0c : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20c10 al_rom rs3 ms3) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms3 vm1 rs3 1 0 1 0x20d20 (0x20d0c : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms4 rs4 RS R9.
  replace (Z_to_bv 64 0x20d20) with (0x20d20 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20c24 al_rom rs4 ms4) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms4 vm1 rs4 2 0 1 0x20d34 (0x20d20 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms5 rs5 RS R9.
  replace (Z_to_bv 64 0x20d34) with (0x20d34 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20c38 al_rom rs5 ms5) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms5 vm1 rs5 2 1 1 0x20d48 (0x20d34 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms6 rs6 RS R9.
  replace (Z_to_bv 64 0x20d48) with (0x20d48 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20c4c al_rom rs6 ms6) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms6 vm1 rs6 3 0 1 0x20d5c (0x20d48 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms7 rs7 RS R9.
  replace (Z_to_bv 64 0x20d5c) with (0x20d5c : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20c60 al_rom rs7 ms7) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms7 vm1 rs7 3 1 1 0x20d70 (0x20d5c : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms8 rs8 RS R9.
  replace (Z_to_bv 64 0x20d70) with (0x20d70 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20c74 al_rom rs8 ms8) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms8 vm1 rs8 3 2 1 0x20d84 (0x20d70 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms9 rs9 RS R9.
  replace (Z_to_bv 64 0x20d84) with (0x20d84 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20c88 al_rom rs9 ms9) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_add_W C A m md s regs kR bR sela arr 7 53 Ak mk vmk rk sels vs sel 4 4 1 2 arrd rows A1 ms9 vm1 rs9 0x10422 6 0x20d9c (hm_name 7) hm_wd_7 (0x20d84 : word) r' S
           CK Hs16 Hlo Hhi H4 INV ltac:(lia) RS HRM1 ltac:(lia) ltac:(unfold RB10_small; lia) RUN Q1 ltac:(red; apply bv_eq; reflexivity) ltac:(rewrite Q10; exact X8) ltac:(rewrite Q11; exact R9) Q12 Q13
           (AG 2%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) (AG 8%bv ltac:(notin_lit)) eq_refl eq_refl eq_refl
           ltac:(lia) ltac:(unfold hm_name, hm_names; simpl; lia) ltac:(unfold hm_name, hm_names; simpl; lia) hm_lit_7 hm_nz_7 ltac:(lia) ltac:(reflexivity) ltac:(unfold hm_name, hm_names; simpl; lia) hm_litw_7 hm_stop_7).
  intros A2 m2 vm2 r2 sels' vs' INV'. replace (Z_to_bv 64 0x20d9c) with (0x20d9c : word) by (apply bv_eq; reflexivity).
  exact (HK A2 m2 vm2 r2 sels' vs' INV').
Qed.

Lemma hm_round_8 : forall C A m md (s : Z) regs (kR bR sela arr : Z) Ak mk vmk rk sels vs (S : TSet),
  Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + SELAHM_STACK <= s)%Z -> (s <= c_top C)%Z -> getr regs 4 = Z_to_bv 64 0x3d100 ->
  (RK10_sela <= kR)%Z -> (RB10_sela <= bR)%Z ->
  hminv C A m md s regs kR bR sela arr 8 60 Ak mk vmk rk sels vs ->
  (forall A2 m2 vm2 r2 sels' vs', hminv C A m md s regs kR bR sela arr (8 + 1) (60 + (3 + 4)) A2 m2 vm2 r2 sels' vs' ->
     realizes SEGS (mkCfg (mkst r2 (0x20e80 : word) m2 al_rom) (with_vmmaps vm2 md)) S) ->
  realizes SEGS (mkCfg (mkst rk (0x20d9c : word) mk al_rom) (with_vmmaps vmk md)) S.
Proof.
  intros C A m md s regs kR bR sela arr Ak mk vmk rk sels vs S CK Hs16 Hlo Hhi H4 HRK HRB INV HK.
  unfold RK10_sela in HRK. unfold RB10_sela, RB10_small in HRB.
  destruct (hm_g_20ca0 al_rom rk mk) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & Q14 & AG).
  apply (hm_brick_W C A m md s regs kR bR sela arr 8 60 Ak mk vmk rk sels vs 4 4 2 1 2 0x20db4 (0x20d9c : word) r' S CK Hs16 Hlo Hhi H4 INV RUN Q1 ltac:(red; apply bv_eq; reflexivity) Q10 Q11 Q12 Q13 Q14 AG
           ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold RB10_small; lia)).
  clear r' RUN Q1 Q10 Q11 Q12 Q13 Q14 AG. intros A1 m1 vm1 r1 sel arrd rows RS R10 HRM1.
  replace (Z_to_bv 64 0x20db4) with (0x20db4 : word) by (apply bv_eq; reflexivity).
  set (v := SELV 4 4 2 1 arrd 0 rows) in *.
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20cb8 al_rom r1 m1) as (r' & RUN & Q1 & Q9 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 m1 vm1 r1 1 1 0 0x20dc8 (0x20db4 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite (AG 10) by (notin_lit); exact R10) ltac:(rewrite Q9; exact R10) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q9 Q11 Q12 Q13 AG X2 X8 XR R10. intros ms1 rs1 RS R9.
  replace (Z_to_bv 64 0x20dc8) with (0x20dc8 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20ccc al_rom rs1 ms1) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms1 vm1 rs1 2 1 0 0x20ddc (0x20dc8 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms2 rs2 RS R9.
  replace (Z_to_bv 64 0x20ddc) with (0x20ddc : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20ce0 al_rom rs2 ms2) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms2 vm1 rs2 2 2 0 0x20df0 (0x20ddc : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms3 rs3 RS R9.
  replace (Z_to_bv 64 0x20df0) with (0x20df0 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20cf4 al_rom rs3 ms3) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms3 vm1 rs3 0 1 1 0x20e04 (0x20df0 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms4 rs4 RS R9.
  replace (Z_to_bv 64 0x20e04) with (0x20e04 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20d08 al_rom rs4 ms4) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms4 vm1 rs4 0 2 1 0x20e18 (0x20e04 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms5 rs5 RS R9.
  replace (Z_to_bv 64 0x20e18) with (0x20e18 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20d1c al_rom rs5 ms5) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms5 vm1 rs5 0 3 1 0x20e2c (0x20e18 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms6 rs6 RS R9.
  replace (Z_to_bv 64 0x20e2c) with (0x20e2c : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20d30 al_rom rs6 ms6) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms6 vm1 rs6 1 2 1 0x20e40 (0x20e2c : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms7 rs7 RS R9.
  replace (Z_to_bv 64 0x20e40) with (0x20e40 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20d44 al_rom rs7 ms7) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms7 vm1 rs7 1 3 1 0x20e54 (0x20e40 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms8 rs8 RS R9.
  replace (Z_to_bv 64 0x20e54) with (0x20e54 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20d58 al_rom rs8 ms8) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms8 vm1 rs8 2 3 1 0x20e68 (0x20e54 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms9 rs9 RS R9.
  replace (Z_to_bv 64 0x20e68) with (0x20e68 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20d6c al_rom rs9 ms9) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_add_W C A m md s regs kR bR sela arr 8 60 Ak mk vmk rk sels vs sel 4 4 2 1 arrd rows A1 ms9 vm1 rs9 0x10f24 4 0x20e80 (hm_name 8) hm_wd_8 (0x20e68 : word) r' S
           CK Hs16 Hlo Hhi H4 INV ltac:(lia) RS HRM1 ltac:(lia) ltac:(unfold RB10_small; lia) RUN Q1 ltac:(red; apply bv_eq; reflexivity) ltac:(rewrite Q10; exact X8) ltac:(rewrite Q11; exact R9) Q12 Q13
           (AG 2%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) (AG 8%bv ltac:(notin_lit)) eq_refl eq_refl eq_refl
           ltac:(lia) ltac:(unfold hm_name, hm_names; simpl; lia) ltac:(unfold hm_name, hm_names; simpl; lia) hm_lit_8 hm_nz_8 ltac:(lia) ltac:(reflexivity) ltac:(unfold hm_name, hm_names; simpl; lia) hm_litw_8 hm_stop_8).
  intros A2 m2 vm2 r2 sels' vs' INV'. replace (Z_to_bv 64 0x20e80) with (0x20e80 : word) by (apply bv_eq; reflexivity).
  exact (HK A2 m2 vm2 r2 sels' vs' INV').
Qed.

Lemma hm_round_9 : forall C A m md (s : Z) regs (kR bR sela arr : Z) Ak mk vmk rk sels vs (S : TSet),
  Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + SELAHM_STACK <= s)%Z -> (s <= c_top C)%Z -> getr regs 4 = Z_to_bv 64 0x3d100 ->
  (RK10_sela <= kR)%Z -> (RB10_sela <= bR)%Z ->
  hminv C A m md s regs kR bR sela arr 9 67 Ak mk vmk rk sels vs ->
  (forall A2 m2 vm2 r2 sels' vs', hminv C A m md s regs kR bR sela arr (9 + 1) (67 + (3 + 4)) A2 m2 vm2 r2 sels' vs' ->
     realizes SEGS (mkCfg (mkst r2 (0x20f64 : word) m2 al_rom) (with_vmmaps vm2 md)) S) ->
  realizes SEGS (mkCfg (mkst rk (0x20e80 : word) mk al_rom) (with_vmmaps vmk md)) S.
Proof.
  intros C A m md s regs kR bR sela arr Ak mk vmk rk sels vs S CK Hs16 Hlo Hhi H4 HRK HRB INV HK.
  unfold RK10_sela in HRK. unfold RB10_sela, RB10_small in HRB.
  destruct (hm_g_20d84 al_rom rk mk) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & Q14 & AG).
  apply (hm_brick_W C A m md s regs kR bR sela arr 9 67 Ak mk vmk rk sels vs 4 4 2 2 2 0x20e98 (0x20e80 : word) r' S CK Hs16 Hlo Hhi H4 INV RUN Q1 ltac:(red; apply bv_eq; reflexivity) Q10 Q11 Q12 Q13 Q14 AG
           ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold RB10_small; lia)).
  clear r' RUN Q1 Q10 Q11 Q12 Q13 Q14 AG. intros A1 m1 vm1 r1 sel arrd rows RS R10 HRM1.
  replace (Z_to_bv 64 0x20e98) with (0x20e98 : word) by (apply bv_eq; reflexivity).
  set (v := SELV 4 4 2 2 arrd 0 rows) in *.
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20d9c al_rom r1 m1) as (r' & RUN & Q1 & Q9 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 m1 vm1 r1 1 2 0 0x20eac (0x20e98 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite (AG 10) by (notin_lit); exact R10) ltac:(rewrite Q9; exact R10) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q9 Q11 Q12 Q13 AG X2 X8 XR R10. intros ms1 rs1 RS R9.
  replace (Z_to_bv 64 0x20eac) with (0x20eac : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20db0 al_rom rs1 ms1) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms1 vm1 rs1 2 1 0 0x20ec0 (0x20eac : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms2 rs2 RS R9.
  replace (Z_to_bv 64 0x20ec0) with (0x20ec0 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20dc4 al_rom rs2 ms2) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms2 vm1 rs2 2 2 0 0x20ed4 (0x20ec0 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms3 rs3 RS R9.
  replace (Z_to_bv 64 0x20ed4) with (0x20ed4 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20dd8 al_rom rs3 ms3) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms3 vm1 rs3 0 0 1 0x20ee8 (0x20ed4 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms4 rs4 RS R9.
  replace (Z_to_bv 64 0x20ee8) with (0x20ee8 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20dec al_rom rs4 ms4) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms4 vm1 rs4 0 1 1 0x20efc (0x20ee8 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms5 rs5 RS R9.
  replace (Z_to_bv 64 0x20efc) with (0x20efc : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20e00 al_rom rs5 ms5) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms5 vm1 rs5 0 2 1 0x20f10 (0x20efc : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms6 rs6 RS R9.
  replace (Z_to_bv 64 0x20f10) with (0x20f10 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20e14 al_rom rs6 ms6) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms6 vm1 rs6 1 0 1 0x20f24 (0x20f10 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms7 rs7 RS R9.
  replace (Z_to_bv 64 0x20f24) with (0x20f24 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20e28 al_rom rs7 ms7) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms7 vm1 rs7 1 1 1 0x20f38 (0x20f24 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms8 rs8 RS R9.
  replace (Z_to_bv 64 0x20f38) with (0x20f38 : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20e3c al_rom rs8 ms8) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_set_W C Ak mk md s regs sela sel v A1 ms8 vm1 rs8 2 0 1 0x20f4c (0x20f38 : word) r' S CK Hlo Hhi RS RUN Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite Q10; exact R9) ltac:(rewrite (AG 9) by (notin_lit); exact R9) Q11 Q12 Q13 (AG 2%bv ltac:(notin_lit)) (AG 8%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)).
  clear RS r' RUN Q1 Q10 Q11 Q12 Q13 AG X2 X8 XR R9. intros ms9 rs9 RS R9.
  replace (Z_to_bv 64 0x20f4c) with (0x20f4c : word) by (apply bv_eq; reflexivity).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & X2 & X8 & XR).
  destruct (hm_g_20e50 al_rom rs9 ms9) as (r' & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & AG).
  apply (hm_add_W C A m md s regs kR bR sela arr 9 67 Ak mk vmk rk sels vs sel 4 4 2 2 arrd rows A1 ms9 vm1 rs9 0x10542 6 0x20f64 (hm_name 9) hm_wd_9 (0x20f4c : word) r' S
           CK Hs16 Hlo Hhi H4 INV ltac:(lia) RS HRM1 ltac:(lia) ltac:(unfold RB10_small; lia) RUN Q1 ltac:(red; apply bv_eq; reflexivity) ltac:(rewrite Q10; exact X8) ltac:(rewrite Q11; exact R9) Q12 Q13
           (AG 2%bv ltac:(notin_lit)) ltac:(intros x Hx; apply AG; revert x Hx; notin_rest) (AG 8%bv ltac:(notin_lit)) eq_refl eq_refl eq_refl
           ltac:(lia) ltac:(unfold hm_name, hm_names; simpl; lia) ltac:(unfold hm_name, hm_names; simpl; lia) hm_lit_9 hm_nz_9 ltac:(lia) ltac:(reflexivity) ltac:(unfold hm_name, hm_names; simpl; lia) hm_litw_9 hm_stop_9).
  intros A2 m2 vm2 r2 sels' vs' INV'. replace (Z_to_bv 64 0x20f64) with (0x20f64 : word) by (apply bv_eq; reflexivity).
  exact (HK A2 m2 vm2 r2 sels' vs' INV').
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem selaAddHitMiss_W : selaAddHitMiss_contract.
Proof.
  intros C A m md regs s ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 kR bR HRM HRK HRB HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LL16] in *.
  pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
  assert (HsS : (c_top C - LSTK + 32 + 32 + CALLOC_STACK <= s)%Z) by (unfold SELAHM_STACK in Hlo; lia).
  assert (HsS' : (c_top C - LSTK + 64 <= s)%Z) by (unfold CALLOC_STACK, ALLOC_STACK in HsS; lia).
  unfold PC_selaAddHitMiss. replace (Z_to_bv 64 0x208ec) with (0x208ec : word) by (apply bv_eq; reflexivity).
  destruct (hm_sA al_rom regs m s ret ltac:(lia) ltac:(lia) (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := HMF m s ret regs).
  assert (WP1 : W C A M1 md /\ POSTM C A s m M1) by (subst M1; unfold HMF; wp_win CK).
  destruct WP1 as [HW1 PM1].
  pose proof (hmcells_HMF m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1. rewrite <- H1 in CE1.
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x3d100) by (rewrite (AG1 4) by notin_lit; exact H4).
  assert (HRK2 : (2 <= kR)%Z) by (unfold RK10_sela in HRK; lia).
  assert (HRB2 : (2 * RB10_small <= bR)%Z) by (unfold RB10_sela, RB10_small in *; lia).
  apply (selaCreate_W C A M1 md r1 (s - 32) (Z_to_bv 64 0x20908) S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity) Q4 Q10 kR bR HRM HRK2 HRB2).
  intros A1 m1 vm1 r2 sela arr HWa CSa PMa R10 SLA0 LsA LaA Ls0 La0 LEQ HRMa.
  replace (Z_to_bv 64 0x20908) with (0x20908 : word) by (apply bv_eq; reflexivity).
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
