(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 LeptRecs LeptSel LeptSlots LeptExecT LeptExecB.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC LeptRoom14 LeptRoomBL.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptDilW V23LeptMbc V23LeptCloseSpec V23LeptCloseIface V23LeptCselsSpec V23LeptCloseSegs V23LeptCloseA V23LeptSelDW.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptPixHdr O23LeptCmapValid O23LeptPixCopyT O23LeptCloseSpec O23LeptCloseIface O23LeptCloseSegs O23LeptCloseA O23LeptCloseT.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section CloseT.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Ltac rzs HW RUN := eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].

(* [comment removed for export] *)
Lemma csc_exit : forall (fr : bvmap 5 word) C Ar A m md regs (s pix1 vs w h cm datas : Z) (cv : cmapv) (ret : word) (S : TSet) (kR bR : Z)
    (fr1 : bvmap 5 word) (cs1 : bv 32) (A9 : AS) (m9 : word -> option byte) (vm9 : VmMaps) (r9 : bvmap 5 word) (cm' : Z) (cv' : cmapv) (kx bx : Z),
  Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + CSC_STACK <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret ->
  getr regs 2 = Z_to_bv 64 s ->
  frm_zero cs1 -> (forall r : reg, In (u r) fs_list -> reg_get fr1 r = reg_get fr r) ->
  W C A9 m9 (with_vmmaps vm9 md) ->
  getr r9 2 = Z_to_bv 64 (s - 112) -> getr r9 8 = Z_to_bv 64 pix1 -> O23LeptCloseT.rkept regs r9 ->
  FRS m9 s ret regs ->
  sub_live Ar A9 -> POSTM C Ar s m m9 ->
  O23LeptCloseSpec.pix1_at C Ar A9 m9 pix1 w h cm' datas cv' -> O23LeptCloseA.cslm (fun _ => False) A A9 cm cv cm' cv' ->
  aroom A9 vm9 kx bx -> (kR - O23LeptCloseSpec.RK_csc vs <= kx)%Z -> (bR - O23LeptCloseSpec.RB_csc vs w h cm <= bx)%Z -> (0 <= kR - O23LeptCloseSpec.RK_csc vs)%Z -> (0 <= bR - O23LeptCloseSpec.RB_csc vs w h cm)%Z ->
  csc_K fr C Ar A m md regs s pix1 vs w h cm datas cv ret S kR bR ->
  realizes SEGS (mkCfg (@mkst (mkFP fr1 cs1) r9 (0xa4c50 : word) m9 al_rom) (with_vmmaps vm9 md)) S.
Proof.
  intros fr C Ar A m md regs s pix1 vs w h cm datas cv ret S kR bR fr1 cs1 A9 m9 vm9 r9 cm' cv' kx bx
    CK Hs16 Hlo Hhi Hret H2 FZ FK HW9 R2 R8 RK FS SUB PM P1 CSL ROOM Hk Hb Hk0 Hb0 HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. unfold CSC_STACK in Hlo.
  pose proof (u64_range (c_sp0 C)) as SP.
  destruct FS as (F1 & F2 & F3 & F4 & F5 & F6).
  destruct (@cs_Z (mkFP fr1 cs1) al_rom r9 m9 s pix1 ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20)
              ltac:(lia) ltac:(lia) Hret F1 F2 F3 F4 F5 F6 R2 R8)
    as (r' & RUN & Z2 & Z10 & Z8 & Z9 & Z18 & Z19 & Z20 & AG).
  rzs HW9 RUN.
  apply (HK fr1 cs1 A9 m9 vm9 r' cm' cv' FZ FK HW9).
  - assert (RKr : forall x, In x [3; 4; 21; 22; 23; 24; 25; 26; 27]%list -> getr r' x = getr regs x)
      by (intros x Hx; rewrite <- (RK x Hx); apply AG; cbn [In] in Hx |- *;
          repeat (destruct Hx as [<-|Hx]; [notin_lit|]); destruct Hx).
    apply cs_kept_intro.
    + rewrite Z2, H2. reflexivity.
    + exact (RKr 3%bv ltac:(in_lit)).
    + exact (RKr 4%bv ltac:(in_lit)).
    + exact Z8.
    + exact Z9.
    + exact Z18.
    + exact Z19.
    + exact Z20.
    + exact (RKr 21%bv ltac:(in_lit)).
    + exact (RKr 22%bv ltac:(in_lit)).
    + exact (RKr 23%bv ltac:(in_lit)).
    + exact (RKr 24%bv ltac:(in_lit)).
    + exact (RKr 25%bv ltac:(in_lit)).
    + exact (RKr 26%bv ltac:(in_lit)).
    + exact (RKr 27%bv ltac:(in_lit)).
  - exact Z10.
  - exact SUB.
  - exact PM.
  - exact P1.
  - exact (O23LeptCloseA.cslm_final A A9 cm cv cm' cv' CSL).
  - apply (aroom_mono A9 vm9 kx bx); [exact ROOM | lia | lia].
Qed.


(* [comment removed for export] *)
Lemma seld_real : forall (fx : FPState) C Ar Ak mk vk md r (s psel sel : Z) (sv : selv) (retpc : word) (S : TSet) (kx bx : Z),
  Cok C -> W C Ak mk (with_vmmaps vk md) -> (s mod 16 = 0)%Z -> (c_top C - LSTK + CSC_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr r 2 = Z_to_bv 64 (s - 112) -> (s - 112 <= psel)%Z -> (psel + 8 <= s)%Z -> (psel mod 8 = 0)%Z ->
  getr r 1 = retpc -> ret_ok retpc -> getr r 4 = Z_to_bv 64 0x1381d0 -> getr r 10 = Z_to_bv 64 psel ->
  rdn SEGS mk (Z_to_bv 64 psel) 8 = Some (Z_to_le_bytes 8 sel) ->
  sel_at (alloc_top (c_vm C)) Ak mk sel sv -> v_name sv = 0%Z -> (v_sy sv = 1 \/ v_sy sv = 4 \/ v_sy sv = 5 \/ v_sy sv = 8)%Z ->
  (forall q, O23LeptCloseA.sblk sel sv q -> live (c_A0 C) q = None) -> (forall q, O23LeptCloseA.sblk sel sv q -> live Ar q = None) ->
  sub_live Ar Ak -> aroom Ak vk kx bx ->
  (forall A' m' vm' r', W C A' m' (with_vmmaps vm' md) -> cs_kept r r' ->
     (forall q, O23LeptCloseA.sblk sel sv q -> live A' q = None) -> (forall q, ~ O23LeptCloseA.sblk sel sv q -> live A' q = live Ak q) ->
     O23LeptCloseA.PWK Ak (fun q => ~ O23LeptCloseA.sblk sel sv q) mk m' ->
     (forall a : word, (s - 112 <= u a)%Z -> ~ (psel <= u a < psel + 8)%Z -> m' a = mk a) ->
     rdn SEGS m' (Z_to_bv 64 psel) 8 = Some (Z_to_le_bytes 8 0) ->
     sub_live Ar A' -> POSTM C Ar s mk m' -> aroom A' vm' kx bx ->
     realizes SEGS (mkCfg (mkst r' retpc m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst r (0xa4c74 : word) mk al_rom) (with_vmmaps vk md)) S.
Proof.
  intros fx C Ar Ak mk vk md r s psel sel sv retpc S kx bx CK HW Hs16 Hlo Hhi R2 Hp1 Hp2 Hp8 R1 Hret R4 R10 Rsel SA Hn Hsy
    L0 LAr SUB ROOM HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. unfold CSC_STACK in Hlo.
  apply (@selDestroy_W fx AL CL ASR PINS P16 C Ak mk (with_vmmaps vk md) r (s - 112)%Z psel sel sv retpc S CK HW R2
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold O23LeptCloseIface.SELD_STACK, ALLOC_STACK; lia)
           Hp1 ltac:(lia) Hp8 R1 Hret R4 R10 Rsel SA Hn Hsy).
  - intros p0 Hp0. apply L0. exists p0. split; [exact Hp0 | reflexivity].
  - intros A' m' vm' r' HW' CS' LD LE PM' R0 BELOW RT. rewrite with_vmmaps_twice in HW'. rewrite with_vmmaps_twice.
    rewrite with_vmmaps_vmmaps in RT.
    assert (LE' : forall q, ~ O23LeptCloseA.sblk sel sv q -> live A' q = live Ak q).
    { intros q Hq. apply LE. intros p0 Hp0 E. apply Hq. exists p0. split; [exact Hp0 | exact E]. }
    assert (LD' : forall q, O23LeptCloseA.sblk sel sv q -> live A' q = None).
    { intros q (p0 & Hp0 & ->). exact (LD p0 Hp0). }
    destruct PM' as [FR LV].
    assert (SUB' : sub_live Ar A').
    { apply (O23LeptCloseA.sub_live_free_X Ar Ak A' (O23LeptCloseA.sblk sel sv) SUB LE' LAr).
      intros q. apply O23LeptCloseA.sblk_dec. destruct SA as (Hsy1 & _). lia. }
    apply (HK A' m' vm' r' HW' CS' LD' LE').
    + exact (O23LeptCloseA.PWK_free Ak A' (O23LeptCloseA.sblk sel sv) mk m' LV LE').
    + intros a Ha Hn8. destruct (Z_lt_dec (u a) psel) as [Hlt | Hge].
      * apply BELOW. lia.
      * apply (FRM_pw C (psel + 8)%Z mk m' CK FR ltac:(lia)). lia.
    + exact R0.
    + exact SUB'.
    + split; [apply (FRM_mono C (psel + 8)%Z s mk m' FR); lia | exact (LIVK_sub Ar A' mk m' SUB' LV)].
    + pose proof (aroom_nonneg Ak vk kx bx ROOM) as [Nk Nb].
      pose proof (RT kx bx ROOM ltac:(lia) ltac:(lia)) as RR. rewrite !Z.sub_0_r in RR. exact RR.
Qed.

(* [comment removed for export] *)
Lemma seld_null : forall (fx : FPState) C Ak mk md r (s psel : Z) (retpc : word) (S : TSet),
  Cok C -> W C Ak mk md -> (s mod 16 = 0)%Z -> (c_top C - LSTK + CSC_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr r 2 = Z_to_bv 64 (s - 112) -> (s - 112 <= psel)%Z -> (psel + 8 <= s)%Z -> (psel mod 8 = 0)%Z ->
  getr r 1 = retpc -> ret_ok retpc -> getr r 10 = Z_to_bv 64 psel ->
  rdn SEGS mk (Z_to_bv 64 psel) 8 = Some (Z_to_le_bytes 8 0) ->
  (forall m' r', W C Ak m' md -> cs_kept r r' -> POSTM C Ak s mk m' -> O23LeptCloseA.PWK Ak (fun _ => True) mk m' ->
     (forall a : word, (s - 112 <= u a)%Z -> m' a = mk a) ->
     realizes SEGS (mkCfg (mkst r' retpc m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst r (0xa4c74 : word) mk al_rom) md) S.
Proof.
  intros fx C Ak mk md r s psel retpc S CK HW Hs16 Hlo Hhi R2 Hp1 Hp2 Hp8 R1 Hret R10 Rz HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. unfold CSC_STACK in Hlo.
  apply (@selDestroy_null_W fx AL CL ASR PINS P16 C Ak mk md r (s - 112)%Z psel retpc S CK HW R2
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold O23LeptCloseIface.SELD_STACK, ALLOC_STACK; lia)
           Hp1 ltac:(lia) Hp8 R1 Hret R10 Rz).
  intros m' r' HW' CS' PM'. destruct PM' as [FR LV].
  apply (HK m' r' HW' CS').
  - split; [apply (FRM_mono C (s - 112)%Z s mk m' FR); lia | exact LV].
  - exact (O23LeptCloseA.PWK_livk Ak mk m' LV).
  - intros a Ha. apply (FRM_pw C (s - 112)%Z mk m' CK FR ltac:(lia)). lia.
Qed.

Lemma m8_sub : forall s k : Z, (s mod 16 = 0)%Z -> (k mod 8 = 0)%Z -> ((s - k) mod 8 = 0)%Z.
Proof.
  intros s k Hs Hk. apply Z.mod_divide; [lia|]. apply Z.divide_sub_r.
  - apply (Z.divide_trans _ 16%Z); [exists 2%Z; reflexivity | apply Z.mod_divide; [lia | exact Hs]].
  - apply Z.mod_divide; [lia | exact Hk].
Qed.

Lemma rk_cs : forall x : reg, In x [3; 4; 21; 22; 23; 24; 25; 26; 27]%list -> AllocIface.callee_saved x.
Proof.
  intros x Hx. cbn [In] in Hx.
  repeat (destruct Hx as [<-|Hx];
    [first [exact cs3 | exact cs4 | exact cs21 | exact cs22 | exact cs23 | exact cs24 | exact cs25 | exact cs26 | exact cs27] |]).
  destruct Hx.
Qed.

Lemma rk_nin : forall x : reg, In x [3; 4; 21; 22; 23; 24; 25; 26; 27]%list -> ~ In x [1; 10]%list.
Proof.
  intros x Hx. cbn [In] in Hx.
  repeat (destruct Hx as [<-|Hx]; [notin_lit |]).
  destruct Hx.
Qed.

Definition CST (C : lctx) (Ar A : AS) (m : word -> option byte) (regs : bvmap 5 word) (s : Z) (ret : word) (pix1 w h cm datas : Z)
    (cv : cmapv) (cm' : Z) (cv' : cmapv) (T : word -> Prop) (A9 : AS) (m9 : word -> option byte) (r9 : bvmap 5 word) : Prop :=
  getr r9 2 = Z_to_bv 64 (s - 112) /\ getr r9 8 = Z_to_bv 64 pix1 /\ O23LeptCloseT.rkept regs r9 /\ FRS m9 s ret regs /\
  sub_live Ar A9 /\ POSTM C Ar s m m9 /\ O23LeptCloseSpec.pix1_at C Ar A9 m9 pix1 w h cm' datas cv' /\
  O23LeptCloseA.cslm T A A9 cm cv cm' cv' /\ (forall q, T q -> ~ O23LeptCloseA.tblk pix1 datas cm' cv' q).

Lemma hop_real : forall (fx : FPState) C Ar A m md regs (s : Z) (ret : word) (pix1 w h cm datas : Z) (cv : cmapv) (cm' : Z) (cv' : cmapv)
    (T T' : word -> Prop) Ak mk vk r (pc : word) (retpc psel sel : Z) (sv : selv) (S : TSet) (kx bx : Z),
  Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + CSC_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 4 = Z_to_bv 64 0x1381d0 -> sub_live Ar A ->
  W C Ak mk (with_vmmaps vk md) -> aroom Ak vk kx bx ->
  CST C Ar A m regs s ret pix1 w h cm datas cv cm' cv' T Ak mk r ->
  (exists r1, msteps SEGS (@mkst fx r pc mk al_rom) (@mkst fx r1 (0xa4c74 : word) mk al_rom) /\
     getr r1 1 = Z_to_bv 64 retpc /\ getr r1 10 = Z_to_bv 64 psel /\ regs_agree (fun x => In x [1; 10]%list) r r1) ->
  ret_ok (Z_to_bv 64 retpc) ->
  (s - 104 <= psel)%Z -> (psel + 8 <= s - 72)%Z -> (psel mod 8 = 0)%Z ->
  rdn SEGS mk (Z_to_bv 64 psel) 8 = Some (Z_to_le_bytes 8 sel) ->
  sel_at (alloc_top (c_vm C)) Ak mk sel sv -> v_name sv = 0%Z -> (v_sy sv = 1 \/ v_sy sv = 4 \/ v_sy sv = 5 \/ v_sy sv = 8)%Z ->
  (forall q, O23LeptCloseA.sblk sel sv q -> live A q = None /\ live (c_A0 C) q = None) ->
  (forall q, O23LeptCloseA.sblk sel sv q -> T q) -> (forall q, T q -> ~ O23LeptCloseA.sblk sel sv q -> T' q) -> (forall q, T' q -> T q) ->
  (forall A' m' vm' r', W C A' m' (with_vmmaps vm' md) -> aroom A' vm' kx bx ->
     CST C Ar A m regs s ret pix1 w h cm datas cv cm' cv' T' A' m' r' ->
     (forall b z : Z, (b + 8 <= psel \/ psel + 8 <= b)%Z -> (s - 112 <= b)%Z -> (b + 8 <= s)%Z ->
        rdn SEGS mk (Z_to_bv 64 b) 8 = Some (Z_to_le_bytes 8 z) -> rdn SEGS m' (Z_to_bv 64 b) 8 = Some (Z_to_le_bytes 8 z)) ->
     (forall sel' sv', sel_at (alloc_top (c_vm C)) Ak mk sel' sv' -> (forall q, O23LeptCloseA.sblk sel' sv' q -> ~ O23LeptCloseA.sblk sel sv q) ->
        sel_at (alloc_top (c_vm C)) A' m' sel' sv') ->
     realizes SEGS (mkCfg (@mkst fx r' (Z_to_bv 64 retpc) m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst fx r pc mk al_rom) (with_vmmaps vk md)) S.
Proof.
  intros fx C Ar A m md regs s ret pix1 w h cm datas cv cm' cv' T T' Ak mk vk r pc retpc psel sel sv S kx bx
    CK Hs16 Hlo Hhi H4 SUBA HW ROOM (R2 & R8 & RK & FS & SUB & PM & P1 & CSL & DJ) (r1 & RUN & RA & RA0 & AG) RO
    Hp1 Hp2 Hp8 Rsel SA Hn Hsy LS ST TT' T'T HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. pose proof Hlo as Hlo'. unfold CSC_STACK in Hlo'.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  assert (G : forall x : reg, ~ In x [1; 10]%list -> getr r1 x = getr r x) by (intros x Hx; exact (AG x Hx)).
  assert (LAr : forall q, O23LeptCloseA.sblk sel sv q -> live Ar q = None).
  { intros q Hq. destruct (live Ar q) as [k|] eqn:E; [|reflexivity]. apply SUBA in E. rewrite (proj1 (LS q Hq)) in E. discriminate E. }
  assert (DEC : forall q, O23LeptCloseA.sblk sel sv q \/ ~ O23LeptCloseA.sblk sel sv q) by (intros q; apply O23LeptCloseA.sblk_dec; lia).
  rzs HW RUN.
  apply (seld_real fx C Ar Ak mk vk md r1 s psel sel sv (Z_to_bv 64 retpc) S kx bx CK HW Hs16 Hlo Hhi
           ltac:(rewrite G by notin_lit; exact R2) ltac:(lia) ltac:(lia) Hp8 RA RO
           ltac:(rewrite G by notin_lit; rewrite (RK 4%bv ltac:(in_lit)); exact H4) RA0 Rsel SA Hn Hsy
           (fun q Hq => proj2 (LS q Hq)) LAr SUB ROOM).
  intros A' m' vm' r' HW' CS' LD LE PW BELOW R0 SUB' PM' ROOM'.
  apply (HK A' m' vm' r' HW' ROOM').
  - refine (conj _ (conj _ (conj _ (conj _ (conj SUB' (conj (POSTM_trans C Ar s m mk m' PM PM') (conj _ (conj _ _)))))))).
    + rewrite (cs_kept_get r1 r' 2%bv CS' cs2), G by notin_lit. exact R2.
    + rewrite (cs_kept_get r1 r' 8%bv CS' cs8), G by notin_lit. exact R8.
    + intros x Hx. rewrite (cs_kept_get r1 r' x CS' (rk_cs x Hx)), (G x (rk_nin x Hx)). exact (RK x Hx).
    + apply (FRS_keep mk m' s ret regs ltac:(lia) ltac:(lia) FS). intros a Ha. apply BELOW; lia.
    + apply (O23LeptCloseA.p1_keep3 C Ar Ak A' (fun q => ~ O23LeptCloseA.sblk sel sv q) mk m' pix1 w h cm' datas cv' P1).
      * intros q Hq. apply LE. intros Hs. exact (DJ q (ST q Hs) Hq).
      * exact PW.
      * intros Hs. apply (DJ _ (ST _ Hs)). left. reflexivity.
      * intros Hc Hs. apply (DJ _ (ST _ Hs)). right. right. split; [exact Hc | left; reflexivity].
    + apply (O23LeptCloseA.cslm_free T T' (O23LeptCloseA.sblk sel sv) A Ak A' cm cv cm' cv' CSL LD LE (fun q Hq => proj1 (LS q Hq)) DEC).
      intros q N1 N2 N3. exact (N1 (TT' q N3 N2)).
    + intros q Hq. exact (DJ q (T'T q Hq)).
  - intros b z Hd Hb1 Hb2 Rb.
    apply (cell_keep mk m' b (b + 8) b z ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); [|exact Rb].
    intros a Ha. apply BELOW; lia.
  - intros sel' sv' SA' DJs.
    exact (O23LeptCloseA.sel_at_keepP (alloc_top (c_vm C)) Ak A' (fun q => ~ O23LeptCloseA.sblk sel sv q) mk m' sel' sv' ATL SA'
             (fun q Hq => LE q (DJs q Hq)) PW DJs).
Qed.

Lemma hop_null : forall (fx : FPState) C Ar A m md regs (s : Z) (ret : word) (pix1 w h cm datas : Z) (cv : cmapv) (cm' : Z) (cv' : cmapv)
    (T : word -> Prop) Ak mk vk r (pc : word) (retpc psel : Z) (S : TSet),
  Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + CSC_STACK <= s)%Z -> (s <= c_top C)%Z ->
  W C Ak mk (with_vmmaps vk md) ->
  CST C Ar A m regs s ret pix1 w h cm datas cv cm' cv' T Ak mk r ->
  (exists r1, msteps SEGS (@mkst fx r pc mk al_rom) (@mkst fx r1 (0xa4c74 : word) mk al_rom) /\
     getr r1 1 = Z_to_bv 64 retpc /\ getr r1 10 = Z_to_bv 64 psel /\ regs_agree (fun x => In x [1; 10]%list) r r1) ->
  ret_ok (Z_to_bv 64 retpc) ->
  (s - 104 <= psel)%Z -> (psel + 8 <= s - 72)%Z -> (psel mod 8 = 0)%Z ->
  rdn SEGS mk (Z_to_bv 64 psel) 8 = Some (Z_to_le_bytes 8 0) ->
  (forall m' r', W C Ak m' (with_vmmaps vk md) ->
     CST C Ar A m regs s ret pix1 w h cm datas cv cm' cv' T Ak m' r' ->
     (forall b z : Z, (s - 112 <= b)%Z -> (b + 8 <= s)%Z ->
        rdn SEGS mk (Z_to_bv 64 b) 8 = Some (Z_to_le_bytes 8 z) -> rdn SEGS m' (Z_to_bv 64 b) 8 = Some (Z_to_le_bytes 8 z)) ->
     (forall sel' sv', sel_at (alloc_top (c_vm C)) Ak mk sel' sv' -> sel_at (alloc_top (c_vm C)) Ak m' sel' sv') ->
     realizes SEGS (mkCfg (@mkst fx r' (Z_to_bv 64 retpc) m' al_rom) (with_vmmaps vk md)) S) ->
  realizes SEGS (mkCfg (@mkst fx r pc mk al_rom) (with_vmmaps vk md)) S.
Proof.
  intros fx C Ar A m md regs s ret pix1 w h cm datas cv cm' cv' T Ak mk vk r pc retpc psel S
    CK Hs16 Hlo Hhi HW (R2 & R8 & RK & FS & SUB & PM & P1 & CSL & DJ) (r1 & RUN & RA & RA0 & AG) RO Hp1 Hp2 Hp8 Rz HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. pose proof Hlo as Hlo'. unfold CSC_STACK in Hlo'.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  assert (G : forall x : reg, ~ In x [1; 10]%list -> getr r1 x = getr r x) by (intros x Hx; exact (AG x Hx)).
  rzs HW RUN.
  apply (seld_null fx C Ak mk (with_vmmaps vk md) r1 s psel (Z_to_bv 64 retpc) S CK HW Hs16 Hlo Hhi
           ltac:(rewrite G by notin_lit; exact R2) ltac:(lia) ltac:(lia) Hp8 RA RO RA0 Rz).
  intros m' r' HW' CS' PM' PW BELOW.
  apply (HK m' r' HW').
  - refine (conj _ (conj _ (conj _ (conj _ (conj SUB (conj (POSTM_trans C Ar s m mk m' PM (POSTM_sub C Ar Ak s mk m' SUB PM')) (conj _ (conj CSL DJ)))))))).
    + rewrite (cs_kept_get r1 r' 2%bv CS' cs2), G by notin_lit. exact R2.
    + rewrite (cs_kept_get r1 r' 8%bv CS' cs8), G by notin_lit. exact R8.
    + intros x Hx. rewrite (cs_kept_get r1 r' x CS' (rk_cs x Hx)), (G x (rk_nin x Hx)). exact (RK x Hx).
    + apply (FRS_keep mk m' s ret regs ltac:(lia) ltac:(lia) FS). intros a Ha. apply BELOW; lia.
    + exact (O23LeptCloseA.p1_keep3 C Ar Ak Ak (fun _ => True) mk m' pix1 w h cm' datas cv' P1 (fun q _ => eq_refl) PW I (fun _ => I)).
  - intros b z Hb1 Hb2 Rb.
    apply (cell_keep mk m' b (b + 8) b z ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); [|exact Rb].
    intros a Ha. apply BELOW; lia.
  - intros sel' sv' SA'.
    exact (O23LeptCloseA.sel_at_keepP (alloc_top (c_vm C)) Ak Ak (fun _ => True) mk m' sel' sv' ATL SA' (fun q _ => eq_refl) PW (fun _ _ => I)).
Qed.


(* [comment removed for export] *)
Lemma csc_seld4 : forall (sh : bool) (fr : bvmap 5 word) C Ar A m md regs (s pix1 w h cm datas : Z) (cv : cmapv) (ret : word) (S : TSet) (kR bR : Z)
    (fr1 : bvmap 5 word) (cs1 : bv 32) (A0 : AS) (m0 : word -> option byte) (vm0 : VmMaps) (r0 : bvmap 5 word) (cm' : Z) (cv' : cmapv) (kx bx : Z)
    (sel1 sel2 : Z) (sv1 sv2 : selv),
  Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + CSC_STACK <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 4 = Z_to_bv 64 0x1381d0 -> sub_live Ar A ->
  frm_zero cs1 -> (forall r : reg, In (u r) fs_list -> reg_get fr1 r = reg_get fr r) ->
  W C A0 m0 (with_vmmaps vm0 md) ->
  getr r0 2 = Z_to_bv 64 (s - 112) -> getr r0 8 = Z_to_bv 64 pix1 -> O23LeptCloseT.rkept regs r0 ->
  FRS m0 s ret regs ->
  rdn SEGS m0 (Z_to_bv 64 (O23LeptCloseA.co1 sh s)) 8 = Some (Z_to_le_bytes 8 sel1) -> rdn SEGS m0 (Z_to_bv 64 (O23LeptCloseA.co2 sh s)) 8 = Some (Z_to_le_bytes 8 sel2) ->
  rdn SEGS m0 (Z_to_bv 64 (O23LeptCloseA.cz1 sh s)) 8 = Some (Z_to_le_bytes 8 0) -> rdn SEGS m0 (Z_to_bv 64 (O23LeptCloseA.cz2 sh s)) 8 = Some (Z_to_le_bytes 8 0) ->
  sub_live Ar A0 -> POSTM C Ar s m m0 ->
  O23LeptCloseSpec.pix1_at C Ar A0 m0 pix1 w h cm' datas cv' ->
  sel_at (alloc_top (c_vm C)) A0 m0 sel1 sv1 -> sel_at (alloc_top (c_vm C)) A0 m0 sel2 sv2 -> O23LeptCloseT.sels_static C A sh sel1 sel2 sv1 sv2 ->
  (forall q, O23LeptCloseA.sblk sel1 sv1 q \/ O23LeptCloseA.sblk sel2 sv2 q -> ~ O23LeptCloseA.tblk pix1 datas cm' cv' q) ->
  O23LeptCloseA.cslm (fun q => O23LeptCloseA.sblk sel1 sv1 q \/ O23LeptCloseA.sblk sel2 sv2 q) A A0 cm cv cm' cv' ->
  aroom A0 vm0 kx bx -> (kR - O23LeptCloseSpec.RK_csc (O23LeptCloseA.vsz sh) <= kx)%Z -> (bR - O23LeptCloseSpec.RB_csc (O23LeptCloseA.vsz sh) w h cm <= bx)%Z ->
  (0 <= kR - O23LeptCloseSpec.RK_csc (O23LeptCloseA.vsz sh))%Z -> (0 <= bR - O23LeptCloseSpec.RB_csc (O23LeptCloseA.vsz sh) w h cm)%Z ->
  csc_K fr C Ar A m md regs s pix1 (O23LeptCloseA.vsz sh) w h cm datas cv ret S kR bR ->
  realizes SEGS (mkCfg (@mkst (mkFP fr1 cs1) r0 (0xa4c28 : word) m0 al_rom) (with_vmmaps vm0 md)) S.
Proof.
  intros sh fr C Ar A m md regs s pix1 w h cm datas cv ret S kR bR fr1 cs1 A0 m0 vm0 r0 cm' cv' kx bx sel1 sel2 sv1 sv2
    CK Hs16 Hlo Hhi Hret H2 H4 SUBA FZ FK HW0 R2 R8 RK FS C1 C2 Z1 Z2 SUB PM P1 SA1 SA2 SS DJ CSL ROOM Hk Hb Hk0 Hb0 HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. pose proof Hlo as Hlo'. unfold CSC_STACK in Hlo'.
  destruct (O23LeptCloseT.sels_sy C A sh sel1 sel2 sv1 sv2 SS) as [Y1 Y2].
  destruct SS as (N1 & N2 & _ & LS & D12).
  pose proof (conj R2 (conj R8 (conj RK (conj FS (conj SUB (conj PM (conj P1 (conj CSL DJ)))))))) as ST0.
  change (CST C Ar A m regs s ret pix1 w h cm datas cv cm' cv'
            (fun q => O23LeptCloseA.sblk sel1 sv1 q \/ O23LeptCloseA.sblk sel2 sv2 q) A0 m0 r0) in ST0.
  assert (LS1 : forall q, O23LeptCloseA.sblk sel1 sv1 q -> live A q = None /\ live (c_A0 C) q = None)
    by (intros q Hq; exact (LS q (or_introl Hq))).
  assert (LS2 : forall q, O23LeptCloseA.sblk sel2 sv2 q -> live A q = None /\ live (c_A0 C) q = None)
    by (intros q Hq; exact (LS q (or_intror Hq))).
  assert (D21 : forall q, O23LeptCloseA.sblk sel2 sv2 q -> ~ O23LeptCloseA.sblk sel1 sv1 q)
    by (intros q Q2 Q1; exact (D12 q Q1 Q2)).
  assert (TT1 : forall q, (fun q => O23LeptCloseA.sblk sel1 sv1 q \/ O23LeptCloseA.sblk sel2 sv2 q) q ->
                  ~ O23LeptCloseA.sblk sel1 sv1 q -> O23LeptCloseA.sblk sel2 sv2 q)
    by (intros q H N; destruct H as [H|H]; [exact (False_ind _ (N H)) | exact H]).
  destruct sh; cbn [O23LeptCloseA.co1 O23LeptCloseA.co2 O23LeptCloseA.cz1 O23LeptCloseA.cz2] in C1, C2, Z1, Z2.
  - apply (hop_real (mkFP fr1 cs1) C Ar A m md regs s ret pix1 w h cm datas cv cm' cv'
             (fun q => O23LeptCloseA.sblk sel1 sv1 q \/ O23LeptCloseA.sblk sel2 sv2 q) (O23LeptCloseA.sblk sel2 sv2)
             A0 m0 vm0 r0 (0xa4c28 : word) 0xa4c38 (s - 80) sel1 sv1 S kx bx CK Hs16 Hlo Hhi H4 SUBA HW0 ROOM ST0
             (@cs_N (mkFP fr1 cs1) al_rom r0 m0 s ltac:(lia) ltac:(lia) R2) ltac:(red; apply bv_eq; reflexivity)
             ltac:(lia) ltac:(lia) (m8_sub s 80 Hs16 eq_refl) C1 SA1 N1 Y1 LS1 (fun q H => or_introl H) TT1 (fun q H => or_intror H)).
    intros A1 m1 vm1 r1 HW1 ROOM1 ST1 SL1 SK1.
    pose proof ST1 as (R2_1 & _).
    replace (Z_to_bv 64 0xa4c38) with (0xa4c38 : word) by (apply bv_eq; reflexivity).
    apply (hop_real (mkFP fr1 cs1) C Ar A m md regs s ret pix1 w h cm datas cv cm' cv'
             (O23LeptCloseA.sblk sel2 sv2) (fun _ => False)
             A1 m1 vm1 r1 (0xa4c38 : word) 0xa4c40 (s - 88) sel2 sv2 S kx bx CK Hs16 Hlo Hhi H4 SUBA HW1 ROOM1 ST1
             (@cs_O (mkFP fr1 cs1) al_rom r1 m1 s ltac:(lia) ltac:(lia) R2_1) ltac:(red; apply bv_eq; reflexivity)
             ltac:(lia) ltac:(lia) (m8_sub s 88 Hs16 eq_refl) (SL1 (s - 88)%Z sel2 ltac:(lia) ltac:(lia) ltac:(lia) C2)
             (SK1 sel2 sv2 SA2 D21) N2 Y2 LS2 (fun q H => H) (fun q H N => N H) (fun q (F : False) => False_ind _ F)).
    intros A2 m2 vm2 r2 HW2 ROOM2 ST2 SL2 SK2.
    pose proof ST2 as (R2_2 & _).
    replace (Z_to_bv 64 0xa4c40) with (0xa4c40 : word) by (apply bv_eq; reflexivity).
    apply (hop_null (mkFP fr1 cs1) C Ar A m md regs s ret pix1 w h cm datas cv cm' cv' (fun _ => False)
             A2 m2 vm2 r2 (0xa4c40 : word) 0xa4c48 (s - 96) S CK Hs16 Hlo Hhi HW2 ST2
             (@cs_P (mkFP fr1 cs1) al_rom r2 m2 s ltac:(lia) ltac:(lia) R2_2) ltac:(red; apply bv_eq; reflexivity)
             ltac:(lia) ltac:(lia) (m8_sub s 96 Hs16 eq_refl)
             (SL2 (s - 96)%Z 0%Z ltac:(lia) ltac:(lia) ltac:(lia) (SL1 (s - 96)%Z 0%Z ltac:(lia) ltac:(lia) ltac:(lia) Z1))).
    intros m3 r3 HW3 ST3 SL3 _.
    pose proof ST3 as (R2_3 & _).
    replace (Z_to_bv 64 0xa4c48) with (0xa4c48 : word) by (apply bv_eq; reflexivity).
    apply (hop_null (mkFP fr1 cs1) C Ar A m md regs s ret pix1 w h cm datas cv cm' cv' (fun _ => False)
             A2 m3 vm2 r3 (0xa4c48 : word) 0xa4c50 (s - 104) S CK Hs16 Hlo Hhi HW3 ST3
             (@cs_Q (mkFP fr1 cs1) al_rom r3 m3 s ltac:(lia) ltac:(lia) R2_3) ltac:(red; apply bv_eq; reflexivity)
             ltac:(lia) ltac:(lia) (m8_sub s 104 Hs16 eq_refl)
             (SL3 (s - 104)%Z 0%Z ltac:(lia) ltac:(lia)
                (SL2 (s - 104)%Z 0%Z ltac:(lia) ltac:(lia) ltac:(lia) (SL1 (s - 104)%Z 0%Z ltac:(lia) ltac:(lia) ltac:(lia) Z2)))).
    intros m4 r4 HW4 (R2_4 & R8_4 & RK_4 & FS_4 & SUB_4 & PM_4 & P1_4 & CSL_4 & _) _ _.
    replace (Z_to_bv 64 0xa4c50) with (0xa4c50 : word) by (apply bv_eq; reflexivity).
    exact (csc_exit fr C Ar A m md regs s pix1 _ w h cm datas cv ret S kR bR fr1 cs1 A2 m4 vm2 r4 cm' cv' kx bx
             CK Hs16 Hlo Hhi Hret H2 FZ FK HW4 R2_4 R8_4 RK_4 FS_4 SUB_4 PM_4 P1_4 CSL_4 ROOM2 Hk Hb Hk0 Hb0 HK).
  - apply (hop_null (mkFP fr1 cs1) C Ar A m md regs s ret pix1 w h cm datas cv cm' cv'
             (fun q => O23LeptCloseA.sblk sel1 sv1 q \/ O23LeptCloseA.sblk sel2 sv2 q)
             A0 m0 vm0 r0 (0xa4c28 : word) 0xa4c38 (s - 80) S CK Hs16 Hlo Hhi HW0 ST0
             (@cs_N (mkFP fr1 cs1) al_rom r0 m0 s ltac:(lia) ltac:(lia) R2) ltac:(red; apply bv_eq; reflexivity)
             ltac:(lia) ltac:(lia) (m8_sub s 80 Hs16 eq_refl) Z1).
    intros m1 r1 HW1 ST1 SL1 SK1.
    pose proof ST1 as (R2_1 & _).
    replace (Z_to_bv 64 0xa4c38) with (0xa4c38 : word) by (apply bv_eq; reflexivity).
    apply (hop_null (mkFP fr1 cs1) C Ar A m md regs s ret pix1 w h cm datas cv cm' cv'
             (fun q => O23LeptCloseA.sblk sel1 sv1 q \/ O23LeptCloseA.sblk sel2 sv2 q)
             A0 m1 vm0 r1 (0xa4c38 : word) 0xa4c40 (s - 88) S CK Hs16 Hlo Hhi HW1 ST1
             (@cs_O (mkFP fr1 cs1) al_rom r1 m1 s ltac:(lia) ltac:(lia) R2_1) ltac:(red; apply bv_eq; reflexivity)
             ltac:(lia) ltac:(lia) (m8_sub s 88 Hs16 eq_refl) (SL1 (s - 88)%Z 0%Z ltac:(lia) ltac:(lia) Z2)).
    intros m2 r2 HW2 ST2 SL2 SK2.
    pose proof ST2 as (R2_2 & _).
    replace (Z_to_bv 64 0xa4c40) with (0xa4c40 : word) by (apply bv_eq; reflexivity).
    apply (hop_real (mkFP fr1 cs1) C Ar A m md regs s ret pix1 w h cm datas cv cm' cv'
             (fun q => O23LeptCloseA.sblk sel1 sv1 q \/ O23LeptCloseA.sblk sel2 sv2 q) (O23LeptCloseA.sblk sel2 sv2)
             A0 m2 vm0 r2 (0xa4c40 : word) 0xa4c48 (s - 96) sel1 sv1 S kx bx CK Hs16 Hlo Hhi H4 SUBA HW2 ROOM ST2
             (@cs_P (mkFP fr1 cs1) al_rom r2 m2 s ltac:(lia) ltac:(lia) R2_2) ltac:(red; apply bv_eq; reflexivity)
             ltac:(lia) ltac:(lia) (m8_sub s 96 Hs16 eq_refl)
             (SL2 (s - 96)%Z sel1 ltac:(lia) ltac:(lia) (SL1 (s - 96)%Z sel1 ltac:(lia) ltac:(lia) C1))
             (SK2 sel1 sv1 (SK1 sel1 sv1 SA1)) N1 Y1 LS1 (fun q H => or_introl H) TT1 (fun q H => or_intror H)).
    intros A3 m3 vm3 r3 HW3 ROOM3 ST3 SL3 SK3.
    pose proof ST3 as (R2_3 & _).
    replace (Z_to_bv 64 0xa4c48) with (0xa4c48 : word) by (apply bv_eq; reflexivity).
    apply (hop_real (mkFP fr1 cs1) C Ar A m md regs s ret pix1 w h cm datas cv cm' cv'
             (O23LeptCloseA.sblk sel2 sv2) (fun _ => False)
             A3 m3 vm3 r3 (0xa4c48 : word) 0xa4c50 (s - 104) sel2 sv2 S kx bx CK Hs16 Hlo Hhi H4 SUBA HW3 ROOM3 ST3
             (@cs_Q (mkFP fr1 cs1) al_rom r3 m3 s ltac:(lia) ltac:(lia) R2_3) ltac:(red; apply bv_eq; reflexivity)
             ltac:(lia) ltac:(lia) (m8_sub s 104 Hs16 eq_refl)
             (SL3 (s - 104)%Z sel2 ltac:(lia) ltac:(lia) ltac:(lia)
                (SL2 (s - 104)%Z sel2 ltac:(lia) ltac:(lia) (SL1 (s - 104)%Z sel2 ltac:(lia) ltac:(lia) C2)))
             (SK3 sel2 sv2 (SK2 sel2 sv2 (SK1 sel2 sv2 SA2)) D21) N2 Y2 LS2
             (fun q H => H) (fun q H N => N H) (fun q (F : False) => False_ind _ F)).
    intros A4 m4 vm4 r4 HW4 ROOM4 (R2_4 & R8_4 & RK_4 & FS_4 & SUB_4 & PM_4 & P1_4 & CSL_4 & _) _ _.
    replace (Z_to_bv 64 0xa4c50) with (0xa4c50 : word) by (apply bv_eq; reflexivity).
    exact (csc_exit fr C Ar A m md regs s pix1 _ w h cm datas cv ret S kR bR fr1 cs1 A4 m4 vm4 r4 cm' cv' kx bx
             CK Hs16 Hlo Hhi Hret H2 FZ FK HW4 R2_4 R8_4 RK_4 FS_4 SUB_4 PM_4 P1_4 CSL_4 ROOM4 Hk Hb Hk0 Hb0 HK).
Qed.

End CloseT.
