(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare
 BnModel BnMath BnMem BnDefs LibIface BnP_add BnP_ads2 BnCbdLib.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIfaceA LibIfaceB AsRtLib AsZX AsZXTac AsZXDefs BnA_lib BnA_frame
 BnB_lib BnB_mul7 BnB_add2 BnB_ads1.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Ltac flia0 := first [ lia | match goal with H : hide _ |- _ => unfold hide in H; lia end | (unfold hide in *; lia) ].
#[local] Ltac BnB_ads1.flia ::= lf_once flia0.
Ltac inr0 H tac := cbn [In] in H; repeat (destruct H as [<-|H]; [tac|]); destruct H.
#[local] Ltac BnB_ads1.inr H tac ::= lf_once ltac:(inr0 H tac).
Import ListNotations. Import ZXA BM. Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section S.
Context {fx : FPState}.
Variable rom : word -> option byte.
Variables (o buf len sp sp1 FS p2 g og bg0 bgl : Z) (ds : list Z).
Hypothesis GG : adsG o buf len sp sp1 FS p2 g og bg0 bgl.
Hypothesis Hds : length ds = Z.to_nat len.
Hypothesis DOK : digits_ok ds.

#[local] Abbreviation F := (FS + 5279744 + p2 * 2048).
#[local] Abbreviation G := g.
#[local] Abbreviation AMBs := (AMB o buf bg0 bgl ds).
#[local] Abbreviation NSs := (NS o FS p2 g).
#[local] Abbreviation SL1s := (SL1 o sp1 g og).
#[local] Abbreviation SL2s := (SL2 o buf sp1 FS p2).
#[local] Abbreviation WINs := (WIN o sp FS p2 g).
#[local] Abbreviation AMBu := (AMB_unch o buf len sp sp1 FS p2 g og bg0 bgl ds GG Hds).
#[local] Abbreviation SL1u := (SL1_unch o buf len sp sp1 FS p2 g og bg0 bgl GG).
#[local] Abbreviation SL2u := (SL2_unch o buf len sp sp1 FS p2 g og bg0 bgl GG).
#[local] Abbreviation WINg := (WIN_grows o sp FS p2 g).
(* [comment removed for export] *)
Definition NS2 : list (Z * Z) := (sp1 - 128, sp1) :: (sp1 + 248, sp1 + 256) :: NSs.
Ltac rngs2 := let rg := fresh "rg" in let H := fresh "Hrg" in
  intros rg H; unfold NS2, NS, ambr, sl1r, sl2r, savr, highr in *; inr H ltac:(slia).


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Abbreviation dI := (Some (48, 57)).
Abbreviation rdB_uvi := [Some (KHI + 256, HIE - 384); Some (IMG, HIE - 19); Some (0, 761); Some (IMG, HIE - 516);
                        dI; dI; dI; dI; dI; dI; dI; dI; dI; dI; dI; dI; dI; dI; dI; dI; dI; dI; dI; Some (0, 780)].
Abbreviation rdB_pins := [(9%bv : reg, ZV 32); (24%bv : reg, ZV 33); (22%bv : reg, ZV 34); (20%bv : reg, ZL SHA);
                         (26%bv : reg, ZL 10); (21%bv : reg, ZV 55); (25%bv : reg, ZV 35)].
Abbreviation rdB_kn :=
  [KC (ZV 32) 224 8 (ZSub (ZL 18446744073709551615) (ZV 33));
   KC (ZV 32) 216 8 (ZAdd (ZV 33) (ZL 1));
   KC (ZV 32) 208 8 (ZAdd (ZV 33) (ZL 2));
   KC (ZV 32) 200 8 (ZAdd (ZV 33) (ZL 3));
   KC (ZV 32) 192 8 (ZAdd (ZV 33) (ZL 4));
   KC (ZV 32) 184 8 (ZAdd (ZV 33) (ZL 5));
   KC (ZV 32) 176 8 (ZAdd (ZV 33) (ZL 6));
   KC (ZV 32) 168 8 (ZAdd (ZV 33) (ZL 7));
   KC (ZV 32) 160 8 (ZAdd (ZV 33) (ZL 8));
   KC (ZV 32) 152 8 (ZAdd (ZV 33) (ZL 9));
   KC (ZV 32) 144 8 (ZAdd (ZV 33) (ZL 10));
   KC (ZV 32) 136 8 (ZAdd (ZV 33) (ZL 11));
   KC (ZV 32) 128 8 (ZAdd (ZV 33) (ZL 12));
   KC (ZV 32) 120 8 (ZAdd (ZV 33) (ZL 13));
   KC (ZV 32) 112 8 (ZAdd (ZV 33) (ZL 14));
   KC (ZV 32) 104 8 (ZAdd (ZV 33) (ZL 15));
   KC (ZV 32) 96 8 (ZAdd (ZV 33) (ZL 16));
   KC (ZV 32) 88 8 (ZAdd (ZV 33) (ZL 17));
   KC (ZV 32) 80 8 (ZAdd (ZV 33) (ZL 18));
   KC (ZV 32) 72 8 (ZV 35);
   KC (ZAdd (ZV 33) (ZV 34)) 0 1 (ZV 36);
   KC (ZDivP (ZAdd (ZV 33) (ZV 34)) 3) SHA 1 (ZL 0);
   KC (ZAdd (ZV 34) (ZAdd (ZV 33) (ZL 1))) 0 1 (ZV 37);
   KC (ZDivP (ZAdd (ZV 34) (ZAdd (ZV 33) (ZL 1))) 3) SHA 1 (ZL 0);
   KC (ZAdd (ZV 34) (ZAdd (ZV 33) (ZL 2))) 0 1 (ZV 38);
   KC (ZDivP (ZAdd (ZV 34) (ZAdd (ZV 33) (ZL 2))) 3) SHA 1 (ZL 0);
   KC (ZAdd (ZV 34) (ZAdd (ZV 33) (ZL 3))) 0 1 (ZV 39);
   KC (ZDivP (ZAdd (ZV 34) (ZAdd (ZV 33) (ZL 3))) 3) SHA 1 (ZL 0);
   KC (ZAdd (ZV 34) (ZAdd (ZV 33) (ZL 4))) 0 1 (ZV 40);
   KC (ZDivP (ZAdd (ZV 34) (ZAdd (ZV 33) (ZL 4))) 3) SHA 1 (ZL 0);
   KC (ZAdd (ZV 34) (ZAdd (ZV 33) (ZL 5))) 0 1 (ZV 41);
   KC (ZDivP (ZAdd (ZV 34) (ZAdd (ZV 33) (ZL 5))) 3) SHA 1 (ZL 0);
   KC (ZAdd (ZV 34) (ZAdd (ZV 33) (ZL 6))) 0 1 (ZV 42);
   KC (ZDivP (ZAdd (ZV 34) (ZAdd (ZV 33) (ZL 6))) 3) SHA 1 (ZL 0);
   KC (ZAdd (ZV 34) (ZAdd (ZV 33) (ZL 7))) 0 1 (ZV 43);
   KC (ZDivP (ZAdd (ZV 34) (ZAdd (ZV 33) (ZL 7))) 3) SHA 1 (ZL 0);
   KC (ZAdd (ZV 34) (ZAdd (ZV 33) (ZL 8))) 0 1 (ZV 44);
   KC (ZDivP (ZAdd (ZV 34) (ZAdd (ZV 33) (ZL 8))) 3) SHA 1 (ZL 0);
   KC (ZAdd (ZV 34) (ZAdd (ZV 33) (ZL 9))) 0 1 (ZV 45);
   KC (ZDivP (ZAdd (ZV 34) (ZAdd (ZV 33) (ZL 9))) 3) SHA 1 (ZL 0);
   KC (ZAdd (ZV 34) (ZAdd (ZV 33) (ZL 10))) 0 1 (ZV 46);
   KC (ZDivP (ZAdd (ZV 34) (ZAdd (ZV 33) (ZL 10))) 3) SHA 1 (ZL 0);
   KC (ZAdd (ZV 34) (ZAdd (ZV 33) (ZL 11))) 0 1 (ZV 47);
   KC (ZDivP (ZAdd (ZV 34) (ZAdd (ZV 33) (ZL 11))) 3) SHA 1 (ZL 0);
   KC (ZAdd (ZV 34) (ZAdd (ZV 33) (ZL 12))) 0 1 (ZV 48);
   KC (ZDivP (ZAdd (ZV 34) (ZAdd (ZV 33) (ZL 12))) 3) SHA 1 (ZL 0);
   KC (ZAdd (ZV 34) (ZAdd (ZV 33) (ZL 13))) 0 1 (ZV 49);
   KC (ZDivP (ZAdd (ZV 34) (ZAdd (ZV 33) (ZL 13))) 3) SHA 1 (ZL 0);
   KC (ZAdd (ZV 34) (ZAdd (ZV 33) (ZL 14))) 0 1 (ZV 50);
   KC (ZDivP (ZAdd (ZV 34) (ZAdd (ZV 33) (ZL 14))) 3) SHA 1 (ZL 0);
   KC (ZAdd (ZV 34) (ZAdd (ZV 33) (ZL 15))) 0 1 (ZV 51);
   KC (ZDivP (ZAdd (ZV 34) (ZAdd (ZV 33) (ZL 15))) 3) SHA 1 (ZL 0);
   KC (ZAdd (ZV 34) (ZAdd (ZV 33) (ZL 16))) 0 1 (ZV 52);
   KC (ZDivP (ZAdd (ZV 34) (ZAdd (ZV 33) (ZL 16))) 3) SHA 1 (ZL 0);
   KC (ZAdd (ZV 34) (ZAdd (ZV 33) (ZL 17))) 0 1 (ZV 53);
   KC (ZDivP (ZAdd (ZV 34) (ZAdd (ZV 33) (ZL 17))) 3) SHA 1 (ZL 0);
   KC (ZAdd (ZV 34) (ZAdd (ZV 33) (ZL 18))) 0 1 (ZV 54);
   KC (ZDivP (ZAdd (ZV 34) (ZAdd (ZV 33) (ZL 18))) 3) SHA 1 (ZL 0)].
Definition RD_KEEP : list Z := [2; 3; 4; 8; 9; 19; 20; 22; 24; 25; 26].

#[using="og GG Hds"] Lemma rd19_B : forall regs m (pos rem : Z) (ch : list Z),
  getr regs 9%bv = Z_to_bv 64 sp1 -> getr regs 24%bv = Z_to_bv 64 buf -> getr regs 22%bv = Z_to_bv 64 pos ->
  getr regs 20%bv = Z_to_bv 64 SHA -> getr regs 26%bv = Z_to_bv 64 10 -> getr regs 25%bv = Z_to_bv 64 o ->
  getr regs 21%bv = Z_to_bv 64 rem ->
  SL2s m -> AMBs m -> WINs m ->
  length ch = 19%nat -> digits_ok ch -> (forall k, (k < 19)%nat -> cellN SEGS_B m (buf + pos + Z.of_nat k) 1 (nth k ch 0)) ->
  0 <= pos -> pos + 19 <= len -> 0 <= rem <= 780 ->
  exists regs',
    msteps SEGS_B (mkst regs (Z_to_bv 64 0x0a9f2c) m rom)
                  (mkst regs' (Z_to_bv 64 0x0aa708) (wbytes m (Z_to_bv 64 (sp1 + 248)) (word_to_le_bytes 8 (Z_to_bv 64 rem))) rom)
    /\ getr regs' 23%bv = Z_to_bv 64 (decval ch) /\ getr regs' 1%bv = Z_to_bv 64 0x0aa2c4
    /\ getr regs' 10%bv = Z_to_bv 64 o /\ getr regs' 11%bv = Z_to_bv 64 19
    /\ keeps RD_KEEP regs regs'.
Proof.
  intros regs m pos rem ch R9 R24 R22 R20 R26 R25 R21 L2 AM W Hlen Hdok Hcells Hp1 Hp2 Hrem.
  destruct AM as (SC & MC & TBL & TSH & OSH & DG & DSH & K27C). destruct L2 as (L16 & L8 & L232 & L56 & L72 & L224 & LT).
  destruct W as (Wsp & Wo & WF & WG). geom GG.
  destruct ch as [|d0 [|d1 [|d2 [|d3 [|d4 [|d5 [|d6 [|d7 [|d8 [|d9 [|d10 [|d11 [|d12 [|d13 [|d14 [|d15 [|d16 [|d17 [|d18 [|? ?]]]]]]]]]]]]]]]]]]]];
    try (cbn in Hlen; discriminate).
  unfold digits_ok in Hdok.
  repeat match type of Hdok with Forall _ (_ :: _) => apply Forall_cons_iff in Hdok; destruct Hdok as [? Hdok] end.
  pose proof (Hcells 0%nat ltac:(lia)) as D0.
  pose proof (Hcells 1%nat ltac:(lia)) as D1.
  pose proof (Hcells 2%nat ltac:(lia)) as D2.
  pose proof (Hcells 3%nat ltac:(lia)) as D3.
  pose proof (Hcells 4%nat ltac:(lia)) as D4.
  pose proof (Hcells 5%nat ltac:(lia)) as D5.
  pose proof (Hcells 6%nat ltac:(lia)) as D6.
  pose proof (Hcells 7%nat ltac:(lia)) as D7.
  pose proof (Hcells 8%nat ltac:(lia)) as D8.
  pose proof (Hcells 9%nat ltac:(lia)) as D9.
  pose proof (Hcells 10%nat ltac:(lia)) as D10.
  pose proof (Hcells 11%nat ltac:(lia)) as D11.
  pose proof (Hcells 12%nat ltac:(lia)) as D12.
  pose proof (Hcells 13%nat ltac:(lia)) as D13.
  pose proof (Hcells 14%nat ltac:(lia)) as D14.
  pose proof (Hcells 15%nat ltac:(lia)) as D15.
  pose proof (Hcells 16%nat ltac:(lia)) as D16.
  pose proof (Hcells 17%nat ltac:(lia)) as D17.
  pose proof (Hcells 18%nat ltac:(lia)) as D18.
  clear Hcells. cbn [nth] in *. rewrite ?Z.add_0_r in D0.
  zx_run SEGS_B constr:(CTX (vi_regs ++ rdB_uvi) rdB_kn [KW (ZV 32) 248 256]) 260%nat [0x0aa708] (SCR [false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false] []) constr:(rdB_pins)
    [sp1; buf; pos; o; d0; d1; d2; d3; d4; d5; d6; d7; d8; d9; d10; d11; d12; d13; d14; d15; d16; d17; d18; rem] constr:(rdB_uvi) regs m rom 0x0a9f2c.
  zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia)
    ltac:(kc1 L224; kc1 (LT 1 ltac:(lia)); kc1 (LT 2 ltac:(lia)); kc1 (LT 3 ltac:(lia)); kc1 (LT 4 ltac:(lia)); kc1 (LT 5 ltac:(lia)); kc1 (LT 6 ltac:(lia)); kc1 (LT 7 ltac:(lia)); kc1 (LT 8 ltac:(lia)); kc1 (LT 9 ltac:(lia)); kc1 (LT 10 ltac:(lia)); kc1 (LT 11 ltac:(lia)); kc1 (LT 12 ltac:(lia)); kc1 (LT 13 ltac:(lia)); kc1 (LT 14 ltac:(lia)); kc1 (LT 15 ltac:(lia)); kc1 (LT 16 ltac:(lia)); kc1 (LT 17 ltac:(lia)); kc1 (LT 18 ltac:(lia)); kc1 L72; kc1 D0; kc1 (DSH ((buf + pos + 0) / 8) ltac:(lia)); kc1 D1; kc1 (DSH ((buf + pos + 1) / 8) ltac:(lia)); kc1 D2; kc1 (DSH ((buf + pos + 2) / 8) ltac:(lia)); kc1 D3; kc1 (DSH ((buf + pos + 3) / 8) ltac:(lia)); kc1 D4; kc1 (DSH ((buf + pos + 4) / 8) ltac:(lia)); kc1 D5; kc1 (DSH ((buf + pos + 5) / 8) ltac:(lia)); kc1 D6; kc1 (DSH ((buf + pos + 6) / 8) ltac:(lia)); kc1 D7; kc1 (DSH ((buf + pos + 7) / 8) ltac:(lia)); kc1 D8; kc1 (DSH ((buf + pos + 8) / 8) ltac:(lia)); kc1 D9; kc1 (DSH ((buf + pos + 9) / 8) ltac:(lia)); kc1 D10; kc1 (DSH ((buf + pos + 10) / 8) ltac:(lia)); kc1 D11; kc1 (DSH ((buf + pos + 11) / 8) ltac:(lia)); kc1 D12; kc1 (DSH ((buf + pos + 12) / 8) ltac:(lia)); kc1 D13; kc1 (DSH ((buf + pos + 13) / 8) ltac:(lia)); kc1 D14; kc1 (DSH ((buf + pos + 14) / 8) ltac:(lia)); kc1 D15; kc1 (DSH ((buf + pos + 15) / 8) ltac:(lia)); kc1 D16; kc1 (DSH ((buf + pos + 16) / 8) ltac:(lia)); kc1 D17; kc1 (DSH ((buf + pos + 17) / 8) ltac:(lia)); kc1 D18; kc1 (DSH ((buf + pos + 18) / 8) ltac:(lia)); exact I)
    ltac:(kwd Wsp; exact I) ltac:(idtac; zx_scs ltac:(flia)).
  zx_name regs1.
  exists regs1. split; [exact ZM|].
  split; [zx_regv ZR; unfold decval; cbn [read_digits]; f_equal; lia|].
  split; [zx_regv ZR|]. split; [zx_regv ZR|]. split; [zx_regv ZR|].
  eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition K19B : list Z := [2; 3; 4; 8; 9; 19; 20; 24; 25; 26].

#[using="len GG Hds DOK"] Lemma iter19_B : forall regs m (done rest : list Z) (b : bn),
  let pos := zlen done in let rem := zlen rest in
  ds = done ++ rest ->
  getr regs 9%bv = Z_to_bv 64 sp1 -> getr regs 2%bv = Z_to_bv 64 sp1 -> getr regs 24%bv = Z_to_bv 64 buf ->
  getr regs 22%bv = Z_to_bv 64 pos -> getr regs 21%bv = Z_to_bv 64 rem -> getr regs 20%bv = Z_to_bv 64 SHA ->
  getr regs 26%bv = Z_to_bv 64 10 -> getr regs 25%bv = Z_to_bv 64 o -> getr regs 19%bv = Z_to_bv 64 MASK ->
  AMBs m -> SL1s m -> SL2s m -> WINs m ->
  19 <= rem ->
  bn_at SEGS_B m o b -> ok (cells b) -> norm (cells b) -> ex b = 0 -> 0 <= val (cells b) < 10 ^ pos ->
  exists regs' m',
    msteps SEGS_B (mkst regs (Z_to_bv 64 0x0a9f2c) m rom)
                  (mkst regs' (Z_to_bv 64 (if rem - 19 <? 19 then 0x0aa414 else 0x0a9f2c)) m' rom)
    /\ bn_at SEGS_B m' o (ads_step (firstn 19 rest) b)
    /\ getr regs' 22%bv = Z_to_bv 64 (pos + 19) /\ getr regs' 21%bv = Z_to_bv 64 (rem - 19) /\ getr regs' 11%bv = Z_to_bv 64 (rem - 19)
    /\ getr regs' 24%bv = Z_to_bv 64 buf
    /\ keeps K19B regs regs'
    /\ AMBs m' /\ SL1s m' /\ SL2s m' /\ WINs m'
    /\ unch m m' NS2 /\ mem_grows m m'.
Proof.
  intros regs m done rest b pos rem Hsplit R9 R2 R24 R22 R21 R20 R26 R25 R19 AM L1 L2 W Hrem Hbn Hok Hn Hex Hval.
  assert (Epos : pos = Z.of_nat (length done)) by reflexivity. assert (Erem : rem = Z.of_nat (length rest)) by reflexivity.
  clearbody pos rem. assert (Hpos0 : 0 <= pos) by lia. assert (Hrem0 : 0 <= rem) by lia.
  assert (Hpr : pos + rem = len).
  { pose proof Hds as X. rewrite Hsplit, length_app in X. pose proof (g_len _ _ _ _ _ _ _ _ _ _ _ GG). lia. }
  pose proof GG as GG0. geom GG.
  set (ch := firstn 19 rest).
  assert (Hchl : length ch = 19%nat) by (unfold ch; rewrite length_firstn; lia).
  assert (Hchz : zlen ch = 19) by (unfold zlen; rewrite Hchl; reflexivity).
  pose proof DOK as DOK'. rewrite Hsplit in DOK'. destruct (digits_ok_app_inv _ _ DOK') as [DOKd DOKr].
  assert (DOKc : digits_ok ch) by (unfold ch; apply digits_ok_firstn; exact DOKr).
  pose proof AM as (SC & MC & TBL & TSH & OSH & DG & DSH & K27C). pose proof W as (Wsp & Wo & WF & WG).
  (* [comment removed for export] *)
  destruct (rd19_B regs m pos rem ch R9 R24 R22 R20 R26 R25 R21 L2 AM W Hchl DOKc) as (regs1 & M1 & A23 & A1 & A10 & A11 & K1); try lia.
  { intros k Hk. unfold ch. pose proof DG as DG'. unfold digs in DG'. rewrite Hsplit in DG'. rewrite <- (firstn_skipn 19 rest) in DG'.
    specialize (DG' (length done + k)%nat ltac:(rewrite !length_app, length_firstn; lia)).
    rewrite app_nth2 in DG' by lia. replace (length done + k - length done)%nat with k in DG' by lia.
    rewrite app_nth1 in DG' by (rewrite length_firstn; lia).
    eapply cellN_eqa; [exact DG' | lia | reflexivity]. }
  set (m1 := wbytes m _ _) in M1.
  assert (U01 : unch m m1 [(sp1 + 248, sp1 + 256)]) by (unfold m1; unchx).
  assert (G01 : mem_grows m m1) by (unfold m1; growsx).
  assert (S248 : cellN SEGS_B m1 (sp1 + 248) 8 rem) by (unfold m1; cellx2).
  pose proof (AMBu m m1 _ U01 ltac:(rngs) AM) as AM1. pose proof AM1 as (SC1 & MC1 & TBL1 & TSH1 & OSH1 & _ & _ & K27C1).
  pose proof (SL1u m m1 _ U01 ltac:(rngs) L1) as L11. pose proof (SL2u m m1 _ U01 ltac:(rngs) L2) as L21.
  pose proof (WINg m m1 G01 W) as W1. pose proof W1 as (Wsp1 & Wo1 & WF1 & WG1).
  assert (Hbn1 : bn_at SEGS_B m1 o b).
  { eapply bn_at_unch; [exact U01 | lia | cbn; lia | | exact Hbn]. intros r Hr. inr Hr ltac:(slia). }
  pose proof (decval_bound ch DOKc) as Hdv. rewrite Hchz in Hdv.
  (* [comment removed for export] *)
  assert (B2 : getr regs1 2%bv = Z_to_bv 64 sp1) by (kept K1 2 R2).
  destruct (mulpow10_B rom regs1 m1 o 19 sp1 (Z_to_bv 64 0x0aa2c4) b A10 A11 B2 A1 ltac:(vm_compute; reflexivity)
              ltac:(lia) Hbn1 Hok Hn) as (regs2 & m2 & M2 & K2 & Hbn2 & Htbl2 & U12 & G12).
  { apply (val_bound_mul _ pos 19); lia. }
  { rewrite Hex. cbn. lia. }
  { exact TBL1. } { exact TSH1. } { exact SC1. } { exact OSH1. } { exact K27C1. } { lia. } { lia. } { lia. } { lia. } { lia. } { flia. }
  { eapply store_ok_of_def_in; [exact Wo1|]. zwidth. lia. }
  { eapply store_ok_of_def_in; [exact Wsp1|]. zwidth. lia. }
  pose proof (mulpow10_spec 19 b Hok Hn ltac:(lia)) as SPM. cbn zeta in SPM. destruct SPM as (Hok2 & Hn2 & Hv2 & Hex2 & Hnil2).
  assert (Hex2' : ex (mulpow10 19 b) = 0).
  { destruct (cells b) eqn:Ec; [unfold mulpow10; cbn [Z.eqb]; rewrite Ec; exact Hex | rewrite Hex2 by congruence; rewrite Hex; reflexivity]. }
  assert (Hv2b : 0 <= val (cells (mulpow10 19 b)) < B ^ 124).
  { split; [apply val_nonneg; exact Hok2|]. rewrite Hv2. change (19 mod 28) with 19. apply (proj1 (val_bound_next _ pos Hval ltac:(lia) ltac:(lia))). }
  assert (Hlen2 : zlen (cells (mulpow10 19 b)) <= 124) by (apply len_bound; auto; lia).
  remember (mulpow10 19 b) as b1 eqn:Eb1. destruct b1 as [l1 e1]. cbn [cells BnModel.ex] in *. subst e1.
  pose proof (AMBu m1 m2 _ U12 ltac:(rngs) AM1) as AM2.
  pose proof (SL1u m1 m2 _ U12 ltac:(rngs) L11) as L12. pose proof (SL2u m1 m2 _ U12 ltac:(rngs) L21) as L22.
  pose proof (WINg m1 m2 G12 W1) as W2.
  assert (S248' : cellN SEGS_B m2 (sp1 + 248) 8 rem).
  { eapply cellN_unch; [exact U12 | lia | cbn; lia | | exact S248]. intros r Hr. inr Hr ltac:(slia). }
  (* [comment removed for export] *)
  assert (C23 : getr regs2 23%bv = Z_to_bv 64 (decval ch)) by (kept K2 23 A23).
  assert (C9 : getr regs2 9%bv = Z_to_bv 64 sp1) by (etransitivity; [exact (K2 9 ltac:(in_list)) | kept K1 9 R9]).
  assert (C2 : getr regs2 2%bv = Z_to_bv 64 sp1) by (kept K2 2 B2).
  assert (C25 : getr regs2 25%bv = Z_to_bv 64 o) by (etransitivity; [exact (K2 25 ltac:(in_list)) | kept K1 25 R25]).
  assert (C19 : getr regs2 19%bv = Z_to_bv 64 MASK) by (etransitivity; [exact (K2 19 ltac:(in_list)) | kept K1 19 R19]).
  assert (C22 : getr regs2 22%bv = Z_to_bv 64 pos) by (etransitivity; [exact (K2 22 ltac:(in_list)) | kept K1 22 R22]).
  assert (C24 : getr regs2 24%bv = Z_to_bv 64 buf) by (etransitivity; [exact (K2 24 ltac:(in_list)) | kept K1 24 R24]).
  assert (K12 : keeps K19B regs regs2).
  { eapply keeps_trans; [eapply keeps_sub_dec; [exact K1|]; vm_compute; reflexivity | eapply keeps_sub_dec; [exact K2|]; vm_compute; reflexivity]. }
  (* [comment removed for export] *)
  assert (ADDP : exists regs3 m3,
    msteps SEGS_B (mkst regs2 (Z_to_bv 64 0x0aa2c4) m2 rom) (mkst regs3 (Z_to_bv 64 0x0a9f14) m3 rom)
    /\ bn_at SEGS_B m3 o (add_u64 (decval ch) (BN l1 0))
    /\ getr regs3 18%bv = Z_to_bv 64 rem /\ getr regs3 22%bv = Z_to_bv 64 pos
    /\ keeps K19B regs2 regs3
    /\ unch m2 m3 ((sp1 - 128, sp1) :: NSs) /\ mem_grows m2 m3).
  { unfold add_u64. destruct (Z.eqb_spec (decval ch) 0) as [Hd0|Hd0].
    - zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (KHI + 256, HIE - 384); Some (0, 780)])
                              [KC (ZV 32) 248 8 (ZV 33)] (@nil kwin))
        10%nat [0x0a9f14; 0x0aa2cc] (SCR [] []) constr:([(9%bv : reg, ZV 32); (23%bv : reg, ZL 0)])
        [sp1; rem] constr:([Some (KHI + 256, HIE - 384); Some (0, 780)]) regs2 m2 rom 0x0aa2c4.
      zx_use2 ZXB ltac:(zx_pins; rewrite C23, Hd0; reflexivity) ltac:(zx_lia) ltac:(kc1 S248'; exact I) ltac:(exact I) ltac:(exact I). zx_name regs3.
      eexists regs3, m2. split; [exact ZM|]. split; [exact Hbn2|].
      split; [zx_regv ZR|]. split; [etransitivity; [exact (reg_kept _ _ _ _ (22%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact C22]|].
      split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
      split; [apply unch_refl | apply mem_grows_refl].
    - zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (KHI + 256, HIE - 384); Some (0, 780); Some (1, 2 ^ 64 - 1)])
                              [KC (ZV 32) 248 8 (ZV 33)] (@nil kwin))
        10%nat [0x0a9f14; 0x0aa2cc] (SCR [] []) constr:([(9%bv : reg, ZV 32); (23%bv : reg, ZV 34)])
        [sp1; rem; decval ch] constr:([Some (KHI + 256, HIE - 384); Some (0, 780); Some (1, 2 ^ 64 - 1)]) regs2 m2 rom 0x0aa2c4.
      zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 S248'; exact I) ltac:(exact I) ltac:(exact I). zx_name regs3.
      assert (K3 : keeps [2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 24; 25; 26; 27] regs2 regs3) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
      zx_reg ZR (18%bv : reg) as D18.
      destruct (au64add_B1 rom o buf len sp sp1 FS p2 g og bg0 bgl ds GG0 Hds (add_B rom) regs3 m2 (decval ch) l1) as (regs4 & m4 & M4 & Hbn4 & K4 & U4 & G4).
      { kept K3 9 C9. } { kept K3 2 C2. } { kept K3 25 C25. } { kept K3 23 C23. } { kept K3 19 C19. }
      { lia. } { exact Hbn2. } { exact Hok2. } { lia. } { exact AM2. } { exact L12. } { exact L22. } { exact W2. }
      eexists regs4, m4. split; [eapply msteps_trans; [exact ZM | exact M4]|].
      split; [unfold add_bn; cbn [cells BnModel.ex]; exact Hbn4|].
      split; [kept K4 18 D18|]. split; [etransitivity; [exact (K4 22 ltac:(in_list)) | kept K3 22 C22]|].
      split; [eapply keeps_trans; [eapply keeps_sub_dec; [exact K3|]; vm_compute; reflexivity | eapply keeps_sub_dec; [exact K4|]; vm_compute; reflexivity]|].
      split; [exact U4 | exact G4]. }
  destruct ADDP as (regs3 & m3 & M3 & Hbn3 & D18 & D22 & K3 & U23 & G23).
  (* [comment removed for export] *)
  assert (LATCH : forall (dir : bool) tgt, (if dir then rem <= 37 /\ tgt = 0x0aa414 else 37 < rem /\ tgt = 0x0a9f2c) ->
    exists regs4,
      msteps SEGS_B (mkst regs3 (Z_to_bv 64 0x0a9f14) m3 rom) (mkst regs4 (Z_to_bv 64 tgt) m3 rom)
      /\ getr regs4 22%bv = Z_to_bv 64 (pos + 19) /\ getr regs4 21%bv = Z_to_bv 64 (rem - 19) /\ getr regs4 11%bv = Z_to_bv 64 (rem - 19)
      /\ keeps [2; 3; 4; 8; 9; 18; 19; 20; 23; 24; 25; 26; 27] regs3 regs4).
  { intros dir tgt Hdir. destruct dir; destruct Hdir as [Hc ->].
    - zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (0, 761); Some (19, 37)]) (@nil kcell) (@nil kwin)) 10%nat [0x0aa414; 0x0a9f2c] (SCR [] [])
        constr:([(22%bv : reg, ZV 32); (18%bv : reg, ZV 33)]) [pos; rem] constr:([Some (0, 761); Some (19, 37)]) regs3 m3 rom 0x0a9f14.
      zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs4.
      exists regs4. split; [exact ZM|]. split; [zx_regv ZR|]. split; [zx_regv ZR|]. split; [zx_regv ZR|].
      eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity.
    - zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (0, 761); Some (38, 780)]) (@nil kcell) (@nil kwin)) 10%nat [0x0aa414; 0x0a9f2c] (SCR [] [])
        constr:([(22%bv : reg, ZV 32); (18%bv : reg, ZV 33)]) [pos; rem] constr:([Some (0, 761); Some (38, 780)]) regs3 m3 rom 0x0a9f14.
      zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs4.
      exists regs4. split; [exact ZM|]. split; [zx_regv ZR|]. split; [zx_regv ZR|]. split; [zx_regv ZR|].
      eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity. }
  assert (U03 : unch m m3 NS2).
  { unfold NS2. eapply unch_trans; [unch_ns U01|]. eapply unch_trans; [unch_ns U12 | unch_ns U23]. }
  assert (G03 : mem_grows m m3) by (eapply mem_grows_trans; [exact G01|]; eapply mem_grows_trans; [exact G12 | exact G23]).
  assert (FIN : forall tgt regs4,
    msteps SEGS_B (mkst regs3 (Z_to_bv 64 0x0a9f14) m3 rom) (mkst regs4 (Z_to_bv 64 tgt) m3 rom) ->
    getr regs4 22%bv = Z_to_bv 64 (pos + 19) -> getr regs4 21%bv = Z_to_bv 64 (rem - 19) -> getr regs4 11%bv = Z_to_bv 64 (rem - 19) ->
    keeps [2; 3; 4; 8; 9; 18; 19; 20; 23; 24; 25; 26; 27] regs3 regs4 ->
    exists regs' m',
      msteps SEGS_B (mkst regs (Z_to_bv 64 0x0a9f2c) m rom) (mkst regs' (Z_to_bv 64 tgt) m' rom)
      /\ bn_at SEGS_B m' o (ads_step ch b)
      /\ getr regs' 22%bv = Z_to_bv 64 (pos + 19) /\ getr regs' 21%bv = Z_to_bv 64 (rem - 19) /\ getr regs' 11%bv = Z_to_bv 64 (rem - 19)
      /\ getr regs' 24%bv = Z_to_bv 64 buf
      /\ keeps K19B regs regs'
      /\ AMBs m' /\ SL1s m' /\ SL2s m' /\ WINs m'
      /\ unch m m' NS2 /\ mem_grows m m').
  { intros tgt regs4 M4 E22 E21 E11 K4.
    eexists regs4, m3. split; [eapply msteps_trans; [exact M1|]; eapply msteps_trans; [exact M2|]; eapply msteps_trans; [exact M3 | exact M4]|].
    split; [unfold ads_step; rewrite Hchz, <- Eb1; unfold decval in Hbn3; exact Hbn3|].
    split; [exact E22|]. split; [exact E21|]. split; [exact E11|].
    split; [etransitivity; [exact (K4 24 ltac:(in_list)) | etransitivity; [exact (K3 24 ltac:(in_list)) | exact C24]]|].
    split; [eapply keeps_trans; [exact K12|]; eapply keeps_trans; [exact K3 | eapply keeps_sub_dec; [exact K4|]; vm_compute; reflexivity]|].
    split; [exact (AMBu m2 m3 _ U23 ltac:(unfold NS; rngs) AM2)|].
    split; [exact (SL1u m2 m3 _ U23 ltac:(unfold NS; rngs) L12)|].
    split; [exact (SL2u m2 m3 _ U23 ltac:(unfold NS; rngs) L22)|].
    split; [exact (WINg m2 m3 G23 W2)|].
    split; [exact U03 | exact G03]. }
  destruct (Z.ltb_spec (rem - 19) 19) as [Hlt|Hge].
  - destruct (LATCH true 0x0aa414 ltac:(split; [lia|reflexivity])) as (regs4 & M4 & E22 & E21 & E11 & K4). eapply FIN; eauto.
  - destruct (LATCH false 0x0a9f2c ltac:(split; [lia|reflexivity])) as (regs4 & M4 & E22 & E21 & E11 & K4). eapply FIN; eauto.
Qed.

End S.
