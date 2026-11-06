(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare BnModel BnMath BnMem BnDefs LibIface BnCbdLib.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIfaceA AsRtLib AsZX AsZXTac AsZXDefs BnA_lib BnA_au64 BnA_shl BnA_cmp BnA_mul6 BnA_frame AsFree5A BnA_ads1 BnA_ads4 BnA_ads6 BnA_cbd1.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Ltac flia0 := first [ lia | match goal with H : hide _ |- _ => unfold hide in H; lia end | (unfold hide in *; lia) ].
#[local] Ltac BnA_ads1.flia ::= lf_once flia0.
Ltac inr0 H tac := cbn [In] in H; repeat (destruct H as [<-|H]; [tac|]); destruct H.
#[local] Ltac BnA_ads1.inr H tac ::= lf_once ltac:(inr0 H tac).
Import ListNotations. Import ZXA BM. Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section S.
Context {fx : FPState}.
Variable rom : word -> option byte.
Variables (buf len sp FS bg0 bgl : Z) (ds : list Z) (p F g g0 expo e w4 : Z) (f ret : word).
Hypothesis CE : cbdE buf len sp FS bg0 bgl.
Hypothesis Hds : length ds = Z.to_nat len.
Hypothesis DOK : digits_ok ds.
Hypothesis Hp : 0 <= p < 512.
Hypothesis HF : F = FS + 5279744 + p * 2048.
Hypothesis HgF : F = 8 * (g - SHA).
Hypothesis Hg0 : FS + 5279744 = 8 * (g0 - SHA).
Hypothesis Hle : -323 <= len + expo <= 309.
Hypothesis He : -2047 <= e <= 2047.
Hypothesis Hw4 : 0 <= w4 < 2 ^ 64.
Hypothesis Hw4e : bv_swrap 32 w4 = e.
Hypothesis Hw4n : bv_swrap 32 (0 - w4) = - e.
Hypothesis Hret : ret_ok ret.
(* [comment removed for export] *)
Hypothesis ads_A_h : forall (o buf len sp FS og bg0 bgl : Z) (ds : list Z) (fl : Z -> Z),
  adsE o buf len sp FS og bg0 bgl -> length ds = Z.to_nat len -> digits_ok ds ->
  (forall j, 0 <= j < 512 -> fl j = 0 \/ fl j = 1) -> (exists j, 0 <= j < 512 /\ fl j = 0) ->
  (forall j, 0 <= j < 512 -> fl j = 0 -> o + 516 <= FS + 5279744 + j * 2048 \/ FS + 5279744 + j * 2048 + 2048 <= o) ->
  (forall j, 0 <= j < 512 -> fl j = 0 -> buf + len <= FS + 5279744 + j * 2048 \/ FS + 5279744 + j * 2048 + 2048 <= buf) ->
  forall regs m (ret : word),
  getr regs 10%bv = Z_to_bv 64 o -> getr regs 11%bv = Z_to_bv 64 buf -> getr regs 12%bv = Z_to_bv 64 len ->
  getr regs 2%bv = Z_to_bv 64 sp -> getr regs 1%bv = ret -> bv_unsigned ret mod 4 = 0 -> getr regs 4%bv = Z_to_bv 64 TP_A ->
  rt_ok m -> ro_ok SEGS_A RO_A m -> gsh_ok m -> objsh m o -> digs buf ds m -> dsh bg0 bgl m ->
  mem_def m (sp - 656) 656 -> mem_def m o 516 ->
  malloc_ctx_ok (sp - 656) sp FS m -> rd_u64 m FSTLS_A FS ->
  mem_def m FS FS_LEN -> mem_def m (sh FS + FS_SHLO) (FS_SHHI - FS_SHLO) -> mem_u64 m (FS + 88) 20 -> mem_byte m (FS + 96) 0 ->
  (forall j, 0 <= j < 512 -> mem_byte m (fs_flag FS 5 j) (fl j)) ->
  exists regs' m' p,
    msteps SEGS_A (mkst regs (Z_to_bv 64 0x0a9c3c) m rom) (mkst regs' ret m' rom)
    /\ keeps CS regs regs' /\ bn_at SEGS_A m' o (assign_decimal ds)
    /\ 0 <= p < 512 /\ fl p = 0
    /\ (forall j, 0 <= j < 512 -> mem_byte m' (fs_flag FS 5 j) (fl j))
    /\ unch m m' [(sp - 656, sp); (o, o + 516); (FS + 40, FS + 48); (fs_flag FS 5 p, fs_flag FS 5 p + 1);
                  (fs_frame FS 5 p, fs_frame FS 5 p + 2048); (sh (fs_frame FS 5 p), sh (fs_frame FS 5 p) + 256)]
    /\ mem_grows m m'.

#[local] Abbreviation sp1 := (csp1 sp).
Ltac kept K n H := etransitivity; [exact (K n ltac:(in_list)) | exact H].
(* [comment removed for export] *)
Definition fl1 (j : Z) : Z := if j =? p then 1 else 0.

(* [comment removed for export] *)
Definition CS3A : list Z := [3; 4; 8; 9; 18; 20; 21; 22; 23; 24; 25; 26; 27].

(* [comment removed for export] *)
Definition CW : list (Z * Z) :=
  [(sp - 3072, sp1); (FS + 40, FS + 48); (FS + 35840, FS + 36352); (FS + 5279744, FS + 6328320); (g0, g0 + 131072)].

Definition a0 : bn := assign_decimal ds.
Definition b0 : bn := assign_u64 (bv_unsigned f).
Definition a1 : bn := if 0 <=? expo then mulpow10 expo a0 else a0.
Definition b1 : bn := if 0 <=? expo then b0 else mulpow10 (- expo) b0.
Definition b2 : bn := if 0 <? e then shl e b1 else b1.
Definition a2 : bn := if 0 <? e then a1 else shl (- e) a1.

(* [comment removed for export] *)
Ltac uw1 :=
  first [ lazymatch goal with |- exists r', _ /\ fst r' <= ?a /\ ?b <= snd r' => exists (a, b); split; [solve [in_list] | cbn [fst snd]; lia] end
        | eexists; split; [left; reflexivity | cbn [fst snd]; lia]
        | eexists; split; [right; left; reflexivity | cbn [fst snd]; lia]
        | eexists; split; [do 2 right; left; reflexivity | cbn [fst snd]; lia]
        | eexists; split; [do 3 right; left; reflexivity | cbn [fst snd]; lia]
        | eexists; split; [do 4 right; left; reflexivity | cbn [fst snd]; lia]
        | eexists; split; [do 5 right; left; reflexivity | cbn [fst snd]; lia]
        | eexists; split; [do 6 right; left; reflexivity | cbn [fst snd]; lia] ].
Ltac uwiden U := eapply unch_widen; [exact U|]; let rg := fresh "rg" in let H := fresh "Hrg" in intros rg H; cbn [fst snd]; inr H ltac:(uw1).

#[using="Type"] Lemma SAV_unchC : forall sp0 m m' rs vs,
  unch m m' rs -> (forall r, In r rs -> snd r <= sp0 - 104 \/ sp0 <= fst r) -> KHI <= sp0 - 104 -> sp0 <= HIE -> SAV sp0 m vs -> SAV sp0 m' vs.
Proof.
  clear. intros sp0 m m' rs vs U HR H1 H2 A k Hk.
  eapply cellN_unch; [exact U | lia | cbn; lia | | exact (A k Hk)].
  intros r Hr; specialize (HR r Hr); cbn; lia.
Qed.

(* [comment removed for export] *)
Abbreviation big := (Some (0, 18446744073709551615)).
Abbreviation ep_uvi := [Some (KHI + 3072, HIE); big; big; big; big; big; big; big; big; big; big; big; big; big; Some (-1, 1)].
Abbreviation ep_kn := [KC (ZV 32) (-8) 8 (ZV 33); KC (ZV 32) (-16) 8 (ZV 34); KC (ZV 32) (-24) 8 (ZV 35); KC (ZV 32) (-32) 8 (ZV 36);
  KC (ZV 32) (-40) 8 (ZV 37); KC (ZV 32) (-48) 8 (ZV 38); KC (ZV 32) (-56) 8 (ZV 39); KC (ZV 32) (-64) 8 (ZV 40);
  KC (ZV 32) (-72) 8 (ZV 41); KC (ZV 32) (-80) 8 (ZV 42); KC (ZV 32) (-88) 8 (ZV 43); KC (ZV 32) (-96) 8 (ZV 44);
  KC (ZV 32) (-104) 8 (ZV 45)].

(* [comment removed for export] *)
#[using="e CE Hds DOK Hp HF HgF Hle He Hw4 ads_A_h"] Lemma cbd_ph12 : forall regs regsP mP,
  getr regsP 1%bv = Z_to_bv 64 0x0a966c -> getr regsP 10%bv = Z_to_bv 64 (F + 32) -> getr regsP 11%bv = Z_to_bv 64 buf ->
  getr regsP 12%bv = Z_to_bv 64 len -> getr regsP 2%bv = Z_to_bv 64 sp1 -> getr regsP 4%bv = Z_to_bv 64 TP_A ->
  getr regsP 9%bv = Z_to_bv 64 sp1 -> getr regsP 8%bv = Z_to_bv 64 sp -> getr regsP 18%bv = Z_to_bv 64 F ->
  getr regsP 20%bv = Z_to_bv 64 expo -> getr regsP 21%bv = Z_to_bv 64 g -> getr regsP 22%bv = Z_to_bv 64 (g + 86) ->
  getr regsP 23%bv = Z_to_bv 64 F -> getr regsP 24%bv = Z_to_bv 64 (F + 32) -> getr regsP 25%bv = Z_to_bv 64 (F + 688) ->
  getr regsP 26%bv = Z_to_bv 64 buf -> getr regsP 27%bv = Z_to_bv 64 (g + 4) ->
  cellN SEGS_A mP (sp1 + 16) 8 (bv_unsigned f) -> cellN SEGS_A mP (sp1 + 24) 8 w4 ->
  SAV sp mP (savs regs ret) -> objsh mP (F + 32) -> objsh mP (F + 688) ->
  rt_ok mP -> ro_ok SEGS_A RO_A mP -> gsh_ok mP -> digs buf ds mP -> dsh bg0 bgl mP ->
  malloc_ctx_ok (sp - 3072) sp FS mP -> rd_u64 mP FSTLS_A FS -> mem_def mP (sp - 3072) 3072 ->
  mem_def mP FS FS_LEN -> mem_def mP (sh FS + FS_SHLO) (FS_SHHI - FS_SHLO) -> mem_u64 mP (FS + 88) 20 -> mem_byte mP (FS + 96) 0 ->
  (forall j, 0 <= j < 512 -> j <> p -> mem_byte mP (fs_flag FS 5 j) 0) -> mem_byte mP (FS + 35840 + p) 1 ->
  mem_u64 mP (F + 2040) (FS + 35840 + p) ->
  getr regs 1%bv = ret ->
  exists regsC mC pA FA gA,
    msteps SEGS_A (mkst regsP (Z_to_bv 64 0x0a9c3c) mP rom) (mkst regsC (Z_to_bv 64 0x0a9678) mC rom)
    /\ 0 <= pA < 512 /\ pA <> p /\ FA = FS + 5279744 + pA * 2048 /\ FA = 8 * (gA - SHA)
    /\ keeps CS3A regsP regsC /\ getr regsC 2%bv = Z_to_bv 64 sp1
    /\ bn_at SEGS_A mC (F + 32) a0 /\ bn_at SEGS_A mC (F + 688) b0 /\ cellN SEGS_A mC (sp1 + 24) 8 w4
    /\ rt_ok mC /\ ro_ok SEGS_A RO_A mC /\ gsh_ok mC /\ objsh mC (F + 32) /\ objsh mC (F + 688)
    /\ (forall j, 0 <= j < 512 -> mem_byte mC (fs_flag FS 5 j) (fl1 j))
    /\ unch mP mC [(sp1 - 656, sp1); (F + 32, F + 548); (F + 688, F + 1204); (FS + 40, FS + 48); (FS + 35840 + pA, FS + 35840 + pA + 1); (FA, FA + 2048); (gA, gA + 256)]
    /\ mem_grows mP mC.
Proof.
  intros regs regsP mP P1 P10 P11 P12 P2 P4 P9 P8 P18 P20 P21 P22 P23 P24 P25 P26 P27 S16 S24 SV OBA OBB RT RO GSH DG DSH MCX TLS Dsp
    DFS DSHD L88 B96 FL0 FL1 Q2040 R1.
  pose proof (csp1_facts buf len sp FS bg0 bgl CE) as (Hs1 & [q1 Hq1] & _).
  pose proof CE as CE0. destruct CE as [Eb1 Eb2 Elen Ebg0 Ebgl Esp1 Esp2 [qs Hqs] Efs1 Efs2 [qf Hqf] Dbsp DspFS Dbh Dbfl Dbfr].
  destruct Eb1 as [Eb1 Zb].   (* [comment removed for export] *)
  unfold FS_LEN in *. hide Zb; hide Dbh; hide Dbfl; hide Dbfr; hide DspFS; hide Dbsp.
  pose proof (u64_range f) as Hfr. pose proof (u64_range ret) as Hrr.
  assert (Elen2 : zlen ds = len) by (unfold zlen; lia).
  (* [comment removed for export] *)
  pose proof (cbd_facts ds len expo (bv_unsigned f) e DOK Elen2 Elen Hle ltac:(lia) He) as CF. cbn zeta in CF.
  destruct CF as ((Aok & An & Aex & Aval5) & (Bok & Bn & Bex & Bval5) & (A1ok & A1n & A1len & A1ex) & (B1ok & B1n & B1len & B1ex) & A2ok' & B2ok').
  change (assign_decimal ds) with a0 in *. change (assign_u64 (bv_unsigned f)) with b0 in *.
  (* [comment removed for export] *)
  remember (B ^ 124) as TOP eqn:ETOP. hide ETOP.
  (* [comment removed for export] *)
  assert (AE : adsE (F + 32) buf len sp1 FS (g - SHA + 4) bg0 bgl).
  { constructor; unfold FS_LEN; [lia | lia | lia | exact (conj Eb1 Zb) | lia | lia | lia | lia | lia | lia | exists (2 * q1); lia | lia | lia | exists qf; exact Hqf
      | unfold hide in DspFS; lia | unfold hide in Dbsp; lia | unfold hide in Dbfr; lia | unfold hide in DspFS; lia | lia
      | unfold hide in Dbh; lia | unfold hide in Dbfl; lia]. }
  assert (Hfl01 : forall j, 0 <= j < 512 -> fl1 j = 0 \/ fl1 j = 1) by (intros j Hj; unfold fl1; destruct (j =? p); auto).
  assert (Hflex : exists j, 0 <= j < 512 /\ fl1 j = 0).
  { unfold fl1. destruct (Z.eq_dec p 0) as [->|Hne]; [exists 1 | exists 0]; split; try lia;
      [reflexivity | destruct (Z.eqb_spec 0 p); [lia | reflexivity]]. }
  assert (HoFR : forall j, 0 <= j < 512 -> fl1 j = 0 -> F + 32 + 516 <= FS + 5279744 + j * 2048 \/ FS + 5279744 + j * 2048 + 2048 <= F + 32).
  { intros j Hj Hf0. unfold fl1 in Hf0. destruct (Z.eqb_spec j p); [discriminate|]. lia. }
  assert (HbFR : forall j, 0 <= j < 512 -> fl1 j = 0 -> buf + len <= FS + 5279744 + j * 2048 \/ FS + 5279744 + j * 2048 + 2048 <= buf).
  { intros j Hj _. unfold hide in Dbfr. lia. }
  destruct (ads_A_h (F + 32) buf len sp1 FS (g - SHA + 4) bg0 bgl ds fl1 AE Hds DOK Hfl01 Hflex HoFR HbFR regsP mP (Z_to_bv 64 0x0a966c)
              P10 P11 P12 P2 P1 ltac:(vm_compute; reflexivity) P4 RT RO GSH OBA DG DSH)
    as (regsA & mA & pA & MA & KA & HA & HpA & HflA & FLA & UA & GA).
  { eapply mem_def_sub; [exact Dsp | lia | lia]. }
  { eapply mem_def_sub; [exact DFS | lia | lia]. }
  { eapply (malloc_ctx_ok_unch _ _ _ _ _ _ _ (@nil (Z * Z))); [exact MCX | apply unch_refl | apply mem_grows_refl | intros r Hr; destruct Hr | lia | lia]. }
  { exact TLS. } { exact DFS. } { exact DSHD. } { exact L88. } { exact B96. }
  { intros j Hj. unfold fl1. destruct (Z.eqb_spec j p) as [->|Hne]; [rewrite fs_flag5; exact FL1 | exact (FL0 j Hj Hne)]. }
  assert (HpAne : pA <> p) by (intros ->; unfold fl1 in HflA; rewrite Z.eqb_refl in HflA; discriminate).
  clear Dbh Dbfl Dbfr Dbsp HbFR HoFR Hfl01 Hflex.
  rewrite fs_flag5, fs_frame5 in UA. unfold sh, SH_A in UA.
  set (FA := FS + 5279744 + pA * 2048) in *.
  assert (HFA : FA = FS + 5279744 + pA * 2048) by reflexivity.
  set (gA := 2147450880 + FA / 8) in *.
  assert (HgA : FA = 8 * (gA - SHA)) by (subst gA FA; rewrite Hqf; lia). clearbody FA gA.
  assert (HAPART : FA + 2048 <= F \/ F + 2048 <= FA) by lia.
  (* [comment removed for export] *)
  assert (KA2 : getr regsA 2%bv = Z_to_bv 64 sp1) by (kept KA 2 P2).
  assert (KA9 : getr regsA 9%bv = Z_to_bv 64 sp1) by (kept KA 9 P9).
  assert (KA25 : getr regsA 25%bv = Z_to_bv 64 (F + 688)) by (kept KA 25 P25).
  assert (S16A : cellN SEGS_A mA (sp1 + 16) 8 (bv_unsigned f)).
  { eapply cellN_unch; [exact UA | lia | cbn; lia | intros r Hr; inr Hr ltac:(slia) | exact S16]. }
  assert (S24A : cellN SEGS_A mA (sp1 + 24) 8 w4).
  { eapply cellN_unch; [exact UA | lia | cbn; lia | intros r Hr; inr Hr ltac:(slia) | exact S24]. }
  assert (HRA : forall r, In r [(sp1 - 656, sp1); (F + 32, F + 32 + 516); (FS + 40, FS + 48); (FS + 35840 + pA, FS + 35840 + pA + 1); (FA, FA + 2048); (gA, gA + 256)] -> highr r)
    by (intros r Hr; unfold highr; inr Hr ltac:(cbn; lia)).
  assert (RTA : rt_ok mA) by (eapply rt_ok_unch; [exact UA | exact HRA | exact RT]).
  assert (ROA : ro_ok SEGS_A RO_A mA) by (eapply ro_ok_unchA; [exact UA | exact HRA | exact RO]).
  assert (GSHA : gsh_ok mA) by (eapply gsh_ok_unch; [exact UA | exact HRA | exact GSH]).
  assert (OBBA : objsh mA (F + 688)).
  { eapply (objsh_unch2 mP mA); [exact UA | intros r Hr; inr Hr ltac:(slia) | lia | lia | exact OBB]. }
  assert (OBAA : objsh mA (F + 32)).
  { eapply (objsh_unch2 mP mA); [exact UA | intros r Hr; inr Hr ltac:(slia) | lia | lia | exact OBA]. }
  (* [comment removed for export] *)
  zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (KHI + 2048, HIE - 160); Some (IMG, HIE - 2048); Some (0, 18446744073709551615)]) [KC (ZV 32) 16 8 (ZV 34)] (@nil kwin))
    10%nat [0x0a9b40] (SCR [] []) constr:([(9%bv : reg, ZV 32); (25%bv : reg, ZAdd (ZV 33) (ZL 688))]) [sp1; F; bv_unsigned f]
    constr:([Some (KHI + 2048, HIE - 160); Some (IMG, HIE - 2048); Some (0, 18446744073709551615)]) regsA mA rom 0x0a966c.
  zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 S16A; exact I) ltac:(exact I) ltac:(exact I). zx_name regsB.
  assert (KB : keeps CS' regsA regsB) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
  destruct (au64_A regsB mA rom (F + 688) (bv_unsigned f) sp1 (Z_to_bv 64 0x0a9678)) as (regsC & mC & MC & KC' & HB & UC & GC);
    try (zx_regv ZR).
  { vm_compute. reflexivity. } { zwidth. lia. } { lia. } { lia. } { lia. } { lia. } { lia. } { flia. }
  { exact (shcells_intro mA RTA ROA). } { exact OBBA. }
  { eapply store_ok_of_def_in; [eapply mem_def_grows; [exact GA | exact DFS]|]. zwidth. lia. }
  { eapply store_ok_of_def_in; [eapply mem_def_grows; [exact GA | exact Dsp]|]. zwidth. lia. }
  change (assign_u64 (bv_unsigned f)) with b0 in HB.
  assert (HA3 : bn_at SEGS_A mC (F + 32) a0).
  { eapply (bn_at_unch SEGS_A mA mC); [exact UC | lia | cbn; lia | intros rg Hrg; inr Hrg ltac:(slia) | exact HA]. }
  assert (KPC : keeps CS3A regsP regsC).
  { eapply keeps_trans; [eapply keeps_sub_dec; [exact KA|]; vm_compute; reflexivity|].
    eapply keeps_trans; [eapply keeps_sub_dec; [exact KB|]; vm_compute; reflexivity|]. eapply keeps_sub_dec; [exact KC'|]; vm_compute; reflexivity. }
  assert (C20 : getr regsC 20%bv = Z_to_bv 64 expo) by (kept KPC 20 P20).
  assert (C2 : getr regsC 2%bv = Z_to_bv 64 sp1) by (etransitivity; [exact (KC' 2 ltac:(in_list)) | zx_regv ZR]).
  assert (C9 : getr regsC 9%bv = Z_to_bv 64 sp1) by (kept KPC 9 P9).
  assert (C24 : getr regsC 24%bv = Z_to_bv 64 (F + 32)) by (kept KPC 24 P24).
  assert (C25 : getr regsC 25%bv = Z_to_bv 64 (F + 688)) by (kept KPC 25 P25).
  assert (UAC : unch mA mC [(F + 688, F + 1204); (sp1 - 16, sp1)]) by (replace (F + 1204) with (F + 688 + 516) by lia; exact UC).
  assert (MPC : msteps SEGS_A (mkst regsP (Z_to_bv 64 0x0a9c3c) mP rom) (mkst regsC (Z_to_bv 64 0x0a9678) mC rom)).
  { eapply msteps_trans; [exact MA|]. eapply msteps_trans; [exact ZM | exact MC]. }
  clear ZE ZR ZF ZM KB KC' UC.
  assert (RTC : rt_ok mC) by (eapply rt_ok_unch; [exact UAC | intros r Hr; unfold highr; inr Hr ltac:(cbn; lia) | exact RTA]).
  assert (ROC : ro_ok SEGS_A RO_A mC) by (eapply ro_ok_unchA; [exact UAC | intros r Hr; unfold highr; inr Hr ltac:(cbn; lia) | exact ROA]).
  assert (GSHC : gsh_ok mC) by (eapply gsh_ok_unch; [exact UAC | intros r Hr; unfold highr; inr Hr ltac:(cbn; lia) | exact GSHA]).
  assert (OBAC : objsh mC (F + 32)) by (eapply (objsh_unch2 mA mC); [exact UAC | intros r Hr; inr Hr ltac:(cbn; lia) | lia | lia | exact OBAA]).
  assert (OBBC : objsh mC (F + 688)) by (eapply (objsh_unch2 mA mC); [exact UAC | intros r Hr; inr Hr ltac:(cbn; lia) | lia | lia | exact OBBA]).
  assert (S24C : cellN SEGS_A mC (sp1 + 24) 8 w4).
  { eapply cellN_unch; [exact UAC | lia | cbn; lia | intros r Hr; inr Hr ltac:(slia) | exact S24A]. }
  assert (GPC : mem_grows mP mC) by (eapply mem_grows_trans; [exact GA | exact GC]).
  assert (WstC : forall o n, sp - 3072 <= o -> o + Z.of_nat n <= sp -> RiscvSemantics.store_ok SEGS_A mC (Z_to_bv 64 o) n = true).
  { intros o n Ho1 Ho2. eapply store_ok_of_def_in; [eapply mem_def_grows; [exact GPC | exact Dsp]|]. lia. }
  assert (WoAC : RiscvSemantics.store_ok SEGS_A mC (Z_to_bv 64 (F + 32)) 516 = true).
  { eapply store_ok_of_def_in; [eapply mem_def_grows; [exact GPC | exact DFS]|]. zwidth. lia. }
  assert (WoBC : RiscvSemantics.store_ok SEGS_A mC (Z_to_bv 64 (F + 688)) 516 = true).
  { eapply store_ok_of_def_in; [eapply mem_def_grows; [exact GPC | exact DFS]|]. zwidth. lia. }
  eexists regsC, mC, pA, FA, gA. split; [exact MPC|]. split; [exact HpA|]. split; [exact HpAne|]. split; [exact HFA|]. split; [exact HgA|].
  split; [exact KPC|]. split; [exact C2|]. split; [exact HA3|]. split; [exact HB|]. split; [exact S24C|].
  split; [exact RTC|]. split; [exact ROC|]. split; [exact GSHC|]. split; [exact OBAC|]. split; [exact OBBC|].
  split.
  { intros j Hj. eapply mem_byte_unch; [exact UAC | rewrite fs_flag5; lia | intros r Hr; rewrite fs_flag5; inr Hr ltac:(slia) | exact (FLA j Hj)]. }
  split; [|exact GPC].
  eapply unch_trans; [uwiden UA | uwiden UAC].
Qed.

(* [comment removed for export] *)
#[using="buf len FS bg0 bgl p g CE Hds DOK Hp HF HgF Hle He Hw4 Hw4e"] Lemma cbd_ph3 : forall regsC mC,
  getr regsC 2%bv = Z_to_bv 64 sp1 -> getr regsC 9%bv = Z_to_bv 64 sp1 -> getr regsC 20%bv = Z_to_bv 64 expo ->
  getr regsC 24%bv = Z_to_bv 64 (F + 32) -> getr regsC 25%bv = Z_to_bv 64 (F + 688) ->
  bn_at SEGS_A mC (F + 32) a0 -> bn_at SEGS_A mC (F + 688) b0 -> cellN SEGS_A mC (sp1 + 24) 8 w4 ->
  rt_ok mC -> ro_ok SEGS_A RO_A mC -> gsh_ok mC -> objsh mC (F + 32) -> objsh mC (F + 688) ->
  RiscvSemantics.store_ok SEGS_A mC (Z_to_bv 64 (F + 32)) 516 = true ->
  RiscvSemantics.store_ok SEGS_A mC (Z_to_bv 64 (F + 688)) 516 = true ->
  (forall o n, sp - 3072 <= o -> o + Z.of_nat n <= sp -> RiscvSemantics.store_ok SEGS_A mC (Z_to_bv 64 o) n = true) ->
  exists regs5 m5 p5,
    (p5 = 0x0a9690 \/ p5 = 0x0a96b0)
    /\ msteps SEGS_A (mkst regsC (Z_to_bv 64 0x0a9678) mC rom) (mkst regs5 (Z_to_bv 64 p5) m5 rom)
    /\ bn_at SEGS_A m5 (F + 32) a1 /\ bn_at SEGS_A m5 (F + 688) b1
    /\ getr regs5 11%bv = Z_to_bv 64 e /\ getr regs5 10%bv = Z_to_bv 64 w4 /\ getr regs5 2%bv = Z_to_bv 64 sp1
    /\ keeps CS3A regsC regs5
    /\ unch mC m5 [(F + 32, F + 548); (F + 688, F + 1204); (sp1 - 48, sp1)] /\ mem_grows mC m5.
Proof.
  intros regsC mC C2 C9 C20 C24 C25 HA3 HB S24C RTC ROC GSHC OBAC OBBC WoAC WoBC WstC.
  pose proof (csp1_facts buf len sp FS bg0 bgl CE) as (Hs1 & [q1 Hq1] & _).
  pose proof CE as CE0. destruct CE as [Eb1 Eb2 Elen Ebg0 Ebgl Esp1 Esp2 [qs Hqs] Efs1 Efs2 [qf Hqf] Dbsp DspFS Dbh Dbfl Dbfr].
  unfold FS_LEN in *. clear Dbh Dbfl Dbfr Dbsp. hide DspFS.
  pose proof (u64_range f) as Hfr.
  assert (Elen2 : zlen ds = len) by (unfold zlen; lia).
  pose proof (cbd_facts ds len expo (bv_unsigned f) e DOK Elen2 Elen Hle ltac:(lia) He) as CF. cbn zeta in CF.
  destruct CF as ((Aok & An & Aex & Aval5) & (Bok & Bn & Bex & Bval5) & _).
  change (assign_decimal ds) with a0 in *. change (assign_u64 (bv_unsigned f)) with b0 in *.
  remember (B ^ 124) as TOP eqn:ETOP. hide ETOP.
  unfold a1, b1.
  destruct (Z.leb_spec 0 expo) as [Hx|Hx].
    - (* [comment removed for export] *)
      zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (KHI + 2048, HIE - 160); Some (IMG, HIE - 2048); Some (0, 308)]) (@nil kcell) (@nil kwin)) 10%nat [0x0aa610] (SCR [] [])
        constr:([(9%bv : reg, ZV 32); (20%bv : reg, ZV 34); (24%bv : reg, ZAdd (ZV 33) (ZL 32)); (25%bv : reg, ZAdd (ZV 33) (ZL 688))]) [sp1; F; expo]
        constr:([Some (KHI + 2048, HIE - 160); Some (IMG, HIE - 2048); Some (0, 308)]) regsC mC rom 0x0a9678.
      zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs4.
      assert (K4 : keeps CS' regsC regs4) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
      destruct (mulpow10_A rom regs4 mC (F + 32) expo sp1 (Z_to_bv 64 0x0a9688) a0) as (regs5 & m5 & M5 & K5 & HA5 & Htbl5 & U5 & G5);
        try (zx_regv ZR).
      { vm_compute. reflexivity. } { lia. } { exact HA3. } { exact Aok. } { exact An. } { unfold hide in ETOP; subst TOP; exact (Aval5 Hx). } { rewrite Aex. cbn. lia. }
      { exact (five_tbl_intro mC ROC). } { exact (tblsh_intro mC GSHC). } { exact (shcells_intro mC RTC ROC). } { exact OBAC. }
      { lia. } { lia. } { lia. } { lia. } { lia. } { flia. } { exact WoAC. } { apply WstC; lia. }
      (* [comment removed for export] *)
      rename ZE into ZE1. rename ZR into ZR1. rename ZF into ZF1. rename ZM into ZM1.
      assert (S24' : cellN SEGS_A m5 (sp1 + 24) 8 w4).
      { eapply cellN_unch; [exact U5 | lia | cbn; lia | intros r Hr; inr Hr ltac:(slia) | exact S24C]. }
      zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (KHI + 2048, HIE - 160); Some (0, 18446744073709551615)]) [KC (ZV 32) 24 8 (ZV 33)] (@nil kwin)) 3%nat [0x0a9690; 0x0a96b0] (SCR [] [])
        constr:([(9%bv : reg, ZV 32)]) [sp1; w4] constr:([Some (KHI + 2048, HIE - 160); Some (0, 18446744073709551615)]) regs5 m5 rom 0x0a9688.
      zx_use2 ZXB ltac:(zx_pins; etransitivity; [exact (K5 9 ltac:(in_list))|]; etransitivity; [exact (K4 9 ltac:(in_list)) | exact C9]) ltac:(zx_lia) ltac:(kc1 S24'; exact I) ltac:(exact I) ltac:(exact I).
      zx_name regs6.
      eexists regs6, m5, 0x0a9690. split; [left; reflexivity|].
      split; [eapply msteps_trans; [exact ZM1|]; eapply msteps_trans; [exact M5 | exact ZM]|].
      split; [exact HA5|].
      split; [eapply (bn_at_unch SEGS_A mC m5); [exact U5 | lia | cbn; lia | intros rg Hrg; inr Hrg ltac:(slia) | exact HB]|].
      split; [zx_reg ZR (11%bv : reg) as H; rewrite H; f_equal; exact Hw4e|].
      split; [zx_regv ZR|].
      split; [etransitivity; [exact (reg_kept _ _ _ _ (2%bv : reg) ZR ltac:(vm_compute; reflexivity))|]; etransitivity; [exact (K5 2 ltac:(in_list))|]; zx_regv ZR1|].
      split; [eapply keeps_trans; [eapply keeps_sub_dec; [exact K4|]; vm_compute; reflexivity|]; eapply keeps_trans; [eapply keeps_sub_dec; [exact K5|]; vm_compute; reflexivity|];
              eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
      split; [|exact G5].
      eapply unch_widen; [exact U5|]. intros rg Hrg; cbn [fst snd]; inr Hrg ltac:(first [eexists; split; [left; reflexivity | cbn; lia] | eexists; split; [do 2 right; left; reflexivity | cbn; lia]]).
    - (* [comment removed for export] *)
      zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (KHI + 2048, HIE - 160); Some (IMG, HIE - 2048); Some (-1103, -1)]) (@nil kcell) (@nil kwin)) 10%nat [0x0aa610] (SCR [] [])
        constr:([(9%bv : reg, ZV 32); (20%bv : reg, ZV 34); (24%bv : reg, ZAdd (ZV 33) (ZL 32)); (25%bv : reg, ZAdd (ZV 33) (ZL 688))]) [sp1; F; expo]
        constr:([Some (KHI + 2048, HIE - 160); Some (IMG, HIE - 2048); Some (-1103, -1)]) regsC mC rom 0x0a9678.
      zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs4.
      assert (K4 : keeps CS' regsC regs4) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
      destruct (mulpow10_A rom regs4 mC (F + 688) (- expo) sp1 (Z_to_bv 64 0x0a96a8) b0) as (regs5 & m5 & M5 & K5 & HB5 & Htbl5 & U5 & G5);
        try (zx_regv ZR).
      { vm_compute. reflexivity. } { lia. } { exact HB. } { exact Bok. } { exact Bn. } { unfold hide in ETOP; subst TOP; exact (Bval5 Hx). } { rewrite Bex. cbn. lia. }
      { exact (five_tbl_intro mC ROC). } { exact (tblsh_intro mC GSHC). } { exact (shcells_intro mC RTC ROC). } { exact OBBC. }
      { lia. } { lia. } { lia. } { lia. } { lia. } { flia. } { exact WoBC. } { apply WstC; lia. }
      rename ZE into ZE1. rename ZR into ZR1. rename ZF into ZF1. rename ZM into ZM1.
      assert (S24' : cellN SEGS_A m5 (sp1 + 24) 8 w4).
      { eapply cellN_unch; [exact U5 | lia | cbn; lia | intros r Hr; inr Hr ltac:(slia) | exact S24C]. }
      zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (KHI + 2048, HIE - 160); Some (0, 18446744073709551615)]) [KC (ZV 32) 24 8 (ZV 33)] (@nil kwin)) 3%nat [0x0a9690; 0x0a96b0] (SCR [] [])
        constr:([(9%bv : reg, ZV 32)]) [sp1; w4] constr:([Some (KHI + 2048, HIE - 160); Some (0, 18446744073709551615)]) regs5 m5 rom 0x0a96a8.
      zx_use2 ZXB ltac:(zx_pins; etransitivity; [exact (K5 9 ltac:(in_list))|]; etransitivity; [exact (K4 9 ltac:(in_list)) | exact C9]) ltac:(zx_lia) ltac:(kc1 S24'; exact I) ltac:(exact I) ltac:(exact I).
      zx_name regs6.
      eexists regs6, m5, 0x0a96b0. split; [right; reflexivity|].
      split; [eapply msteps_trans; [exact ZM1|]; eapply msteps_trans; [exact M5 | exact ZM]|].
      split; [eapply (bn_at_unch SEGS_A mC m5); [exact U5 | lia | cbn; lia | intros rg Hrg; inr Hrg ltac:(slia) | exact HA3]|].
      split; [exact HB5|].
      split; [zx_reg ZR (11%bv : reg) as H; rewrite H; f_equal; exact Hw4e|].
      split; [zx_regv ZR|].
      split; [etransitivity; [exact (reg_kept _ _ _ _ (2%bv : reg) ZR ltac:(vm_compute; reflexivity))|]; etransitivity; [exact (K5 2 ltac:(in_list))|]; zx_regv ZR1|].
      split; [eapply keeps_trans; [eapply keeps_sub_dec; [exact K4|]; vm_compute; reflexivity|]; eapply keeps_trans; [eapply keeps_sub_dec; [exact K5|]; vm_compute; reflexivity|];
              eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
      split; [|exact G5].
      eapply unch_widen; [exact U5|]. intros rg Hrg; cbn [fst snd]; inr Hrg ltac:(first [eexists; split; [right; left; reflexivity | cbn; lia] | eexists; split; [do 2 right; left; reflexivity | cbn; lia]]).
Qed.
(* [comment removed for export] *)
#[using="buf len FS bg0 bgl p g CE Hds DOK Hp HF HgF Hle He Hw4 Hw4n"] Lemma cbd_ph4 : forall regs5 m5 p5,
  (p5 = 0x0a9690 \/ p5 = 0x0a96b0) ->
  getr regs5 11%bv = Z_to_bv 64 e -> getr regs5 10%bv = Z_to_bv 64 w4 -> getr regs5 2%bv = Z_to_bv 64 sp1 ->
  getr regs5 24%bv = Z_to_bv 64 (F + 32) -> getr regs5 25%bv = Z_to_bv 64 (F + 688) ->
  bn_at SEGS_A m5 (F + 32) a1 -> bn_at SEGS_A m5 (F + 688) b1 ->
  rt_ok m5 -> ro_ok SEGS_A RO_A m5 -> objsh m5 (F + 32) -> objsh m5 (F + 688) ->
  RiscvSemantics.store_ok SEGS_A m5 (Z_to_bv 64 (F + 32)) 516 = true ->
  RiscvSemantics.store_ok SEGS_A m5 (Z_to_bv 64 (F + 688)) 516 = true ->
  (forall o n, sp - 3072 <= o -> o + Z.of_nat n <= sp -> RiscvSemantics.store_ok SEGS_A m5 (Z_to_bv 64 o) n = true) ->
  exists regs7 m7,
    msteps SEGS_A (mkst regs5 (Z_to_bv 64 p5) m5 rom) (mkst regs7 (Z_to_bv 64 0x0a96c0) m7 rom)
    /\ bn_at SEGS_A m7 (F + 32) a2 /\ bn_at SEGS_A m7 (F + 688) b2 /\ ok (cells a2) /\ ok (cells b2) /\ zlen (cells a2) <= 126 /\ zlen (cells b2) <= 126
    /\ getr regs7 2%bv = Z_to_bv 64 sp1 /\ keeps CS3A regs5 regs7
    /\ unch m5 m7 [(F + 32, F + 548); (F + 688, F + 1204); (sp1 - 16, sp1)] /\ mem_grows m5 m7.
Proof.
  intros regs5 m5 p5 Hp5 D11 D10 D2 C24' C25' HA5 HB5 RT5 RO5 OBA5 OBB5 WoA5 WoB5 Wst5.
  pose proof (csp1_facts buf len sp FS bg0 bgl CE) as (Hs1 & [q1 Hq1] & _).
  pose proof CE as CE0. destruct CE as [Eb1 Eb2 Elen Ebg0 Ebgl Esp1 Esp2 [qs Hqs] Efs1 Efs2 [qf Hqf] Dbsp DspFS Dbh Dbfl Dbfr].
  unfold FS_LEN in *. clear Dbh Dbfl Dbfr Dbsp. hide DspFS.
  pose proof (u64_range f) as Hfr.
  assert (Elen2 : zlen ds = len) by (unfold zlen; lia).
  pose proof (cbd_facts ds len expo (bv_unsigned f) e DOK Elen2 Elen Hle ltac:(lia) He) as CF. cbn zeta in CF.
  change (assign_decimal ds) with a0 in CF. change (assign_u64 (bv_unsigned f)) with b0 in CF.
  change (if 0 <=? expo then mulpow10 expo a0 else a0) with a1 in CF. change (if 0 <=? expo then b0 else mulpow10 (- expo) b0) with b1 in CF.
  destruct CF as (_ & _ & (A1ok & A1n & A1len & A1ex) & (B1ok & B1n & B1len & B1ex) & A2ok' & B2ok').
  assert (SHBlen : 0 <= e -> zlen (cells (shl e b1)) <= zlen (cells b1) + 1) by (intros Hx; exact (proj2 (proj2 (proj2 (proj2 (shl_spec e b1 B1ok B1n Hx)))))).
  assert (SHAlen : 0 <= - e -> zlen (cells (shl (- e) a1)) <= zlen (cells a1) + 1) by (intros Hx; exact (proj2 (proj2 (proj2 (proj2 (shl_spec (- e) a1 A1ok A1n Hx)))))).
  assert (BR : exists regs6,
      msteps SEGS_A (mkst regs5 (Z_to_bv 64 p5) m5 rom) (mkst regs6 (Z_to_bv 64 0x0ab0fc) m5 rom)
      /\ getr regs6 10%bv = Z_to_bv 64 (if 0 <? e then F + 688 else F + 32)
      /\ getr regs6 11%bv = Z_to_bv 64 (if 0 <? e then e else - e)
      /\ getr regs6 2%bv = Z_to_bv 64 sp1 /\ getr regs6 1%bv = Z_to_bv 64 0x0a96c0
      /\ keeps CS' regs5 regs6).
    { destruct (Z.ltb_spec 0 e) as [Hx|Hx]; destruct Hp5 as [-> | ->].
      - zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (IMG, HIE - 2048); Some (1, 2047); Some (0, 18446744073709551615)]) (@nil kcell) (@nil kwin)) 10%nat [0x0ab0fc] (SCR [] [])
          constr:([(11%bv : reg, ZV 33); (10%bv : reg, ZV 34); (24%bv : reg, ZAdd (ZV 32) (ZL 32)); (25%bv : reg, ZAdd (ZV 32) (ZL 688))]) [F; e; w4]
          constr:([Some (IMG, HIE - 2048); Some (1, 2047); Some (0, 18446744073709551615)]) regs5 m5 rom 0x0a9690.
        zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs6.
        exists regs6. split; [exact ZM|]. split; [zx_regv ZR|]. split; [zx_regv ZR|].
        split; [etransitivity; [exact (reg_kept _ _ _ _ (2%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact D2]|]. split; [zx_regv ZR|].
        eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity.
      - zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (IMG, HIE - 2048); Some (1, 2047); Some (0, 18446744073709551615)]) (@nil kcell) (@nil kwin)) 10%nat [0x0ab0fc] (SCR [] [])
          constr:([(11%bv : reg, ZV 33); (10%bv : reg, ZV 34); (24%bv : reg, ZAdd (ZV 32) (ZL 32)); (25%bv : reg, ZAdd (ZV 32) (ZL 688))]) [F; e; w4]
          constr:([Some (IMG, HIE - 2048); Some (1, 2047); Some (0, 18446744073709551615)]) regs5 m5 rom 0x0a96b0.
        zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs6.
        exists regs6. split; [exact ZM|]. split; [zx_regv ZR|]. split; [zx_regv ZR|].
        split; [etransitivity; [exact (reg_kept _ _ _ _ (2%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact D2]|]. split; [zx_regv ZR|].
        eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity.
      - zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (IMG, HIE - 2048); Some (-2047, 0); Some (0, 18446744073709551615)]) (@nil kcell) (@nil kwin)) 10%nat [0x0ab0fc] (SCR [] [])
          constr:([(11%bv : reg, ZV 33); (10%bv : reg, ZV 34); (24%bv : reg, ZAdd (ZV 32) (ZL 32)); (25%bv : reg, ZAdd (ZV 32) (ZL 688))]) [F; e; w4]
          constr:([Some (IMG, HIE - 2048); Some (-2047, 0); Some (0, 18446744073709551615)]) regs5 m5 rom 0x0a9690.
        zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs6.
        exists regs6. split; [exact ZM|]. split; [zx_regv ZR|]. split; [zx_reg ZR (11%bv : reg) as H; rewrite H; f_equal; exact Hw4n|].
        split; [etransitivity; [exact (reg_kept _ _ _ _ (2%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact D2]|]. split; [zx_regv ZR|].
        eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity.
      - zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (IMG, HIE - 2048); Some (-2047, 0); Some (0, 18446744073709551615)]) (@nil kcell) (@nil kwin)) 10%nat [0x0ab0fc] (SCR [] [])
          constr:([(11%bv : reg, ZV 33); (10%bv : reg, ZV 34); (24%bv : reg, ZAdd (ZV 32) (ZL 32)); (25%bv : reg, ZAdd (ZV 32) (ZL 688))]) [F; e; w4]
          constr:([Some (IMG, HIE - 2048); Some (-2047, 0); Some (0, 18446744073709551615)]) regs5 m5 rom 0x0a96b0.
        zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs6.
        exists regs6. split; [exact ZM|]. split; [zx_regv ZR|]. split; [zx_reg ZR (11%bv : reg) as H; rewrite H; f_equal; exact Hw4n|].
        split; [etransitivity; [exact (reg_kept _ _ _ _ (2%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact D2]|]. split; [zx_regv ZR|].
        eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity. }
    destruct BR as (regs6 & M6 & F10 & F11 & F2 & F1 & K6).
    unfold a2, b2. destruct (Z.ltb_spec 0 e) as [Hx|Hx].
    - specialize (SHBlen ltac:(lia)).
      destruct (shl_A rom regs6 m5 (F + 688) e sp1 (Z_to_bv 64 0x0a96c0) b1 F10 F11 F2 F1 ltac:(vm_compute; reflexivity) ltac:(lia) HB5 B1ok ltac:(lia))
        as (regs7 & m7 & M7 & K7 & HB7 & U7 & G7).
      { pose proof (Z.div_le_upper_bound e 28 73). lia. } { lia. } { lia. } { lia. } { lia. } { lia. } { flia. }
      { exact (shcells_intro m5 RT5 RO5). } { exact OBB5. } { exact WoB5. } { apply Wst5; zwidth; lia. }
      eexists regs7, m7. split; [eapply msteps_trans; [exact M6 | exact M7]|].
      split; [eapply (bn_at_unch SEGS_A m5 m7); [exact U7 | lia | cbn; lia | intros rg Hrg; inr Hrg ltac:(slia) | exact HA5]|].
      split; [exact HB7|]. split; [exact A1ok|]. split; [exact B2ok'|]. split; [lia|]. split; [lia|].
      split; [kept K7 2 F2|].
      split; [eapply keeps_trans; [eapply keeps_sub_dec; [exact K6|]; vm_compute; reflexivity | eapply keeps_sub_dec; [exact K7|]; vm_compute; reflexivity]|].
      split; [|exact G7].
      eapply unch_widen; [exact U7|]. intros rg Hrg; cbn [fst snd]; inr Hrg ltac:(first [eexists; split; [right; left; reflexivity | cbn; lia] | eexists; split; [do 2 right; left; reflexivity | cbn; lia]]).
    - specialize (SHAlen ltac:(lia)).
      destruct (shl_A rom regs6 m5 (F + 32) (- e) sp1 (Z_to_bv 64 0x0a96c0) a1 F10 F11 F2 F1 ltac:(vm_compute; reflexivity) ltac:(lia) HA5 A1ok ltac:(lia))
        as (regs7 & m7 & M7 & K7 & HA7 & U7 & G7).
      { pose proof (Z.div_le_upper_bound (- e) 28 73). lia. } { lia. } { lia. } { lia. } { lia. } { lia. } { flia. }
      { exact (shcells_intro m5 RT5 RO5). } { exact OBA5. } { exact WoA5. } { apply Wst5; zwidth; lia. }
      eexists regs7, m7. split; [eapply msteps_trans; [exact M6 | exact M7]|].
      split; [exact HA7|].
      split; [eapply (bn_at_unch SEGS_A m5 m7); [exact U7 | lia | cbn; lia | intros rg Hrg; inr Hrg ltac:(slia) | exact HB5]|].
      split; [exact A2ok'|]. split; [exact B1ok|]. split; [lia|]. split; [lia|].
      split; [kept K7 2 F2|].
      split; [eapply keeps_trans; [eapply keeps_sub_dec; [exact K6|]; vm_compute; reflexivity | eapply keeps_sub_dec; [exact K7|]; vm_compute; reflexivity]|].
      split; [|exact G7].
      eapply unch_widen; [exact U7|]. intros rg Hrg; cbn [fst snd]; inr Hrg ltac:(first [eexists; split; [left; reflexivity | cbn; lia] | eexists; split; [do 2 right; left; reflexivity | cbn; lia]]).
Qed.
(* [comment removed for export] *)
#[using="buf len bg0 bgl g0 w4 CE Hds Hp HF HgF Hg0 Hw4 Hret"] Lemma cbd_ph5 : forall regs regs7 m7,
  getr regs 1%bv = ret ->
  getr regs7 24%bv = Z_to_bv 64 (F + 32) -> getr regs7 25%bv = Z_to_bv 64 (F + 688) -> getr regs7 2%bv = Z_to_bv 64 sp1 ->
  getr regs7 8%bv = Z_to_bv 64 sp -> getr regs7 18%bv = Z_to_bv 64 F -> getr regs7 23%bv = Z_to_bv 64 F ->
  getr regs7 22%bv = Z_to_bv 64 (g + 86) -> getr regs7 27%bv = Z_to_bv 64 (g + 4) ->
  bn_at SEGS_A m7 (F + 32) a2 -> bn_at SEGS_A m7 (F + 688) b2 ->
  ok (cells a2) -> ok (cells b2) -> zlen (cells a2) <= 126 -> zlen (cells b2) <= 126 ->
  rt_ok m7 -> ro_ok SEGS_A RO_A m7 -> objsh m7 (F + 32) -> objsh m7 (F + 688) ->
  SAV sp m7 (savs regs ret) ->
  mem_u64 m7 (F + 2040) (FS + 35840 + p) -> mem_def m7 (FS + 35840 + p) 1 -> mem_def m7 g 256 -> mem_def m7 F 2048 ->
  mem_def m7 (sp - 3072) 3072 ->
  exists regs' m',
    msteps SEGS_A (mkst regs7 (Z_to_bv 64 0x0a96c0) m7 rom) (mkst regs' ret m' rom)
    /\ getr regs' 2%bv = Z_to_bv 64 sp /\ rest13 regs' (savs regs ret) /\ keeps [3; 4] regs7 regs'
    /\ getr regs' 10%bv = Z_to_bv 64 (compare a2 b2)
    /\ mem_byte m' (FS + 35840 + p) 0
    /\ unch m7 m' [(sp1 - 16, sp1); (F, F + 8); (FS + 35840 + p, FS + 35840 + p + 1); (g, g + 256)] /\ mem_grows m7 m'.
Proof.
  intros regs regs7 m7 R1 E24 E25 E2 E8 E18 E23 E22 E27 HA7 HB7 A2ok B2ok A2len B2len RT7 RO7 OBA7 OBB7 SV7 Q2040 Dq WG WF Wsp.
  pose proof (csp1_facts buf len sp FS bg0 bgl CE) as (Hs1 & [q1 Hq1] & _).
  pose proof CE as CE0. destruct CE as [Eb1 Eb2 Elen Ebg0 Ebgl Esp1 Esp2 [qs Hqs] Efs1 Efs2 [qf Hqf] Dbsp DspFS Dbh Dbfl Dbfr].
  unfold FS_LEN in *. clear Dbh Dbfl Dbfr Dbsp. hide DspFS.
  pose proof (u64_range ret) as Hrr.
  (* [comment removed for export] *)
  zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (IMG, HIE - 2048)]) (@nil kcell) (@nil kwin)) 10%nat [0x0ab28c] (SCR [] [])
    constr:([(24%bv : reg, ZAdd (ZV 32) (ZL 32)); (25%bv : reg, ZAdd (ZV 32) (ZL 688))]) [F] constr:([Some (IMG, HIE - 2048)]) regs7 m7 rom 0x0a96c0.
  zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs8.
  assert (K8 : keeps CS' regs7 regs8) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
  destruct (cmp_A rom regs8 m7 (F + 32) (F + 688) sp1 (Z_to_bv 64 0x0a96cc) a2 b2) as (regs9 & m9 & M9 & K9 & R10' & U9 & G9); try (zx_regv ZR).
  { vm_compute. reflexivity. } { exact HA7. } { exact HB7. } { exact A2ok. } { exact B2ok. } { exact A2len. } { exact B2len. }
  { lia. } { lia. } { lia. } { lia. } { lia. } { lia. } { lia. } { lia. } { flia. } { flia. }
  { exact (shcells_intro m7 RT7 RO7). } { exact OBA7. } { exact OBB7. }
  { eapply store_ok_of_def_in; [exact Wsp|]. zwidth. lia. }
  assert (M79 : msteps SEGS_A (mkst regs7 (Z_to_bv 64 0x0a96c0) m7 rom) (mkst regs9 (Z_to_bv 64 0x0a96cc) m9 rom)) by (eapply msteps_trans; [exact ZM | exact M9]).
  assert (K79 : keeps CS' regs7 regs9) by (eapply keeps_trans; [exact K8 | eapply keeps_sub_dec; [exact K9|]; vm_compute; reflexivity]).
  assert (I2 : getr regs9 2%bv = Z_to_bv 64 sp1).
  { etransitivity; [exact (K9 2 ltac:(in_list))|]. etransitivity; [exact (reg_kept _ _ _ _ (2%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact E2]. }
  clear ZE ZR ZF ZM K8 K9 M9.
  assert (I22 : getr regs9 22%bv = Z_to_bv 64 (g + 86)) by (kept K79 22 E22).
  assert (I27 : getr regs9 27%bv = Z_to_bv 64 (g + 4)) by (kept K79 27 E27).
  assert (I18 : getr regs9 18%bv = Z_to_bv 64 F) by (kept K79 18 E18).
  assert (I23 : getr regs9 23%bv = Z_to_bv 64 F) by (kept K79 23 E23).
  assert (I8 : getr regs9 8%bv = Z_to_bv 64 sp) by (kept K79 8 E8).
  assert (HR9 : forall r, In r [(sp1 - 16, sp1)] -> highr r) by (intros r Hr; unfold highr; inr Hr ltac:(slia)).
  assert (RT9 : rt_ok m9) by (eapply rt_ok_unch; [exact U9 | exact HR9 | exact RT7]).
  assert (RO9 : ro_ok SEGS_A RO_A m9) by (eapply ro_ok_unchA; [exact U9 | exact HR9 | exact RO7]).
  (* [comment removed for export] *)
  zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (SHA, KHI - 512)]) (@nil kcell) (@nil kwin)) 10%nat [0x7844c] (SCR [] [])
    constr:([(22%bv : reg, ZAdd (ZV 32) (ZL 86))]) [g] constr:([Some (SHA, KHI - 512)]) regs9 m9 rom 0x0a96cc.
  zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs10.
  assert (J19 : getr regs10 19%bv = Z_to_bv 64 (compare a2 b2)) by (zx_regv ZR; rewrite ?Z_to_bv_bv_unsigned; exact R10').
  destruct (setsh_A rom true regs10 m9 (g + 86) 65 (Z_to_bv 64 0x0a96dc)) as (regs11 & M11 & K11); try (zx_regv ZR).
  { vm_compute. reflexivity. } { lia. } { lia. } { lia. }
  { eapply store_ok_of_def_in; [eapply mem_def_grows; [exact G9 | exact WG]|]. zwidth. change (Z.of_nat (Z.to_nat 65)) with 65. lia. }
  { eapply mscells_unch; [exact U9 | exact HR9 | exact (mscells_intro m7 RO7)]. }
  cbn [negb] in M11. set (m11 := wbytes m9 _ _) in M11.
  assert (U911 : unch m9 m11 [(g + 86, g + 151)]).
  { unfold m11. eapply (unch_store_bs m9 (g + 86)); rewrite ?repeat_length; [lia | zwidth; lia | in_list | lia | lia]. }
  assert (G911 : mem_grows m9 m11) by (unfold m11; apply grows_store).
  assert (M911 : msteps SEGS_A (mkst regs9 (Z_to_bv 64 0x0a96cc) m9 rom) (mkst regs11 (Z_to_bv 64 0x0a96dc) m11 rom)) by (eapply msteps_trans; [exact ZM | exact M11]).
  assert (K911 : keeps [2; 3; 4; 8; 9; 18; 20; 21; 23; 24; 25; 26; 27] regs9 regs11).
  { eapply keeps_trans; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | eapply keeps_sub_dec; [exact K11|]; vm_compute; reflexivity]. }
  assert (J19' : getr regs11 19%bv = Z_to_bv 64 (compare a2 b2)) by (kept K11 19 J19).
  clear ZE ZR ZF ZM M11 K11.
  (* [comment removed for export] *)
  assert (J27 : getr regs11 27%bv = Z_to_bv 64 (g + 4)) by (kept K911 27 I27).
  zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (SHA, KHI - 512)]) (@nil kcell) (@nil kwin)) 10%nat [0x7844c] (SCR [] [])
    constr:([(27%bv : reg, ZAdd (ZV 32) (ZL 4))]) [g] constr:([Some (SHA, KHI - 512)]) regs11 m11 rom 0x0a96dc.
  zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs12.
  assert (HR11 : forall r, In r [(g + 86, g + 151)] -> highr r) by (intros r Hr; unfold highr; inr Hr ltac:(slia)).
  destruct (setsh_A rom true regs12 m11 (g + 4) 65 (Z_to_bv 64 0x0a96e8)) as (regs13 & M13 & K13); try (zx_regv ZR).
  { vm_compute. reflexivity. } { lia. } { lia. } { lia. }
  { eapply store_ok_of_def_in; [eapply mem_def_grows; [eapply mem_grows_trans; [exact G9 | exact G911] | exact WG]|]. zwidth. change (Z.of_nat (Z.to_nat 65)) with 65. lia. }
  { eapply mscells_unch; [exact U911 | exact HR11 |]. eapply mscells_unch; [exact U9 | exact HR9 | exact (mscells_intro m7 RO7)]. }
  cbn [negb] in M13. set (m13 := wbytes m11 _ _) in M13.
  assert (U1113 : unch m11 m13 [(g + 4, g + 69)]).
  { unfold m13. eapply (unch_store_bs m11 (g + 4)); rewrite ?repeat_length; [lia | zwidth; lia | in_list | lia | lia]. }
  assert (G1113 : mem_grows m11 m13) by (unfold m13; apply grows_store).
  assert (M1113 : msteps SEGS_A (mkst regs11 (Z_to_bv 64 0x0a96dc) m11 rom) (mkst regs13 (Z_to_bv 64 0x0a96e8) m13 rom)) by (eapply msteps_trans; [exact ZM | exact M13]).
  assert (K1113 : keeps [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26] regs11 regs13).
  { eapply keeps_trans; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | eapply keeps_sub_dec; [exact K13|]; vm_compute; reflexivity]. }
  clear ZE ZR ZF ZM M13 K13.
  (* [comment removed for export] *)
  assert (U713 : unch m7 m13 [(sp1 - 16, sp1); (F, F + 8); (FS + 35840 + p, FS + 35840 + p + 1); (g, g + 256)]).
  { eapply unch_trans; [eapply unch_trans; [uwiden U9 | uwiden U911] | uwiden U1113]. }
  assert (G713 : mem_grows m7 m13) by (eapply mem_grows_trans; [eapply mem_grows_trans; [exact G9 | exact G911] | exact G1113]).
  assert (HR713 : forall r, In r [(sp1 - 16, sp1); (F, F + 8); (FS + 35840 + p, FS + 35840 + p + 1); (g, g + 256)] -> highr r) by (intros r Hr; unfold highr; inr Hr ltac:(slia)).
  (* [comment removed for export] *)
  assert (J18 : getr regs11 18%bv = Z_to_bv 64 F) by (kept K911 18 I18).
  assert (J23 : getr regs11 23%bv = Z_to_bv 64 F) by (kept K911 23 I23).
  assert (J8 : getr regs11 8%bv = Z_to_bv 64 sp) by (kept K911 8 I8).
  assert (J2 : getr regs11 2%bv = Z_to_bv 64 sp1) by (kept K911 2 I2).
  assert (L18 : getr regs13 18%bv = Z_to_bv 64 F) by (kept K1113 18 J18).
  assert (L23 : getr regs13 23%bv = Z_to_bv 64 F) by (kept K1113 23 J23).
  assert (L8 : getr regs13 8%bv = Z_to_bv 64 sp) by (kept K1113 8 J8).
  assert (L2 : getr regs13 2%bv = Z_to_bv 64 sp1) by (kept K1113 2 J2).
  assert (L19 : getr regs13 19%bv = Z_to_bv 64 (compare a2 b2)) by (kept K1113 19 J19').
  assert (WF13 : mem_def m13 F 2048) by (eapply mem_def_grows; [exact G713 | exact WF]).
  zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (IMG, HIE - 2048)]) (@nil kcell) [KW (ZV 32) 0 8]) 10%nat [0x5b8ac] (SCR [] [])
    constr:([(18%bv : reg, ZV 32); (23%bv : reg, ZV 32)]) [F] constr:([Some (IMG, HIE - 2048)]) regs13 m13 rom 0x0a96e8.
  zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(kwd WF13; exact I) ltac:(exact I). zx_name regs14.
  rename ZM into M1314. set (m14 := wbytes m13 _ _) in M1314.
  assert (K1314 : keeps [2; 3; 4; 8; 9; 19; 20; 21; 22; 24; 25; 26; 27] regs13 regs14) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
  assert (U1314 : unch m13 m14 [(F, F + 8)]) by (subst m14; clear - Efs1 Efs2 HF Hp; unchx).
  assert (G1314 : mem_grows m13 m14) by (subst m14; growsx).
  assert (U714 : unch m7 m14 [(sp1 - 16, sp1); (F, F + 8); (FS + 35840 + p, FS + 35840 + p + 1); (g, g + 256)]).
  { eapply unch_trans; [exact U713 | uwiden U1314]. }
  assert (G714 : mem_grows m7 m14) by (eapply mem_grows_trans; [exact G713 | exact G1314]).
  assert (RT14 : rt_ok m14) by (eapply rt_ok_unch; [exact U714 | exact HR713 | exact RT7]).
  assert (RO14 : ro_ok SEGS_A RO_A m14) by (eapply ro_ok_unchA; [exact U714 | exact HR713 | exact RO7]).
  destruct (free5_A fx regs14 m14 rom (Z_to_bv 64 0x0a9704) sp1 F (FS + 35840 + p)) as (regs15 & m15 & M15 & K15 & Hflag & _ & FR15).
  all: unfold app_mem, KHI_A, HIEND_A, IMGHI_A, LOSH_A, FREE5_FR, sh, SH_A.   (* [comment removed for export] *)
  { zx_regv ZR. } { vm_compute. reflexivity. } { zx_regv ZR; exact L2. }
  { rewrite Hq1. lia. } { lia. } { lia. }
  { eapply mem_def_grows; [exact G714|]. eapply mem_def_sub; [exact Wsp | lia | lia]. }
  { zx_regv ZR. } { rewrite HgF. lia. } { lia. } { lia. } { lia. }
  { eapply mem_u64_unch; [exact U714 | lia | lia | intros r Hr; inr Hr ltac:(slia) | exact Q2040]. }
  { lia. } { lia. } { lia. } { eapply mem_def_grows; [exact G714 | exact Dq]. }
  { replace (2147450880 + F / 8) with g by lia. eapply mem_def_grows; [exact G714 | exact WG]. }
  { flia. } { lia. } { flia. } { lia. } { lia. }
  { exact RT14. } { exact RO14. }
  pose proof (unch_of_frame _ _ _ FR15) as U1415. pose proof (grows_of_frame _ _ _ FR15) as G1415.
  unfold sh, SH_A, FREE5_FR in U1415. replace (2147450880 + F / 8) with g in U1415 by lia.
  apply keeps_of_cs in K15.
  assert (U715 : unch m7 m15 [(sp1 - 16, sp1); (F, F + 8); (FS + 35840 + p, FS + 35840 + p + 1); (g, g + 256)]).
  { eapply unch_trans; [exact U714 | uwiden U1415]. }
  (* [comment removed for export] *)
  assert (SV15 : SAV sp m15 (savs regs ret)).
  { eapply SAV_unchC; [exact U715 | intros r Hr; cbn [fst snd]; inr Hr ltac:(slia) | lia | lia | exact SV7]. }
  assert (N8 : getr regs14 8%bv = Z_to_bv 64 sp) by (kept K1314 8 L8).
  assert (N19 : getr regs14 19%bv = Z_to_bv 64 (compare a2 b2)) by (kept K1314 19 L19).
  assert (B8 : getr regs15 8%bv = Z_to_bv 64 sp) by (kept K15 8 N8).
  assert (B19 : getr regs15 19%bv = Z_to_bv 64 (compare a2 b2)) by (kept K15 19 N19).
  clear ZE ZR ZF.
  pose proof (u64_range (getr regs 8%bv)) as V1. pose proof (u64_range (getr regs 9%bv)) as V2. pose proof (u64_range (getr regs 18%bv)) as V3.
  pose proof (u64_range (getr regs 19%bv)) as V4. pose proof (u64_range (getr regs 20%bv)) as V5. pose proof (u64_range (getr regs 21%bv)) as V6.
  pose proof (u64_range (getr regs 22%bv)) as V7. pose proof (u64_range (getr regs 23%bv)) as V8. pose proof (u64_range (getr regs 24%bv)) as V9.
  pose proof (u64_range (getr regs 25%bv)) as V10. pose proof (u64_range (getr regs 26%bv)) as V11. pose proof (u64_range (getr regs 27%bv)) as V12.
  pose proof (SV15 0%nat ltac:(lia)) as W0. pose proof (SV15 1%nat ltac:(lia)) as W1. pose proof (SV15 2%nat ltac:(lia)) as W2.
  pose proof (SV15 3%nat ltac:(lia)) as W3. pose proof (SV15 4%nat ltac:(lia)) as W4. pose proof (SV15 5%nat ltac:(lia)) as W5.
  pose proof (SV15 6%nat ltac:(lia)) as W6. pose proof (SV15 7%nat ltac:(lia)) as W7. pose proof (SV15 8%nat ltac:(lia)) as W8.
  pose proof (SV15 9%nat ltac:(lia)) as W9. pose proof (SV15 10%nat ltac:(lia)) as W10. pose proof (SV15 11%nat ltac:(lia)) as W11.
  pose proof (SV15 12%nat ltac:(lia)) as W12.
  unfold savs in W0, W1, W2, W3, W4, W5, W6, W7, W8, W9, W10, W11, W12.
  cbn [nth Z.of_nat Z.mul Pos.mul Pos.of_succ_nat Pos.succ] in W0, W1, W2, W3, W4, W5, W6, W7, W8, W9, W10, W11, W12.
  pose proof (compare_range a2 b2) as Hcr.
  zx_run SEGS_A constr:(CTX (vi_regs ++ ep_uvi) ep_kn (@nil kwin)) 30%nat [0x0a9754] (SCR [] []) constr:([(8%bv : reg, ZV 32); (19%bv : reg, ZV 46)])
    [sp; bv_unsigned ret; bv_unsigned (getr regs 8%bv); bv_unsigned (getr regs 9%bv); bv_unsigned (getr regs 18%bv); bv_unsigned (getr regs 19%bv);
     bv_unsigned (getr regs 20%bv); bv_unsigned (getr regs 21%bv); bv_unsigned (getr regs 22%bv); bv_unsigned (getr regs 23%bv);
     bv_unsigned (getr regs 24%bv); bv_unsigned (getr regs 25%bv); bv_unsigned (getr regs 26%bv); bv_unsigned (getr regs 27%bv);
     compare a2 b2]
    constr:(ep_uvi) regs15 m15 rom 0x0a9704.
  zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia)
    ltac:(kc1 W0; kc1 W1; kc1 W2; kc1 W3; kc1 W4; kc1 W5; kc1 W6; kc1 W7; kc1 W8; kc1 W9; kc1 W10; kc1 W11; kc1 W12; exact I)
    ltac:(exact I) ltac:(exact I). zx_name regs16.
  assert (R1' : getr regs16 1%bv = ret) by (zx_regv ZR).
  eexists regs16, m15. split.
  { eapply msteps_trans; [exact M79|]. eapply msteps_trans; [exact M911|]. eapply msteps_trans; [exact M1113|].
    eapply msteps_trans; [exact M1314|]. eapply msteps_trans; [exact M15|]. eapply msteps_trans; [exact ZM|]. zx_ret SEGS_A; [exact R1' | exact Hret]. }
  split; [zx_regv ZR|].
  split; [unfold rest13, savs; cbn [nth]; repeat split; zx_regv ZR|].
  split.
  { eapply keeps_trans; [eapply keeps_sub_dec; [exact K79|]; vm_compute; reflexivity|].
    eapply keeps_trans; [eapply keeps_sub_dec; [exact K911|]; vm_compute; reflexivity|].
    eapply keeps_trans; [eapply keeps_sub_dec; [exact K1113|]; vm_compute; reflexivity|].
    eapply keeps_trans; [eapply keeps_sub_dec; [exact K1314|]; vm_compute; reflexivity|].
    eapply keeps_trans; [eapply keeps_sub_dec; [exact K15|]; vm_compute; reflexivity|].
    eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity. }
  split; [zx_regv ZR|].
  split; [exact Hflag|].
  split; [exact U715 | eapply mem_grows_trans; [exact G714 | exact G1415]].
Qed.
(* [comment removed for export] *)
#[using="CE Hds DOK Hp HF HgF Hg0 Hle He Hw4 Hw4e Hw4n Hret ads_A_h"] Lemma cbd_core_A : forall regs regsP mP,
  getr regsP 1%bv = Z_to_bv 64 0x0a966c -> getr regsP 10%bv = Z_to_bv 64 (F + 32) -> getr regsP 11%bv = Z_to_bv 64 buf ->
  getr regsP 12%bv = Z_to_bv 64 len -> getr regsP 2%bv = Z_to_bv 64 sp1 -> getr regsP 4%bv = Z_to_bv 64 TP_A ->
  getr regsP 9%bv = Z_to_bv 64 sp1 -> getr regsP 8%bv = Z_to_bv 64 sp -> getr regsP 18%bv = Z_to_bv 64 F ->
  getr regsP 20%bv = Z_to_bv 64 expo -> getr regsP 21%bv = Z_to_bv 64 g -> getr regsP 22%bv = Z_to_bv 64 (g + 86) ->
  getr regsP 23%bv = Z_to_bv 64 F -> getr regsP 24%bv = Z_to_bv 64 (F + 32) -> getr regsP 25%bv = Z_to_bv 64 (F + 688) ->
  getr regsP 26%bv = Z_to_bv 64 buf -> getr regsP 27%bv = Z_to_bv 64 (g + 4) ->
  cellN SEGS_A mP (sp1 + 16) 8 (bv_unsigned f) -> cellN SEGS_A mP (sp1 + 24) 8 w4 ->
  SAV sp mP (savs regs ret) -> objsh mP (F + 32) -> objsh mP (F + 688) ->
  rt_ok mP -> ro_ok SEGS_A RO_A mP -> gsh_ok mP -> digs buf ds mP -> dsh bg0 bgl mP ->
  malloc_ctx_ok (sp - 3072) sp FS mP -> rd_u64 mP FSTLS_A FS -> mem_def mP (sp - 3072) 3072 ->
  mem_def mP FS FS_LEN -> mem_def mP (sh FS + FS_SHLO) (FS_SHHI - FS_SHLO) -> mem_u64 mP (FS + 88) 20 -> mem_byte mP (FS + 96) 0 ->
  (forall j, 0 <= j < 512 -> j <> p -> mem_byte mP (fs_flag FS 5 j) 0) -> mem_byte mP (FS + 35840 + p) 1 ->
  mem_u64 mP (F + 2040) (FS + 35840 + p) ->
  getr regs 1%bv = ret ->
  exists regs' m',
    msteps SEGS_A (mkst regsP (Z_to_bv 64 0x0a9c3c) mP rom) (mkst regs' ret m' rom)
    /\ getr regs' 2%bv = Z_to_bv 64 sp /\ rest13 regs' (savs regs ret) /\ keeps [3; 4] regsP regs'
    /\ getr regs' 10%bv = Z_to_bv 64 (cbd ds expo (bv_unsigned f) e)
    /\ (forall j, 0 <= j < 512 -> mem_byte m' (fs_flag FS 5 j) 0)
    /\ unch mP m' CW /\ mem_grows mP m'.
Proof.
  intros regs regsP mP P1 P10 P11 P12 P2 P4 P9 P8 P18 P20 P21 P22 P23 P24 P25 P26 P27 S16 S24 SV OBA OBB RT RO GSH DG DSH MCX TLS Dsp
    DFS DSHD L88 B96 FL0 FL1 Q2040 R1.
  destruct (cbd_ph12 regs regsP mP P1 P10 P11 P12 P2 P4 P9 P8 P18 P20 P21 P22 P23 P24 P25 P26 P27 S16 S24 SV OBA OBB RT RO GSH DG DSH MCX TLS Dsp
              DFS DSHD L88 B96 FL0 FL1 Q2040 R1)
    as (regsC & mC & pA & FA & gA & MPC & HpA & HpAne & HFA & HgA & KPC & C2 & HA3 & HB & S24C & RTC & ROC & GSHC & OBAC & OBBC & FLC & UPC & GPC).
  clear S16 S24 OBA OBB RT RO GSH DG DSH MCX TLS L88 B96 FL0 FL1.
  pose proof (csp1_facts buf len sp FS bg0 bgl CE) as (Hs1 & [q1 Hq1] & _).
  pose proof CE as CE0. destruct CE as [Eb1 Eb2 Elen Ebg0 Ebgl Esp1 Esp2 [qs Hqs] Efs1 Efs2 [qf Hqf] Dbsp DspFS Dbh Dbfl Dbfr].
  unfold FS_LEN in *. clear Dbh Dbfl Dbfr Dbsp Ebg0 Ebgl. hide DspFS.
  assert (HAPART : FA + 2048 <= F \/ F + 2048 <= FA) by lia. hide HAPART.
  (* [comment removed for export] *)
  assert (WstC : forall o n, sp - 3072 <= o -> o + Z.of_nat n <= sp -> RiscvSemantics.store_ok SEGS_A mC (Z_to_bv 64 o) n = true).
  { intros o n Ho1 Ho2. eapply store_ok_of_def_in; [eapply mem_def_grows; [exact GPC | exact Dsp]|]. lia. }
  assert (WoAC : RiscvSemantics.store_ok SEGS_A mC (Z_to_bv 64 (F + 32)) 516 = true).
  { eapply store_ok_of_def_in; [eapply mem_def_grows; [exact GPC | exact DFS]|]. zwidth. lia. }
  assert (WoBC : RiscvSemantics.store_ok SEGS_A mC (Z_to_bv 64 (F + 688)) 516 = true).
  { eapply store_ok_of_def_in; [eapply mem_def_grows; [exact GPC | exact DFS]|]. zwidth. lia. }
  (* [comment removed for export] *)
  destruct (cbd_ph3 regsC mC C2 ltac:(kept KPC 9 P9) ltac:(kept KPC 20 P20) ltac:(kept KPC 24 P24) ltac:(kept KPC 25 P25) HA3 HB S24C RTC ROC GSHC OBAC OBBC WoAC WoBC WstC)
    as (regs5 & m5 & p5 & Hp5 & M35 & HA5 & HB5 & D11 & D10 & D2 & K35 & U35 & G35).
  assert (HR35 : forall r, In r [(F + 32, F + 548); (F + 688, F + 1204); (sp1 - 48, sp1)] -> highr r) by (intros r Hr; unfold highr; inr Hr ltac:(slia)).
  assert (RT5 : rt_ok m5) by (eapply rt_ok_unch; [exact U35 | exact HR35 | exact RTC]).
  assert (RO5 : ro_ok SEGS_A RO_A m5) by (eapply ro_ok_unchA; [exact U35 | exact HR35 | exact ROC]).
  assert (OBA5 : objsh m5 (F + 32)) by (eapply (objsh_unch2 mC m5); [exact U35 | intros r Hr; inr Hr ltac:(slia) | lia | lia | exact OBAC]).
  assert (OBB5 : objsh m5 (F + 688)) by (eapply (objsh_unch2 mC m5); [exact U35 | intros r Hr; inr Hr ltac:(slia) | lia | lia | exact OBBC]).
  assert (KP5 : keeps CS3A regsP regs5) by (eapply keeps_trans; [exact KPC | exact K35]).
  (* [comment removed for export] *)
  destruct (cbd_ph4 regs5 m5 p5 Hp5 D11 D10 D2 ltac:(kept KP5 24 P24) ltac:(kept KP5 25 P25) HA5 HB5 RT5 RO5 OBA5 OBB5)
    as (regs7 & m7 & M57 & HA7 & HB7 & A2ok & B2ok & A2len & B2len & F2 & K57 & U57 & G57).
  { eapply store_ok_grows; [exact G35 | exact WoAC]. } { eapply store_ok_grows; [exact G35 | exact WoBC]. }
  { intros o n Ho1 Ho2. eapply store_ok_grows; [exact G35|]. apply WstC; lia. }
  assert (HR57 : forall r, In r [(F + 32, F + 548); (F + 688, F + 1204); (sp1 - 16, sp1)] -> highr r) by (intros r Hr; unfold highr; inr Hr ltac:(slia)).
  assert (RT7 : rt_ok m7) by (eapply rt_ok_unch; [exact U57 | exact HR57 | exact RT5]).
  assert (RO7 : ro_ok SEGS_A RO_A m7) by (eapply ro_ok_unchA; [exact U57 | exact HR57 | exact RO5]).
  assert (OBA7 : objsh m7 (F + 32)) by (eapply (objsh_unch2 m5 m7); [exact U57 | intros r Hr; inr Hr ltac:(slia) | lia | lia | exact OBA5]).
  assert (OBB7 : objsh m7 (F + 688)) by (eapply (objsh_unch2 m5 m7); [exact U57 | intros r Hr; inr Hr ltac:(slia) | lia | lia | exact OBB5]).
  assert (KP7 : keeps CS3A regsP regs7) by (eapply keeps_trans; [exact KP5 | exact K57]).
  assert (GP7 : mem_grows mP m7) by (eapply mem_grows_trans; [exact GPC|]; eapply mem_grows_trans; [exact G35 | exact G57]).
  (* [comment removed for export] *)
  assert (UP7 : unch mP m7 [(sp1 - 656, sp1); (F + 32, F + 548); (F + 688, F + 1204); (FS + 40, FS + 48); (FS + 35840 + pA, FS + 35840 + pA + 1); (FA, FA + 2048); (gA, gA + 256)]).
  { eapply unch_trans; [exact UPC|]. eapply unch_trans; [uwiden U35 | uwiden U57]. }
  assert (SV7 : SAV sp m7 (savs regs ret)).
  { eapply SAV_unchC; [exact UP7 | intros r Hr; cbn [fst snd]; inr Hr ltac:(slia) | lia | lia | exact SV]. }
  assert (Q7 : mem_u64 m7 (F + 2040) (FS + 35840 + p)).
  { eapply mem_u64_unch; [exact UP7 | lia | lia | intros r Hr; inr Hr ltac:(slia) | exact Q2040]. }
  (* [comment removed for export] *)
  destruct (cbd_ph5 regs regs7 m7 R1 ltac:(kept KP7 24 P24) ltac:(kept KP7 25 P25) F2 ltac:(kept KP7 8 P8) ltac:(kept KP7 18 P18) ltac:(kept KP7 23 P23)
              ltac:(kept KP7 22 P22) ltac:(kept KP7 27 P27) HA7 HB7 A2ok B2ok A2len B2len RT7 RO7 OBA7 OBB7 SV7 Q7)
    as (regs9 & m9 & M79 & X2 & X13 & K79 & X10 & Hflag & U79 & G79).
  { eapply mem_def_grows; [exact GP7|]. eapply mem_def_sub; [exact DFS | lia | lia]. }
  { eapply mem_def_grows; [exact GP7|]. eapply mem_def_sub; [exact DSHD | unfold sh, SH_A, FS_SHLO, FS_FRAMES; lia | unfold sh, SH_A, FS_SHLO, FS_SHHI, FS_FRAMES, FS_LEN; lia]. }
  { eapply mem_def_grows; [exact GP7|]. eapply mem_def_sub; [exact DFS | lia | lia]. }
  { eapply mem_def_grows; [exact GP7 | exact Dsp]. }
  eexists regs9, m9.
  split; [eapply msteps_trans; [exact MPC|]; eapply msteps_trans; [exact M35|]; eapply msteps_trans; [exact M57 | exact M79]|].
  split; [exact X2|]. split; [exact X13|].
  split; [eapply keeps_trans; [eapply keeps_sub_dec; [exact KP7|]; vm_compute; reflexivity | exact K79]|].
  split; [exact X10|].
  split.
  { intros j Hj. rewrite fs_flag5. destruct (Z.eq_dec j p) as [->|Hne]; [exact Hflag|].
    pose proof (FLC j Hj) as X. unfold fl1 in X. rewrite fs_flag5 in X. destruct (Z.eqb_spec j p); [lia|].
    eapply mem_byte_unch; [exact U79 | lia | intros r Hr; inr Hr ltac:(slia) |].
    eapply mem_byte_unch; [exact U57 | lia | intros r Hr; inr Hr ltac:(slia) |].
    eapply mem_byte_unch; [exact U35 | lia | intros r Hr; inr Hr ltac:(slia) | exact X]. }
  split; [|eapply mem_grows_trans; [exact GP7 | exact G79]].
  unfold CW. eapply unch_trans; [uwiden UP7 | uwiden U79].
Qed.
End S.
