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
  BnModel BnMath BnMem BnDefs LibIface BnCbdLib.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIfaceA LibIfaceB AsRtLib AsRtLibB AsZX AsZXTac AsZXDefs BnA_lib BnA_frame BnB_lib AsMallocB BnB_ads1 BnB_ads6 BnB_cbd1.
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
Variables (buf len sp FS bg0 bgl : Z) (ds : list Z).
Hypothesis CE : cbdE buf len sp FS bg0 bgl.
Hypothesis Hds : length ds = Z.to_nat len.

#[local] Abbreviation sp1 := (csp1 sp).


Ltac cgeom CE :=
  destruct CE as [Eb1 Eb2 Elen Ebg0 Ebgl Esp1 Esp2 [qs Hqs] Efs1 Efs2 [qf Hqf] Dbsp DspFS Dbh Dbfl Dbfr];
  unfold FS_LEN in *; hide Dbh; hide Dbfl; hide Dbfr; hide DspFS; hide Dbsp.

(* [comment removed for export] *)
Abbreviation b0b_pins := [(2%bv : reg, ZV 32); (9%bv : reg, ZV 32); (10%bv : reg, ZV 33); (11%bv : reg, ZV 34); (12%bv : reg, ZV 35); (13%bv : reg, ZV 36); (14%bv : reg, ZV 37)].
Abbreviation b0b_uvi := [Some (KHI + 2048, HIE - 160); Some (IMG, HIE - 1); Some (1, 780); Some (0, 18446744073709551615); Some (0, 18446744073709551615); Some (0, 18446744073709551615)].

Ltac dl H := unfold hide in H; cbn [fst snd]; lia.
Ltac pl := cbn [fst snd]; lia.
Ltac inr H tac := cbn [In] in H; repeat (destruct H as [<-|H]; [tac|]); destruct H.
#[local] Ltac inr H tac ::= lf_once ltac:(inr0 H tac).
Ltac inr6 H t1 t2 t3 t4 t5 t6 := cbn [In] in H; destruct H as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; [t1|t2|t3|t4|t5|t6].
Ltac inr3 H t1 t2 t3 := cbn [In] in H; destruct H as [<-|[<-|[<-|[]]]]; [t1|t2|t3].
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

(* [comment removed for export] *)
#[using="CE Hds"] Lemma cbd_pro2 : forall regs regs2 m m2 (ret f : word) (expo w4 p F g : Z),
  0 <= p < 512 -> F = FS + 5279744 + p * 2048 -> F = 8 * (g - SHA) ->
  getr regs2 10%bv = Z_to_bv 64 F -> getr regs2 9%bv = Z_to_bv 64 sp1 -> getr regs2 20%bv = Z_to_bv 64 SHA -> getr regs2 2%bv = Z_to_bv 64 sp1 ->
  getr regs2 4%bv = Z_to_bv 64 TP_B -> getr regs2 8%bv = Z_to_bv 64 sp -> getr regs2 21%bv = Z_to_bv 64 expo -> getr regs2 27%bv = Z_to_bv 64 buf ->
  mscellsB m2 -> mem_def m2 g 256 -> mem_def m2 F 2048 -> mem_def m2 (sp - 3072) 3072 ->
  (cellN SEGS_B m2 (sp1 + 16) 8 len /\ cellN SEGS_B m2 (sp1 + 24) 8 (bv_unsigned f) /\ cellN SEGS_B m2 (sp1 + 8) 8 w4) ->
  SAV sp m2 (savs regs ret) ->
  mem_byte m2 (FS + 35840 + p) 1 -> mem_u64 m2 (F + 2040) (FS + 35840 + p) ->
  unch m m2 [(sp - 432, sp); (FS + 40, FS + 48); (FS + 35840 + p, FS + 35840 + p + 1); (F, F + 1344); (F + 2040, F + 2048); (g, g + 256)] ->
  mem_grows m m2 ->
  rt_ok_B m -> ro_ok SEGS_B RO_B m -> gsh_ok_B m -> digs buf ds m -> dsh bg0 bgl m ->
  malloc_ctx_ok_B (sp - 3072) sp FS m -> rd_u64_B m FSTLS_B FS -> mem_u64 m (FS + 88) 20 -> mem_byte m (FS + 96) 0 ->
  (forall j, 0 <= j < 512 -> mem_byte m (fs_flag FS 5 j) 0) ->
  0 <= expo < 2 ^ 64 -> 0 <= w4 < 2 ^ 64 ->
  exists regsP mP,
    msteps SEGS_B (mkst regs2 (Z_to_bv 64 0x0a94c4) m2 rom) (mkst regsP (Z_to_bv 64 0x0a9c5c) mP rom)
    /\ getr regsP 1%bv = Z_to_bv 64 0x0a9634 /\ getr regsP 10%bv = Z_to_bv 64 (F + 32) /\ getr regsP 11%bv = Z_to_bv 64 buf
    /\ getr regsP 12%bv = Z_to_bv 64 len /\ getr regsP 2%bv = Z_to_bv 64 sp1 /\ getr regsP 4%bv = Z_to_bv 64 TP_B
    /\ getr regsP 9%bv = Z_to_bv 64 sp1 /\ getr regsP 8%bv = Z_to_bv 64 sp /\ getr regsP 18%bv = Z_to_bv 64 F
    /\ getr regsP 21%bv = Z_to_bv 64 expo /\ getr regsP 20%bv = Z_to_bv 64 g /\ getr regsP 19%bv = Z_to_bv 64 (g + 86)
    /\ getr regsP 24%bv = Z_to_bv 64 F /\ getr regsP 22%bv = Z_to_bv 64 (F + 32) /\ getr regsP 23%bv = Z_to_bv 64 (F + 688)
    /\ getr regsP 27%bv = Z_to_bv 64 buf /\ getr regsP 26%bv = Z_to_bv 64 (g + 4)
    /\ keeps [3; 4] regs2 regsP
    /\ cellN SEGS_B mP (sp1 + 16) 8 len /\ cellN SEGS_B mP (sp1 + 24) 8 (bv_unsigned f) /\ cellN SEGS_B mP (sp1 + 8) 8 w4
    /\ SAV sp mP (savs regs ret) /\ objshB mP (F + 32) /\ objshB mP (F + 688)
    /\ rt_ok_B mP /\ ro_ok SEGS_B RO_B mP /\ gsh_ok_B mP /\ digs buf ds mP /\ dsh bg0 bgl mP
    /\ malloc_ctx_ok_B (sp - 3072) sp FS mP /\ rd_u64_B mP FSTLS_B FS
    /\ mem_u64 mP (FS + 88) 20 /\ mem_byte mP (FS + 96) 0
    /\ (forall j, 0 <= j < 512 -> j <> p -> mem_byte mP (fs_flag FS 5 j) 0) /\ mem_byte mP (FS + 35840 + p) 1
    /\ mem_u64 mP (F + 2040) (FS + 35840 + p)
    /\ unch m mP [(sp - 432, sp); (FS + 40, FS + 48); (FS + 35840 + p, FS + 35840 + p + 1); (F, F + 1344); (F + 2040, F + 2048); (g, g + 256)]
    /\ mem_grows m mP.
Proof.
  intros regs regs2 m m2 ret f expo w4 p F g Hp HFdef HgF C10 D9 D21 D2 D4 D8 D20 D26 MC2 WG2 WF2 Wsp2 SL2' SV2 FL1 Q2040 U02 G02
    RT RO GSH DG DSH MCX TLS L88 B96 FL0 Hexpo Hw4.
  pose proof (csp1_facts buf len sp FS bg0 bgl CE) as (Hs1 & [q1 Hq1] & Hs16). clear Hs16.
  pose proof CE as CE0. cgeom CE. move DspFS after Dbfr.
  pose proof (u64_range f) as Wf. hide Hds.
  (* [comment removed for export] *)
  zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (KHI + 2048, HIE - 160); Some (IMG, HIE - 2048)]) (@nil kcell)
                          [KW (ZV 32) 0 160; KW (ZV 33) 0 24; KW (ZDivP (ZV 33) 3) SHA (SHA + 256)])
    40%nat [0x78590] (SCR [] []) constr:([(9%bv : reg, ZV 32); (10%bv : reg, ZV 33); (20%bv : reg, ZL SHA)]) [sp1; F]
    constr:([Some (KHI + 2048, HIE - 160); Some (IMG, HIE - 2048)]) regs2 m2 rom 0x0a94c4.
  zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I)
    ltac:(kwd Wsp2; kwd WF2; kwd WG2; exact I) ltac:(exact I). zx_name regs3.
  zx_reg ZR (1%bv : reg) as C1. zx_reg ZR (10%bv : reg) as C10'. zx_reg ZR (11%bv : reg) as C11. zx_reg ZR (18%bv : reg) as C18.
  zx_reg ZR (20%bv : reg) as C21. zx_reg ZR (24%bv : reg) as C23. zx_reg ZR (22%bv : reg) as C24. zx_reg ZR (23%bv : reg) as C25. zx_reg ZR (26%bv : reg) as C27.
  assert (K3 : keeps [2; 3; 4; 8; 9; 19; 21; 25; 27] regs2 regs3) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
  rename ZM into M3. clear ZE ZR ZF. set (m3 := wbytes _ _ _) in M3.
  assert (U23 : unch m2 m3 [(sp1 + 48, sp1 + 56); (F, F + 24); (g, g + 4)]) by (subst m3; clear - Hs1 Esp1 Esp2 Efs1 Efs2 Hp HFdef HgF; unchx).
  assert (G23 : mem_grows m2 m3) by (subst m3; growsx).
  destruct (setsh_B rom true regs3 m3 (g + 4) 65 (Z_to_bv 64 0x0a9558)) as (regs4 & M4 & K4).
  { rewrite C10'; f_equal; lia. } { exact C11. } { exact C1. } { vm_compute. reflexivity. } { lia. } { lia. } { lia. }
  { eapply store_ok_of_def_in; [eapply mem_def_grows; [exact G23 | exact WG2]|]. zwidth. lia. }
  { eapply mscellsB_unch; [exact U23 | intros r Hr; unfold highr; inr Hr ltac:(slia) | exact MC2]. }
  cbn [negb] in M4. set (m4 := wbytes m3 _ _) in M4.
  assert (U34 : unch m3 m4 [(g + 4, g + 69)]).
  { unfold m4. eapply (unch_store_bs m3 (g + 4)); rewrite ?repeat_length; [lia | zwidth; lia | in_list | lia | lia]. }
  assert (G34 : mem_grows m3 m4) by (unfold m4; apply grows_store).
  assert (D21' : getr regs4 20%bv = Z_to_bv 64 g) by (etransitivity; [exact (K4 20 ltac:(in_list)) | etransitivity; [exact C21 | f_equal; lia]]).
  (* [comment removed for export] *)
  zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (SHA, KHI - 256)]) (@nil kcell) [KW (ZV 32) 0 256])
    40%nat [0x78590] (SCR [] []) constr:([(20%bv : reg, ZV 32)]) [g] constr:([Some (SHA, KHI - 256)]) regs4 m4 rom 0x0a9558.
  zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I)
    ltac:(kwd (mem_def_grows _ _ _ _ (mem_grows_trans _ _ _ G23 G34) WG2); exact I) ltac:(exact I). zx_name regs5.
  zx_reg ZR (1%bv : reg) as E1. zx_reg ZR (10%bv : reg) as E10. zx_reg ZR (11%bv : reg) as E11. zx_reg ZR (19%bv : reg) as E22.
  assert (K5 : keeps [2; 3; 4; 8; 9; 18; 20; 21; 22; 23; 24; 25; 26; 27] regs4 regs5) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
  rename ZM into M5. clear ZE ZR ZF. set (m5 := wbytes _ _ _) in M5.
  assert (U45 : unch m4 m5 [(g + 69, g + 86)]) by (subst m5; clear - Hs1 Esp1 Esp2 Efs1 Efs2 Hp HFdef HgF; unchx).
  assert (G45 : mem_grows m4 m5) by (subst m5; growsx).
  assert (G25 : mem_grows m2 m5) by (eapply mem_grows_trans; [exact G23|]; eapply mem_grows_trans; [exact G34 | exact G45]).
  assert (U25 : unch m2 m5 [(sp1 + 48, sp1 + 56); (F, F + 24); (g, g + 86)]).
  { eapply unch_trans; [uwiden U23 | eapply unch_trans; [uwiden U34 | uwiden U45]]. }
  destruct (setsh_B rom true regs5 m5 (g + 86) 65 (Z_to_bv 64 0x0a95b0)) as (regs6 & M6 & K6).
  { rewrite E10; f_equal; lia. } { exact E11. } { exact E1. } { vm_compute. reflexivity. } { lia. } { lia. } { lia. }
  { eapply store_ok_of_def_in; [eapply mem_def_grows; [exact G25 | exact WG2]|]. zwidth. lia. }
  { eapply mscellsB_unch; [exact U25 | intros r Hr; unfold highr; inr Hr ltac:(slia) | exact MC2]. }
  cbn [negb] in M6. set (m6 := wbytes m5 _ _) in M6.
  assert (U56 : unch m5 m6 [(g + 86, g + 151)]).
  { unfold m6. eapply (unch_store_bs m5 (g + 86)); rewrite ?repeat_length; [lia | zwidth; lia | in_list | lia | lia]. }
  assert (G56 : mem_grows m5 m6) by (unfold m6; apply grows_store).
  assert (F21 : getr regs6 20%bv = Z_to_bv 64 g) by (etransitivity; [exact (K6 20 ltac:(in_list)) | kept K5 20 D21']).
  assert (F27 : getr regs6 26%bv = Z_to_bv 64 (g + 4)).
  { etransitivity; [exact (K6 26 ltac:(in_list)) |]. etransitivity; [exact (K5 26 ltac:(in_list)) |].
    etransitivity; [exact (K4 26 ltac:(in_list)) | etransitivity; [exact C27 | f_equal; lia]]. }
  (* [comment removed for export] *)
  zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (SHA, KHI - 256)]) (@nil kcell) [KW (ZV 32) 0 256])
    40%nat [0x78470] (SCR [] []) constr:([(20%bv : reg, ZV 32); (26%bv : reg, ZAdd (ZV 32) (ZL 4))]) [g] constr:([Some (SHA, KHI - 256)]) regs6 m6 rom 0x0a95b0.
  zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I)
    ltac:(kwd (mem_def_grows _ _ _ _ (mem_grows_trans _ _ _ G25 G56) WG2); exact I) ltac:(exact I). zx_name regs7.
  zx_reg ZR (1%bv : reg) as H1. zx_reg ZR (10%bv : reg) as H10. zx_reg ZR (11%bv : reg) as H11.
  assert (K7 : keeps [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] regs6 regs7) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
  rename ZM into M7. clear ZE ZR ZF. set (m7 := wbytes _ _ _) in M7.
  assert (U67 : unch m6 m7 [(g + 151, g + 168)]) by (subst m7; clear - Hs1 Esp1 Esp2 Efs1 Efs2 Hp HFdef HgF; unchx).
  assert (G67 : mem_grows m6 m7) by (subst m7; growsx).
  assert (G27 : mem_grows m2 m7) by (eapply mem_grows_trans; [exact G25|]; eapply mem_grows_trans; [exact G56 | exact G67]).
  assert (U27 : unch m2 m7 [(sp1 + 48, sp1 + 56); (F, F + 24); (g, g + 168)]).
  { eapply unch_trans; [uwiden U25 | eapply unch_trans; [uwiden U56 | uwiden U67]]. }
  destruct (setsh_B rom false regs7 m7 (g + 4) 64 (Z_to_bv 64 0x0a9604)) as (regs8 & M8 & K8).
  { rewrite H10; f_equal; lia. } { exact H11. } { exact H1. } { vm_compute. reflexivity. } { lia. } { lia. } { lia. }
  { eapply store_ok_of_def_in; [eapply mem_def_grows; [exact G27 | exact WG2]|]. zwidth. lia. }
  { eapply mscellsB_unch; [exact U27 | intros r Hr; unfold highr; inr Hr ltac:(slia) | exact MC2]. }
  cbn [negb] in M8. set (m8 := wbytes m7 _ _) in M8.
  assert (U78 : unch m7 m8 [(g + 4, g + 68)]).
  { unfold m8. eapply (unch_store_bs m7 (g + 4)); rewrite ?repeat_length; [lia | zwidth; lia | in_list | lia | lia]. }
  assert (G78 : mem_grows m7 m8) by (unfold m8; apply grows_store).
  assert (OBA8 : objshB m8 (F + 32)).
  { intros k Hk. unfold m8. eapply cellN_byte; [| lia | lia | lia].
    replace (SHA + (F + 32) / 8 + k) with (g + 4 + k) by lia. apply mem_byte_repeat_in; rewrite ?repeat_length; try lia. reflexivity. }
  assert (I21 : getr regs8 20%bv = Z_to_bv 64 g) by (etransitivity; [exact (K8 20 ltac:(in_list)) | kept K7 20 F21]).
  assert (I18 : getr regs8 18%bv = Z_to_bv 64 F).
  { etransitivity; [exact (K8 18 ltac:(in_list)) |]. etransitivity; [exact (K7 18 ltac:(in_list)) |]. etransitivity; [exact (K6 18 ltac:(in_list)) |].
    etransitivity; [exact (K5 18 ltac:(in_list)) |]. etransitivity; [exact (K4 18 ltac:(in_list)) | exact C18]. }
  assert (I22 : getr regs8 19%bv = Z_to_bv 64 (g + 86)).
  { etransitivity; [exact (K8 19 ltac:(in_list)) |]. etransitivity; [exact (K7 19 ltac:(in_list)) |]. etransitivity; [exact (K6 19 ltac:(in_list)) | etransitivity; [exact E22 | f_equal; lia]]. }
  (* [comment removed for export] *)
  zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (SHA, KHI - 256); Some (IMG, HIE - 2048)]) (@nil kcell) [KW (ZV 32) 0 256; KW (ZV 33) 0 1344])
    40%nat [0x78470] (SCR [] []) constr:([(20%bv : reg, ZV 32); (18%bv : reg, ZV 33); (19%bv : reg, ZAdd (ZV 32) (ZL 86))]) [g; F]
    constr:([Some (SHA, KHI - 256); Some (IMG, HIE - 2048)]) regs8 m8 rom 0x0a9604.
  zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I)
    ltac:(kwd (mem_def_grows _ _ _ _ (mem_grows_trans _ _ _ G27 G78) WG2); kwd (mem_def_grows _ _ _ _ (mem_grows_trans _ _ _ G27 G78) WF2); exact I) ltac:(exact I).
  zx_name regs9.
  zx_reg ZR (1%bv : reg) as J1. zx_reg ZR (10%bv : reg) as J10. zx_reg ZR (11%bv : reg) as J11. zx_reg ZR (25%bv : reg) as J19.
  assert (K9 : keeps [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 26; 27] regs8 regs9) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
  rename ZM into M9. clear ZE ZR ZF. set (m9 := wbytes _ _ _) in M9.
  assert (U89 : unch m8 m9 [(g + 68, g + 69); (F + 32, F + 36)]) by (subst m9; clear - Hs1 Esp1 Esp2 Efs1 Efs2 Hp HFdef HgF; unchx).
  assert (G89 : mem_grows m8 m9) by (subst m9; growsx).
  assert (G29 : mem_grows m2 m9) by (eapply mem_grows_trans; [exact G27|]; eapply mem_grows_trans; [exact G78 | exact G89]).
  assert (U29 : unch m2 m9 [(sp1 + 48, sp1 + 56); (F, F + 36); (g, g + 168)]).
  { eapply unch_trans; [uwiden U27 | eapply unch_trans; [uwiden U78 | uwiden U89]]. }
  destruct (setsh_B rom false regs9 m9 (g + 86) 64 (Z_to_bv 64 0x0a961c)) as (regs10 & M10 & K10).
  { rewrite J10; f_equal; lia. } { exact J11. } { exact J1. } { vm_compute. reflexivity. } { lia. } { lia. } { lia. }
  { eapply store_ok_of_def_in; [eapply mem_def_grows; [exact G29 | exact WG2]|]. zwidth. lia. }
  { eapply mscellsB_unch; [exact U29 | intros r Hr; unfold highr; inr Hr ltac:(slia) | exact MC2]. }
  cbn [negb] in M10. set (m10 := wbytes m9 _ _) in M10.
  assert (U910 : unch m9 m10 [(g + 86, g + 150)]).
  { unfold m10. eapply (unch_store_bs m9 (g + 86)); rewrite ?repeat_length; [lia | zwidth; lia | in_list | lia | lia]. }
  assert (G910 : mem_grows m9 m10) by (unfold m10; apply grows_store).
  assert (OBB10 : objshB m10 (F + 688)).
  { intros k Hk. unfold m10. eapply cellN_byte; [| lia | lia | lia].
    replace (SHA + (F + 688) / 8 + k) with (g + 86 + k) by lia. apply mem_byte_repeat_in; rewrite ?repeat_length; try lia. reflexivity. }
  assert (OBA10 : objshB m10 (F + 32)).
  { eapply (objshB_unch2 m9 m10); [exact U910 | intros r Hr; inr Hr ltac:(slia) | lia | lia |].
    eapply (objshB_unch2 m8 m9); [exact U89 | intros r Hr; inr Hr ltac:(slia) | lia | lia | exact OBA8]. }
  (* [comment removed for export] *)
  assert (L21 : getr regs10 20%bv = Z_to_bv 64 g) by (etransitivity; [exact (K10 20 ltac:(in_list)) | kept K9 20 I21]).
  assert (L18 : getr regs10 18%bv = Z_to_bv 64 F) by (etransitivity; [exact (K10 18 ltac:(in_list)) | kept K9 18 I18]).
  assert (L19 : getr regs10 25%bv = Z_to_bv 64 4) by (etransitivity; [exact (K10 25 ltac:(in_list)) | exact J19]).
  assert (L24 : getr regs10 22%bv = Z_to_bv 64 (F + 32)).
  { etransitivity; [exact (K10 22 ltac:(in_list)) |]. etransitivity; [exact (K9 22 ltac:(in_list)) |]. etransitivity; [exact (K8 22 ltac:(in_list)) |].
    etransitivity; [exact (K7 22 ltac:(in_list)) |]. etransitivity; [exact (K6 22 ltac:(in_list)) |]. etransitivity; [exact (K5 22 ltac:(in_list)) |].
    etransitivity; [exact (K4 22 ltac:(in_list)) | etransitivity; [exact C24 | f_equal; lia]]. }
  assert (L26 : getr regs10 27%bv = Z_to_bv 64 buf).
  { etransitivity; [exact (K10 27 ltac:(in_list)) |]. etransitivity; [exact (K9 27 ltac:(in_list)) |]. etransitivity; [exact (K8 27 ltac:(in_list)) |].
    etransitivity; [exact (K7 27 ltac:(in_list)) |]. etransitivity; [exact (K6 27 ltac:(in_list)) |]. etransitivity; [exact (K5 27 ltac:(in_list)) |].
    etransitivity; [exact (K4 27 ltac:(in_list)) |]. kept K3 27 D26. }
  assert (L9 : getr regs10 9%bv = Z_to_bv 64 sp1).
  { etransitivity; [exact (K10 9 ltac:(in_list)) |]. etransitivity; [exact (K9 9 ltac:(in_list)) |]. etransitivity; [exact (K8 9 ltac:(in_list)) |].
    etransitivity; [exact (K7 9 ltac:(in_list)) |]. etransitivity; [exact (K6 9 ltac:(in_list)) |]. etransitivity; [exact (K5 9 ltac:(in_list)) |].
    etransitivity; [exact (K4 9 ltac:(in_list)) | kept K3 9 D9]. }
  assert (S8 : cellN SEGS_B m10 (sp1 + 16) 8 len).
  { destruct SL2' as (X1 & _). eapply cellN_unch; [exact U910 | lia | cbn; lia | intros r Hr; inr Hr ltac:(pl) |].
    eapply cellN_unch; [exact U29 | lia | cbn; lia | intros r Hr; inr3 Hr ltac:(pl) ltac:(dl DspFS) ltac:(pl) | exact X1]. }
  (* [comment removed for export] *)
  zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (SHA, KHI - 256); Some (IMG, HIE - 2048); Some (KHI + 2048, HIE - 160); Some (1, 780); Some (IMG, HIE - 1)])
                          [KC (ZV 34) 16 8 (ZV 35)] [KW (ZV 32) 0 256; KW (ZV 33) 0 1344])
    40%nat [0x0a9c5c] (SCR [] []) constr:([(20%bv : reg, ZV 32); (18%bv : reg, ZV 33); (25%bv : reg, ZL 4); (22%bv : reg, ZAdd (ZV 33) (ZL 32)); (27%bv : reg, ZV 36); (9%bv : reg, ZV 34)])
    [g; F; sp1; len; buf] constr:([Some (SHA, KHI - 256); Some (IMG, HIE - 2048); Some (KHI + 2048, HIE - 160); Some (1, 780); Some (IMG, HIE - 1)]) regs10 m10 rom 0x0a961c.
  zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 S8; exact I)
    ltac:(kwd (mem_def_grows _ _ _ _ (mem_grows_trans _ _ _ G29 G910) WG2); kwd (mem_def_grows _ _ _ _ (mem_grows_trans _ _ _ G29 G910) WF2); exact I)
    ltac:(idtac; zx_scs ltac:(flia)). zx_name regsP.
  zx_reg ZR (1%bv : reg) as P1. zx_reg ZR (10%bv : reg) as P10. zx_reg ZR (11%bv : reg) as P11. zx_reg ZR (12%bv : reg) as P12.
  assert (KP : keeps [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] regs10 regsP) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
  rename ZM into MP. clear ZE ZR ZF. set (mP := wbytes _ _ _) in MP.
  assert (U1011 : unch m10 mP [(g + 150, g + 151); (F + 688, F + 692)]) by (subst mP; clear - Hs1 Esp1 Esp2 Efs1 Efs2 Hp HFdef HgF; unchx).
  assert (G1011 : mem_grows m10 mP) by (subst mP; growsx).
  (* [comment removed for export] *)
  assert (U2P : unch m2 mP [(sp1 + 48, sp1 + 56); (F, F + 692); (g, g + 168)]).
  { eapply unch_trans; [uwiden U29 | eapply unch_trans; [uwiden U910 | uwiden U1011]]. }
  assert (G2P : mem_grows m2 mP) by (eapply mem_grows_trans; [exact G29|]; eapply mem_grows_trans; [exact G910 | exact G1011]).
  assert (HR2P : forall r, In r [(sp1 + 48, sp1 + 56); (F, F + 692); (g, g + 168)] -> highr r) by (intros r Hr; unfold highr; inr Hr ltac:(slia)).
  assert (U0P : unch m mP [(sp - 432, sp); (FS + 40, FS + 48); (FS + 35840 + p, FS + 35840 + p + 1); (F, F + 1344); (F + 2040, F + 2048); (g, g + 256)]).
  { eapply unch_trans; [exact U02 | uwiden U2P]. }
  assert (HR0P : forall r, In r [(sp - 432, sp); (FS + 40, FS + 48); (FS + 35840 + p, FS + 35840 + p + 1); (F, F + 1344); (F + 2040, F + 2048); (g, g + 256)] -> highr r)
    by (intros r Hr; unfold highr; inr Hr ltac:(slia)).
  (* [comment removed for export] *)
  exists regsP, mP. split.
  { eapply msteps_trans; [exact M3|].
    eapply msteps_trans; [exact M4|]. eapply msteps_trans; [exact M5|]. eapply msteps_trans; [exact M6|]. eapply msteps_trans; [exact M7|].
    eapply msteps_trans; [exact M8|]. eapply msteps_trans; [exact M9|]. eapply msteps_trans; [exact M10 | exact MP]. }
  split; [exact P1|]. split; [rewrite P10; f_equal; lia|]. split; [exact P11|]. split; [exact P12|].
  assert (KK : keeps [2; 3; 4; 8; 9; 21] regs2 regsP).
  { eapply keeps_trans; [eapply keeps_sub_dec; [exact K3|]; vm_compute; reflexivity|].
    eapply keeps_trans; [eapply keeps_sub_dec; [exact K4|]; vm_compute; reflexivity|].
    eapply keeps_trans; [eapply keeps_sub_dec; [exact K5|]; vm_compute; reflexivity|].
    eapply keeps_trans; [eapply keeps_sub_dec; [exact K6|]; vm_compute; reflexivity|].
    eapply keeps_trans; [eapply keeps_sub_dec; [exact K7|]; vm_compute; reflexivity|].
    eapply keeps_trans; [eapply keeps_sub_dec; [exact K8|]; vm_compute; reflexivity|].
    eapply keeps_trans; [eapply keeps_sub_dec; [exact K9|]; vm_compute; reflexivity|].
    eapply keeps_trans; [eapply keeps_sub_dec; [exact K10|]; vm_compute; reflexivity|].
    eapply keeps_sub_dec; [exact KP|]; vm_compute; reflexivity. }
  split; [kept KK 2 D2|].
  split; [kept KK 4 D4|]. split; [kept KP 9 L9|]. split; [kept KK 8 D8|]. split; [kept KP 18 L18|]. split; [kept KK 21 D20|].
  split; [kept KP 20 L21|].
  split; [etransitivity; [exact (KP 19 ltac:(in_list)) |]; etransitivity; [exact (K10 19 ltac:(in_list)) | kept K9 19 I22]|].
  split.
  { etransitivity; [exact (KP 24 ltac:(in_list)) |]. etransitivity; [exact (K10 24 ltac:(in_list)) |]. etransitivity; [exact (K9 24 ltac:(in_list)) |].
    etransitivity; [exact (K8 24 ltac:(in_list)) |]. etransitivity; [exact (K7 24 ltac:(in_list)) |]. etransitivity; [exact (K6 24 ltac:(in_list)) |].
    etransitivity; [exact (K5 24 ltac:(in_list)) |]. etransitivity; [exact (K4 24 ltac:(in_list)) | exact C23]. }
  split; [kept KP 22 L24|].
  split.
  { etransitivity; [exact (KP 23 ltac:(in_list)) |]. etransitivity; [exact (K10 23 ltac:(in_list)) |]. etransitivity; [exact (K9 23 ltac:(in_list)) |].
    etransitivity; [exact (K8 23 ltac:(in_list)) |]. etransitivity; [exact (K7 23 ltac:(in_list)) |]. etransitivity; [exact (K6 23 ltac:(in_list)) |].
    etransitivity; [exact (K5 23 ltac:(in_list)) |]. etransitivity; [exact (K4 23 ltac:(in_list)) | etransitivity; [exact C25 | f_equal; lia]]. }
  split; [kept KP 27 L26|].
  split.
  { etransitivity; [exact (KP 26 ltac:(in_list)) |]. etransitivity; [exact (K10 26 ltac:(in_list)) |]. etransitivity; [exact (K9 26 ltac:(in_list)) |].
    etransitivity; [exact (K8 26 ltac:(in_list)) | kept K7 26 F27]. }
  split; [eapply keeps_sub_dec; [exact KK|]; vm_compute; reflexivity|].
  destruct SL2' as (X1 & X2 & X3).
  split; [eapply cellN_unch; [exact U2P | lia | cbn; lia | intros r Hr; inr3 Hr ltac:(pl) ltac:(dl DspFS) ltac:(pl) | exact X1]|].
  split; [eapply cellN_unch; [exact U2P | lia | cbn; lia | intros r Hr; inr3 Hr ltac:(pl) ltac:(dl DspFS) ltac:(pl) | exact X2]|].
  split; [eapply cellN_unch; [exact U2P | lia | cbn; lia | intros r Hr; inr3 Hr ltac:(pl) ltac:(dl DspFS) ltac:(pl) | exact X3]|].
  split.
  { intros k Hk. eapply cellN_unch; [exact U2P | lia | cbn; lia | intros r Hr; inr3 Hr ltac:(pl) ltac:(dl DspFS) ltac:(pl) | exact (SV2 k Hk)]. }
  split; [eapply (objshB_unch2 m10 mP); [exact U1011 | intros r Hr; inr Hr ltac:(slia) | lia | lia | exact OBA10]|].
  split; [eapply (objshB_unch2 m10 mP); [exact U1011 | intros r Hr; inr Hr ltac:(slia) | lia | lia | exact OBB10]|].
  split; [eapply rt_ok_B_unch; [exact U0P | exact HR0P | exact RT]|].
  split; [eapply ro_ok_unchB; [exact U0P | exact HR0P | exact RO]|].
  split; [eapply gsh_ok_B_unch; [exact U0P | exact HR0P | exact GSH]|].
  split.
  { intros k Hk. unfold hide in Hds. rewrite Hds in Hk. eapply cellN_unch; [exact U0P | lia | cbn; lia | | apply DG; rewrite Hds; exact Hk].
    intros r Hr. inr6 Hr ltac:(dl Dbsp) ltac:(dl Dbh) ltac:(dl Dbfl) ltac:(dl Dbfr) ltac:(dl Dbfr) ltac:(pl). }
  split.
  { intros q Hq. eapply cellN_unch; [exact U0P | lia | cbn; lia | | apply DSH; exact Hq].
    intros r Hr. inr6 Hr ltac:(pl) ltac:(pl) ltac:(pl) ltac:(pl) ltac:(pl) ltac:(dl Dbfr). }
  split.
  { eapply malloc_ctx_ok_B_unch; [exact MCX | exact U0P | eapply mem_grows_trans; [exact G02 | exact G2P] | | lia | lia].
    intros r Hr. split; [pose proof (HR0P r Hr) as X; unfold highr in X; lia|]. unfold FS_LEN, KHI_A. inr Hr ltac:(slia). }   (* [comment removed for export] *)
  split; [eapply cellN_low_unchB; [exact U0P | exact HR0P | unfold FSTLS_B; lia | unfold FSTLS_B; cbn; lia | exact TLS]|].
  split; [eapply mem_u64_unch; [exact U0P | lia | lia | intros r Hr; inr6 Hr ltac:(dl DspFS) ltac:(pl) ltac:(pl) ltac:(pl) ltac:(pl) ltac:(pl) | exact L88]|].
  split; [eapply mem_byte_unch; [exact U0P | lia | intros r Hr; inr6 Hr ltac:(dl DspFS) ltac:(pl) ltac:(pl) ltac:(pl) ltac:(pl) ltac:(pl) | exact B96]|].
  split.
  { intros j Hj Hne. rewrite fs_flag5. eapply mem_byte_unch; [exact U0P | lia | | rewrite <- fs_flag5; exact (FL0 j Hj)].
    intros r Hr. inr6 Hr ltac:(dl DspFS) ltac:(pl) ltac:(pl) ltac:(pl) ltac:(pl) ltac:(pl). }
  split; [eapply mem_byte_unch; [exact U2P | lia | intros r Hr; inr3 Hr ltac:(dl DspFS) ltac:(pl) ltac:(pl) | exact FL1]|].
  split; [eapply mem_u64_unch; [exact U2P | lia | lia | intros r Hr; inr3 Hr ltac:(dl DspFS) ltac:(pl) ltac:(pl) | exact Q2040]|].
  split; [exact U0P | eapply mem_grows_trans; [exact G02 | exact G2P]].
Qed.

(* [comment removed for export] *)
#[using="CE Hds"] Lemma cbd_pro_B : forall regs m (ret f : word) (expo w4 : Z),
  getr regs 10%bv = Z_to_bv 64 buf -> getr regs 11%bv = Z_to_bv 64 len -> getr regs 12%bv = Z_to_bv 64 expo ->
  getr regs 13%bv = f -> getr regs 14%bv = Z_to_bv 64 w4 -> 0 <= expo < 2 ^ 64 -> 0 <= w4 < 2 ^ 64 ->
  getr regs 2%bv = Z_to_bv 64 sp -> getr regs 1%bv = ret -> getr regs 4%bv = Z_to_bv 64 TP_B ->
  rt_ok_B m -> ro_ok SEGS_B RO_B m -> gsh_ok_B m -> digs buf ds m -> dsh bg0 bgl m ->
  mem_def m (sp - 3072) 3072 ->
  malloc_ctx_ok_B (sp - 3072) sp FS m -> rd_u64_B m FSTLS_B FS ->
  mem_def m FS FS_LEN -> mem_def m (sh FS + FS_SHLO) (FS_SHHI - FS_SHLO) -> mem_u64 m (FS + 88) 20 -> mem_byte m (FS + 96) 0 ->
  (forall j, 0 <= j < 512 -> mem_byte m (fs_flag FS 5 j) 0) ->
  exists regsP mP p F g,
    msteps SEGS_B (mkst regs (Z_to_bv 64 0x0a9444) m rom) (mkst regsP (Z_to_bv 64 0x0a9c5c) mP rom)
    /\ 0 <= p < 512 /\ F = FS + 5279744 + p * 2048 /\ F = 8 * (g - SHA)
    /\ getr regsP 1%bv = Z_to_bv 64 0x0a9634 /\ getr regsP 10%bv = Z_to_bv 64 (F + 32) /\ getr regsP 11%bv = Z_to_bv 64 buf
    /\ getr regsP 12%bv = Z_to_bv 64 len /\ getr regsP 2%bv = Z_to_bv 64 sp1 /\ getr regsP 4%bv = Z_to_bv 64 TP_B
    /\ getr regsP 9%bv = Z_to_bv 64 sp1 /\ getr regsP 8%bv = Z_to_bv 64 sp /\ getr regsP 18%bv = Z_to_bv 64 F
    /\ getr regsP 21%bv = Z_to_bv 64 expo /\ getr regsP 20%bv = Z_to_bv 64 g /\ getr regsP 19%bv = Z_to_bv 64 (g + 86)
    /\ getr regsP 24%bv = Z_to_bv 64 F /\ getr regsP 22%bv = Z_to_bv 64 (F + 32) /\ getr regsP 23%bv = Z_to_bv 64 (F + 688)
    /\ getr regsP 27%bv = Z_to_bv 64 buf /\ getr regsP 26%bv = Z_to_bv 64 (g + 4)
    /\ keeps [3; 4] regs regsP
    /\ cellN SEGS_B mP (sp1 + 16) 8 len /\ cellN SEGS_B mP (sp1 + 24) 8 (bv_unsigned f) /\ cellN SEGS_B mP (sp1 + 8) 8 w4
    /\ SAV sp mP (savs regs ret) /\ objshB mP (F + 32) /\ objshB mP (F + 688)
    /\ rt_ok_B mP /\ ro_ok SEGS_B RO_B mP /\ gsh_ok_B mP /\ digs buf ds mP /\ dsh bg0 bgl mP
    /\ malloc_ctx_ok_B (sp - 3072) sp FS mP /\ rd_u64_B mP FSTLS_B FS
    /\ mem_u64 mP (FS + 88) 20 /\ mem_byte mP (FS + 96) 0
    /\ (forall j, 0 <= j < 512 -> j <> p -> mem_byte mP (fs_flag FS 5 j) 0) /\ mem_byte mP (FS + 35840 + p) 1
    /\ mem_u64 mP (F + 2040) (FS + 35840 + p)
    /\ unch m mP [(sp - 432, sp); (FS + 40, FS + 48); (FS + 35840 + p, FS + 35840 + p + 1); (F, F + 1344); (F + 2040, F + 2048); (g, g + 256)]
    /\ mem_grows m mP.
Proof.
  intros regs m ret f expo w4 R10 R11 R12 R13 R14 Hexpo Hw4 R2 R1 R4 RT RO GSH DG DSH Dsp MCX TLS DFS DSHD L88 B96 FL0.
  destruct (cbd_pro1 rom buf len sp FS bg0 bgl ds CE Hds regs m ret f expo w4 R10 R11 R12 R13 R14 Hexpo Hw4 R2 R1 R4 RT RO GSH DG DSH Dsp MCX TLS DFS DSHD L88 B96 FL0)
    as (regs2 & m2 & p & F & g & M02 & Hp & HFdef & HgF & C10 & D9 & D21 & D2 & D4 & D8 & D20 & D26 & K02 & MC2 & WG2 & WF2 & Wsp2 & SL2' & SV2 & FL1 & Q2040 & U02 & G02).
  destruct (cbd_pro2 regs regs2 m m2 ret f expo w4 p F g Hp HFdef HgF C10 D9 D21 D2 D4 D8 D20 D26 MC2 WG2 WF2 Wsp2 SL2' SV2 FL1 Q2040 U02 G02
              RT RO GSH DG DSH MCX TLS L88 B96 FL0 Hexpo Hw4)
    as (regsP & mP & M2P & REST).
  exists regsP, mP, p, F, g. split; [eapply msteps_trans; [exact M02 | exact M2P]|].
  split; [exact Hp|]. split; [exact HFdef|]. split; [exact HgF|].
  decompose [and] REST.
  repeat match goal with |- _ /\ _ => split end; try assumption.
  eapply keeps_trans; [exact K02 | assumption].
Qed.
End S.
