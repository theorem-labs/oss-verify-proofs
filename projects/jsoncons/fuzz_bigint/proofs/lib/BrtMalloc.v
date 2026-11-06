(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac BrtLeaf BrtPoison BrtAllocG BrtUnwind.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import Bo0_code_5fed4_60754 Bo0_code_67fdc_6814c Bo0_code_3d2b4_3e23c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section FPX. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
Lemma art_icu1 : forall regs (M rom : word -> option byte) (raw0 : word) (S n tp key tsd ctx t top bot : Z),
  getr regs 1 = raw0 -> getr regs 2 = Z_to_bv 64 S -> getr regs 4 = Z_to_bv 64 tp -> getr regs 10 = Z_to_bv 64 n ->
  0x10007fff8000 + 8192 <= S -> S <= 2 ^ 47 -> 0 <= n < 2 ^ 64 ->
  4096 <= t -> t + 4096 < 2 ^ 47 -> hid (t + 4096 <= 0x10000 \/ 0x634000 <= t) -> apart t 4096 (S - 4096) 8192 ->
  apart ctx 4096 (S - 4096) 8192 -> hid (ctx + 4096 <= 0x10000 \/ 0x634000 <= ctx) -> apart t 4096 ctx 4096 ->
  0x10100 <= tp -> tp + 8 <= 0x634000 -> 0x10000 <= tsd -> tsd + 1024 <= 0x634000 -> 0 <= bot < top -> top < 2 ^ 63 ->
  wrA M (S - 4096) 4096 -> wrA M t 4096 -> art_tsd M tp key tsd ctx t ->
  cellA M 0xdf418 1 1 -> cellA M 0xdf43c 4 30 -> cellA M 0xd64b8 8 0x170268 -> cellA M (0x170268 + 34) 1 1 ->
  cellA M (t + 3168) 1 0 -> cellA M (t + 40) 1 0 -> cellA M (t + 8) 8 top -> cellA M (t + 16) 8 bot ->
  exists regs1 M1,
    msteps ASEGS (mkst regs (0x600b4 : word) M rom) (mkst regs1 (0x80ab4 : word) M1 rom)
    /\ getr regs1 1 = (0x68118 : bv 64)%bv /\ getr regs1 2 = Z_to_bv 64 (S - 2208) /\ getr regs1 10 = Z_to_bv 64 (S - 2128)
    /\ getr regs1 11 = Z_to_bv 64 0x6017c /\ getr regs1 12 = Z_to_bv 64 S /\ getr regs1 13 = Z_to_bv 64 top /\ getr regs1 14 = Z_to_bv 64 bot
    /\ getr regs1 15 = Z_to_bv 64 30 /\ getr regs1 24 = Z_to_bv 64 (t + 2047) /\ getr regs1 4 = Z_to_bv 64 tp
    /\ (forall r : reg, In r [3; 25; 26; 27]%bv -> getr regs1 r = getr regs r)
    /\ mem_grows M M1
    /\ (forall x : word, ~ (S - 2272 <= U x < S) -> U x <> t + 3168 -> M1 x = M x)
    /\ cellA M1 (S - 8) 8 (U raw0) /\ cellA M1 (S - 16) 8 (U (getr regs 8)) /\ cellA M1 (S - 24) 8 (U (getr regs 9)) /\ cellA M1 (S - 32) 8 (U (getr regs 18))
    /\ cellA M1 (S - 40) 8 (U (getr regs 19)) /\ cellA M1 (S - 48) 8 (U (getr regs 20)) /\ cellA M1 (S - 56) 8 (U (getr regs 21))
    /\ cellA M1 (S - 2136) 8 0x601d8 /\ cellA M1 (S - 2144) 8 S /\ cellA M1 (S - 2152) 8 n /\ cellA M1 (S - 2160) 8 (U (0x6017c : bv 64)%bv) /\ cellA M1 (S - 2168) 8 1
    /\ cellA M1 (S - 2176) 8 (S - 2128) /\ cellA M1 (S - 2184) 8 (S - 81)
    /\ cellA M1 (S - 2192) 8 (U (getr regs 22)) /\ cellA M1 (S - 2200) 8 (U (getr regs 23)) /\ cellA M1 (S - 2208) 8 (U (getr regs 24))
    /\ cellA M1 (S - 2128) 8 (S - 2112) /\ cellA M1 (S - 2120) 4 0 /\ cellA M1 (S - 2116) 4 0
    /\ wrA M1 (S - 4096) 4096.
Proof.
  intros regs M rom raw0 S n tp key tsd ctx t top bot H1 H2 H4 H10 HS HS' Hn Ht Ht' Timg Atsp Actx Cimg Atctx Htp0 Htp1 Htsd0 Htsd Hbt Htop
         W Wt TSD Ci Cctx Cg38 Cfast Cunw C40 C8 C16.
  pose proof TSD as (Ttsd1 & Ttsd2 & Ttsd3 & Ttsd4 & Ttsd5 & TR).
  eexists _, _. split.
  - zstep F_600b4 D_600b4.
    zsd F_600b8 D_600b8 (S - 8) (U raw0) ltac:(rewok W). zsd F_600bc D_600bc (S - 16) (U (getr regs 8)) ltac:(rewok W).
    zsd F_600c0 D_600c0 (S - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_600c4 D_600c4 (S - 32) (U (getr regs 18)) ltac:(rewok W).
    zsd F_600c8 D_600c8 (S - 40) (U (getr regs 19)) ltac:(rewok W). zsd F_600cc D_600cc (S - 48) (U (getr regs 20)) ltac:(rewok W).
    zsd F_600d0 D_600d0 (S - 56) (U (getr regs 21)) ltac:(rewok W).
    zstep F_600d4 D_600d4. zstep F_600d8 D_600d8. zstep F_600dc D_600dc. zstep F_600e0 D_600e0.
    stepn F_600e4 D_600e4.
    zcall (art_try_init_fn _ _ _ _ (S - 2128)).
    zbft F_600e8 D_600e8.
    zstep F_600ec D_600ec. zstep F_600f0 D_600f0. zstep F_600f4 D_600f4. zstep F_600f8 D_600f8. zstep F_600fc D_600fc.
    zsd F_60100 D_60100 (S - 72) 0 ltac:(rewok W).
    zsd F_60104 D_60104 (S - 2128) (S - 2112) ltac:(rewok W).
    zsd F_60108 D_60108 (S - 2120) 0 ltac:(rewok W). rewrite (Wn8_zero_split _ (S - 2120)) by lia. replace (S - 2120 + 4) with (S - 2116) by lia.
    stepn F_6010c D_6010c.
    zcall (art_malloc_ctx_fn _ _ _ _).
    zstep F_60110 D_60110.
    zbtk F_60114 D_60114.
    stepn F_60178 D_60178.
    zcall (art_get_pc_fn _ _ _ _).
    zstep F_6017c D_6017c.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cg38' : cellA X 0xd64b8 8 0x170268) by zcell; assert (Cfast' : cellA X (0x170268 + 34) 1 1) by zcell end.
    zld F_60180 D_60180 0xd64b8 Cg38'. zlbu F_60184 D_60184 (0x170268 + 34) Cfast'.
    zstep F_60188 D_60188.
    stepn F_6018c D_6018c.
    zcall (art_malloc_ctx_fn _ _ _ _).
    zstep F_60190 D_60190. zstep F_60194 D_60194. zstep F_60198 D_60198.
    stepn F_6019c D_6019c. rwH. rewrite art_zb_and by lia. rewrite art_land_full_l by lia.
    zstep F_601a0 D_601a0.
    zsd F_601a4 D_601a4 (S - 72) S ltac:(rewok W).
    zbtk F_601a8 D_601a8.
    zstep F_601bc D_601bc. zstep F_601c0 D_601c0. zstep F_601c4 D_601c4. zstep F_601c8 D_601c8. zstep F_601cc D_601cc. zstep F_601d0 D_601d0.
    stepn F_601d4 D_601d4.
    (* [comment removed for export] *)
    zstep F_67ffc D_67ffc.
    zsd F_68000 D_68000 (S - 2136) 0x601d8 ltac:(rewok W). zsd F_68004 D_68004 (S - 2144) S ltac:(rewok W). zsd F_68008 D_68008 (S - 2152) n ltac:(rewok W).
    zsd F_6800c D_6800c (S - 2160) (U (0x6017c : bv 64)%bv) ltac:(rewok W). zsd F_68010 D_68010 (S - 2168) 1 ltac:(rewok W). zsd F_68014 D_68014 (S - 2176) (S - 2128) ltac:(rewok W).
    zsd F_68018 D_68018 (S - 2184) (S - 81) ltac:(rewok W). zsd F_6801c D_6801c (S - 2192) (U (getr regs 22)) ltac:(rewok W).
    zsd F_68020 D_68020 (S - 2200) (U (getr regs 23)) ltac:(rewok W). zsd F_68024 D_68024 (S - 2208) (U (getr regs 24)) ltac:(rewok W).
    zstep F_68028 D_68028. zstep F_6802c D_6802c. zstep F_68030 D_68030. zstep F_68034 D_68034. zstep F_68038 D_68038. zstep F_6803c D_6803c.
    zsw F_68040 D_68040 (S - 2120) 0 ltac:(rewok W).
    stepn F_68044 D_68044.
    zcall (art_asan_inited_fn _ _ _ _).
    zbft F_68048 D_68048.
    stepn F_6804c D_6804c.
    zcall (art_cur_thread_fn _ _ _ _ (S - 2208) tp key tsd ctx t).
    { unfold art_tsd. repeat split; try lia; zcell. }
    zbft F_68050 D_68050.
    zstep F_68054 D_68054.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cunw' : cellA X (t + 2047 + 1121) 1 0) by (replace (t + 2047 + 1121) with (t + 3168) by lia; zcell) end.
    zlbu F_68058 D_68058 (t + 2047 + 1121) Cunw'.
    zstep F_6805c D_6805c.
    zsb F_68060 D_68060 (t + 2047 + 1121) 1 ltac:(rewok Wt).
    zbft F_68064 D_68064.
    zstep F_68068 D_68068.
    stepn F_6806c D_6806c.
    zcall (art_stack_top_fn _ _ _ _ t top bot).
    zstep F_68070 D_68070. zstep F_68074 D_68074.
    stepn F_68078 D_68078.
    zcall (art_stack_bottom_fn _ _ _ _ t top bot).
    zstep F_6807c D_6807c.
    zbft F_68080 D_68080.
    zstep F_68084 D_68084. zstep F_68088 D_68088. zstep F_6808c D_6808c. zstep F_68090 D_68090. zstep F_68094 D_68094. zstep F_68098 D_68098. zstep F_6809c D_6809c.
    stepn F_680a0 D_680a0.
    stepn F_68114 D_68114.
    zcall (art_unwind_fn _ _ _ _ (S - 2208) (S - 2128) 0x6017c S top bot).
    apply mst_refl.
  - repeat match goal with |- _ /\ _ => split end.
    all: lazymatch goal with
         | |- getr _ _ = _ => gres; rwH; first [reflexivity | f_equal; lia | bveq]
         | |- forall r : reg, In r _ -> _ => intros r Hr; cbn [In] in Hr; destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; gres; reflexivity
         | |- mem_grows _ _ => repeat (eapply mem_grows_trans; [|apply Wn_grows]); apply mem_grows_refl
         | |- forall x : word, _ => intros x N1 N2; zagree
         | |- wr _ _ _ _ => zwr
         | |- cell _ _ _ _ _ => zcell
         end.
Qed.

(* [comment removed for export] *)
Lemma art_icu2_fn : forall regs (M rom : word -> option byte) (S n t f22 f23 f24 : Z),
  getr regs 2 = Z_to_bv 64 (S - 2208) -> getr regs 24 = Z_to_bv 64 (t + 2047) ->
  8192 <= S -> S <= 2 ^ 47 -> 0 <= n < 2 ^ 64 -> 4096 <= t -> t + 4096 < 2 ^ 64 -> apart t 4096 (S - 4096) 8192 ->
  0 <= f22 < 2 ^ 64 -> 0 <= f23 < 2 ^ 64 -> 0 <= f24 < 2 ^ 64 ->
  wrA M (S - 4096) 4096 -> wrA M t 4096 ->
  cellA M (S - 2136) 8 0x601d8 -> cellA M (S - 2144) 8 S -> cellA M (S - 2152) 8 n -> cellA M (S - 2160) 8 (U (0x6017c : bv 64)%bv) -> cellA M (S - 2168) 8 1 ->
  cellA M (S - 2176) 8 (S - 2128) -> cellA M (S - 2184) 8 (S - 81) -> cellA M (S - 2192) 8 f22 -> cellA M (S - 2200) 8 f23 -> cellA M (S - 2208) 8 f24 ->
  msteps ASEGS (mkst regs (0x68118 : word) M rom) (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x3d5c0 : bv 64)%bv) 2 (Z_to_bv 64 (S - 2144))) 8 (Z_to_bv 64 S)) 9 (Z_to_bv 64 n)) 10 (Z_to_bv 64 0xdb0d8)) 11 (Z_to_bv 64 n)) 12 (Z_to_bv 64 8)) 13 (Z_to_bv 64 (S - 2128))) 14 (Z_to_bv 64 1)) 15 (Z_to_bv 64 1)) 18 (Z_to_bv 64 (U (0x6017c : bv 64)%bv))) 19 (Z_to_bv 64 1)) 20 (Z_to_bv 64 (S - 2128))) 21 (Z_to_bv 64 (S - 81))) 22 (Z_to_bv 64 f22)) 23 (Z_to_bv 64 f23)) 24 (Z_to_bv 64 f24)) (0x3d5f0 : word) (Wn 8 (Wn 8 (Wn 1 M (t + 3168) 0) (S - 2136) (U (0x601e8 : bv 64)%bv)) (S - 2144) S) rom).
Proof.
  intros regs M rom S n t f22 f23 f24 H2 H24 HS HS' Hn Ht Ht' Atsp Hf22 Hf23 Hf24 W Wt C36 C44 C52 C60 C68 C76 C84 C92 C00 C08.
  zsb F_68118 D_68118 (t + 2047 + 1121) 0 ltac:(rewok Wt). replace (t + 2047 + 1121) with (t + 3168) by lia.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (D36 : cellA X (S - 2136) 8 0x601d8) by zcell; assert (D44 : cellA X (S - 2144) 8 S) by zcell; assert (D52 : cellA X (S - 2152) 8 n) by zcell;
    assert (D60 : cellA X (S - 2160) 8 (U (0x6017c : bv 64)%bv)) by zcell; assert (D68 : cellA X (S - 2168) 8 1) by zcell;
    assert (D76 : cellA X (S - 2176) 8 (S - 2128)) by zcell; assert (D84 : cellA X (S - 2184) 8 (S - 81)) by zcell;
    assert (D92 : cellA X (S - 2192) 8 f22) by zcell; assert (D00 : cellA X (S - 2200) 8 f23) by zcell; assert (D08 : cellA X (S - 2208) 8 f24) by zcell end.
  zld F_6811c D_6811c (S - 2136) D36. zld F_68120 D_68120 (S - 2144) D44. zld F_68124 D_68124 (S - 2152) D52. zld F_68128 D_68128 (S - 2160) D60.
  zld F_6812c D_6812c (S - 2168) D68. zld F_68130 D_68130 (S - 2176) D76. zld F_68134 D_68134 (S - 2184) D84. zld F_68138 D_68138 (S - 2192) D92.
  zld F_6813c D_6813c (S - 2200) D00. zld F_68140 D_68140 (S - 2208) D08.
  zstep F_68144 D_68144.
  stepjr F_68148 D_68148 (0x601d8 : bv 64)%bv ltac:(gres; bveq).
  zstep F_601d8 D_601d8. zstep F_601dc D_601dc. zstep F_601e0 D_601e0.
  stepn F_601e4 D_601e4.
  zstep F_3d594 D_3d594.
  zsd F_3d598 D_3d598 (S - 2136) (U (0x601e8 : bv 64)%bv) ltac:(rewok W).
  zsd F_3d59c D_3d59c (S - 2144) S ltac:(rewok W).
  zstep F_3d5a0 D_3d5a0. zstep F_3d5a4 D_3d5a4. zstep F_3d5a8 D_3d5a8. zstep F_3d5ac D_3d5ac. zstep F_3d5b0 D_3d5b0. zstep F_3d5b4 D_3d5b4. zstep F_3d5b8 D_3d5b8.
  stepn F_3d5bc D_3d5bc.
  zret.
Qed.

(* [comment removed for export] *)
Lemma art_ic3_fn : forall regs (M rom : word -> option byte) (raw0 : word) (S ub g16 g24 g32 g40 g48 g56 : Z),
  getr regs 2 = Z_to_bv 64 (S - 2144) -> getr regs 10 = Z_to_bv 64 ub -> 1 <= ub < 2 ^ 64 -> 8192 <= S -> S <= 2 ^ 47 -> ret_ok raw0 ->
  0 <= g16 < 2 ^ 64 -> 0 <= g24 < 2 ^ 64 -> 0 <= g32 < 2 ^ 64 -> 0 <= g40 < 2 ^ 64 -> 0 <= g48 < 2 ^ 64 -> 0 <= g56 < 2 ^ 64 ->
  cellA M (S - 2136) 8 (U (0x601e8 : bv 64)%bv) -> cellA M (S - 2144) 8 S ->
  cellA M (S - 8) 8 (U raw0) -> cellA M (S - 16) 8 g16 -> cellA M (S - 24) 8 g24 -> cellA M (S - 32) 8 g32 -> cellA M (S - 40) 8 g40 ->
  cellA M (S - 48) 8 g48 -> cellA M (S - 56) 8 g56 ->
  msteps ASEGS (mkst regs (0x3d5c0 : word) M rom) (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw0) 2 (Z_to_bv 64 S)) 8 (Z_to_bv 64 g16)) 9 (Z_to_bv 64 g24)) 18 (Z_to_bv 64 g32)) 19 (Z_to_bv 64 g40)) 20 (Z_to_bv 64 g48)) 21 (Z_to_bv 64 g56)) raw0 M rom).
Proof.
  intros regs M rom raw0 S ub g16 g24 g32 g40 g48 g56 H2 H10 Hub HS HS' Hret Hg16 Hg24 Hg32 Hg40 Hg48 Hg56 C36 C44 C8 C16 C24 C32 C40 C48 C56.
  zbft F_3d5c0 D_3d5c0.
  zld F_3d5c4 D_3d5c4 (S - 2136) C36. zld F_3d5c8 D_3d5c8 (S - 2144) C44.
  zstep F_3d5cc D_3d5cc.
  stepjr F_3d5d0 D_3d5d0 (0x601e8 : bv 64)%bv ltac:(gres; bveq).
  zstep F_601e8 D_601e8.
  zld F_601ec D_601ec (S - 8) C8. rewrite Z_to_bv_bv_unsigned.
  zld F_601f0 D_601f0 (S - 16) C16. zld F_601f4 D_601f4 (S - 24) C24. zld F_601f8 D_601f8 (S - 32) C32.
  zld F_601fc D_601fc (S - 40) C40. zld F_60200 D_60200 (S - 48) C48. zld F_60204 D_60204 (S - 56) C56.
  zstep F_60208 D_60208.
  stepret F_6020c D_6020c raw0 ltac:(rwH; reflexivity).
  zret.
Qed.
End FPX.
