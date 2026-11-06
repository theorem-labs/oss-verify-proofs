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
     ArtMem ArtRegs ArtAtomics ArtTac BrtLeaf BrtPoison BrtAllocG BrtUnwind BrtFree1.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import Bo0_code_5fed4_60754 Bo0_code_67fdc_6814c Bo0_code_3d2b4_3e23c Bo0_code_4183c_42d28.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Ltac showst := lazymatch goal with |- msteps _ (mkst ?R ?P ?MM _) _ => idtac "REGS" R; idtac "PC" P; idtac "MEM" MM end; fail "SHOWST".

Section FPX. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
Lemma art_fcu1 : forall regs (M rom : word -> option byte) (raw0 : word) (S p qp tp key tsd ctx t top bot : Z),
  getr regs 1 = raw0 -> getr regs 2 = Z_to_bv 64 S -> getr regs 4 = Z_to_bv 64 tp -> getr regs 10 = Z_to_bv 64 p ->
  0x10007fff8000 + 8192 <= S -> S + 4096 < 2 ^ 47 -> 0 <= p < 2 ^ 47 -> p = 2 ^ 32 * qp + p mod 2 ^ 32 ->
  4096 <= t -> t + 8192 < 2 ^ 47 -> hid (t + 8192 <= 0x10000 \/ 0x634000 <= t) -> apart t 8192 (S - 4096) 8192 ->
  apart ctx 4096 (S - 4096) 8192 -> hid (ctx + 4096 <= 0x10000 \/ 0x634000 <= ctx) -> apart t 8192 ctx 4096 ->
  0x10100 <= tp -> tp + 8 <= 0x634000 -> 0x10000 <= tsd -> tsd + 1024 <= 0x634000 -> 0 <= bot < top -> top < 2 ^ 63 ->
  wrA M (S - 4096) 4096 -> wrA M t 8192 -> art_tsd M tp key tsd ctx t ->
  cellA M 0xdf418 1 1 -> cellA M 0xdf43c 4 30 -> cellA M 0xd64b8 8 0x170268 -> cellA M (0x170268 + 34) 1 1 ->
  cellA M (t + 3168) 1 0 -> cellA M (t + 40) 1 0 -> cellA M (t + 8) 8 top -> cellA M (t + 16) 8 bot ->
  cellA M 0x16e1c8 1 1 -> cellA M (0xdf940 + 8 + 8 * qp) 8 0 ->
  exists regs1 M1,
    msteps ASEGS (mkst regs (0x5fee4 : word) M rom) (mkst regs1 (0x80ab4 : word) M1 rom)
    /\ getr regs1 1 = (0x68118 : bv 64)%bv /\ getr regs1 2 = Z_to_bv 64 (S - 2208) /\ getr regs1 10 = Z_to_bv 64 (S - 2128)
    /\ getr regs1 11 = Z_to_bv 64 0x6001c /\ getr regs1 12 = Z_to_bv 64 S /\ getr regs1 13 = Z_to_bv 64 top /\ getr regs1 14 = Z_to_bv 64 bot
    /\ getr regs1 15 = Z_to_bv 64 30 /\ getr regs1 24 = Z_to_bv 64 (t + 2047) /\ getr regs1 4 = Z_to_bv 64 tp
    /\ (forall r : reg, In r [3; 25; 26; 27]%bv -> getr regs1 r = getr regs r)
    /\ mem_grows M M1
    /\ (forall x : word, ~ (S - 2272 <= U x < S) -> U x <> t + 3168 -> M1 x = M x)
    /\ cellA M1 (S - 8) 8 (U raw0) /\ cellA M1 (S - 16) 8 (U (getr regs 8)) /\ cellA M1 (S - 24) 8 (U (getr regs 9)) /\ cellA M1 (S - 32) 8 (U (getr regs 18))
    /\ cellA M1 (S - 40) 8 (U (getr regs 19)) /\ cellA M1 (S - 48) 8 (U (getr regs 20)) /\ cellA M1 (S - 56) 8 (U (getr regs 21))
    /\ cellA M1 (S - 2136) 8 0x60078 /\ cellA M1 (S - 2144) 8 S /\ cellA M1 (S - 2152) 8 p /\ cellA M1 (S - 2160) 8 (U (0x6001c : bv 64)%bv) /\ cellA M1 (S - 2168) 8 1
    /\ cellA M1 (S - 2176) 8 (S - 2128) /\ cellA M1 (S - 2184) 8 (S - 81)
    /\ cellA M1 (S - 2192) 8 (U (getr regs 22)) /\ cellA M1 (S - 2200) 8 (U (getr regs 23)) /\ cellA M1 (S - 2208) 8 (U (getr regs 24))
    /\ cellA M1 (S - 2128) 8 (S - 2112) /\ cellA M1 (S - 2120) 4 0 /\ cellA M1 (S - 2116) 4 0
    /\ wrA M1 (S - 4096) 4096.
Proof.
  intros regs M rom raw0 S p qp tp key tsd ctx t top bot H1 H2 H4 H10 HS HS' Hp Eqp Ht Ht' Timg Atsp Actx Cimg Atctx Htp0 Htp1 Htsd0 Htsd Hbt Htop
         W Wt TSD Ci Cctx Cg38 Cfast Cunw C40 C8 C16 Cinit Cmap.
  pose proof TSD as (Ttsd1 & Ttsd2 & Ttsd3 & Ttsd4 & Ttsd5 & TR).
  assert (Hqp : 0 <= qp < 2 ^ 15) by (pose proof (Z.mod_pos_bound p (2 ^ 32) ltac:(lia)); lia).
  assert (Hqp' : p / 2 ^ 32 = qp). { symmetry. apply (Z.div_unique_pos _ (2 ^ 32) qp (p mod 2 ^ 32)); [pose proof (Z.mod_pos_bound p (2 ^ 32)); lia|lia]. }
  eexists _, _. split.
  - zstep F_5fee4 D_5fee4.
    zsd F_5fee8 D_5fee8 (S - 8) (U raw0) ltac:(rewok W). zsd F_5feec D_5feec (S - 16) (U (getr regs 8)) ltac:(rewok W).
    zsd F_5fef0 D_5fef0 (S - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_5fef4 D_5fef4 (S - 32) (U (getr regs 18)) ltac:(rewok W).
    zsd F_5fef8 D_5fef8 (S - 40) (U (getr regs 19)) ltac:(rewok W). zsd F_5fefc D_5fefc (S - 48) (U (getr regs 20)) ltac:(rewok W).
    zsd F_5ff00 D_5ff00 (S - 56) (U (getr regs 21)) ltac:(rewok W).
    zstep F_5ff04 D_5ff04. zstep F_5ff08 D_5ff08. zstep F_5ff0c D_5ff0c. zstep F_5ff10 D_5ff10.
    stepn F_5ff14 D_5ff14.
    zcall (art_int_alloc_fn _ _ _ _ (S - 2128)).
    (* [comment removed for export] *)
    stepn F_5ff18 D_5ff18. rwH. rewrite art_zb_srli by lia. rewrite (Z.div_small p (2 ^ 47)) by lia.
    zbft F_5ff1c D_5ff1c.
    stepn F_5ff20 D_5ff20. rwH. rewrite art_zb_srli by lia. rewrite Hqp'.
    stepn F_5ff24 D_5ff24. rwH. rewrite art_zb_slli by lia.
    zstep F_5ff28 D_5ff28.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cmap' : cellA X (0xdf940 + qp * 2 ^ 3 + 8) 8 0) by (replace (0xdf940 + qp * 2 ^ 3 + 8) with (0xdf940 + 8 + 8 * qp) by lia; recell Cmap) end.
    zld F_5ff2c D_5ff2c (0xdf940 + qp * 2 ^ 3 + 8) Cmap'.
    stepfence F_5ff30 D_5ff30.
    zbtk F_5ff34 D_5ff34.
    (* [comment removed for export] *)
    zstep F_5ffbc D_5ffbc. zstep F_5ffc0 D_5ffc0. zstep F_5ffc4 D_5ffc4. zstep F_5ffc8 D_5ffc8. zstep F_5ffcc D_5ffcc.
    zsd F_5ffd0 D_5ffd0 (S - 72) 0 ltac:(rewok W).
    zsd F_5ffd4 D_5ffd4 (S - 2128) (S - 2112) ltac:(rewok W).
    zsd F_5ffd8 D_5ffd8 (S - 2120) 0 ltac:(rewok W). rewrite (Wn8_zero_split _ (S - 2120)) by lia. replace (S - 2120 + 4) with (S - 2116) by lia.
    stepn F_5ffdc D_5ffdc.
    zcall (art_malloc_ctx_fn _ _ _ _).
    zstep F_5ffe0 D_5ffe0.
    zbtk F_5ffe4 D_5ffe4.
    stepn F_60018 D_60018.
    zcall (art_get_pc_fn _ _ _ _).
    zstep F_6001c D_6001c.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cg38' : cellA X 0xd64b8 8 0x170268) by zcell; assert (Cfast' : cellA X (0x170268 + 34) 1 1) by zcell end.
    zld F_60020 D_60020 0xd64b8 Cg38'. zlbu F_60024 D_60024 (0x170268 + 34) Cfast'.
    zstep F_60028 D_60028.
    stepn F_6002c D_6002c.
    zcall (art_malloc_ctx_fn _ _ _ _).
    zstep F_60030 D_60030. zstep F_60034 D_60034. zstep F_60038 D_60038.
    stepn F_6003c D_6003c. rwH. rewrite art_zb_and by lia. rewrite art_land_full_l by lia.
    zstep F_60040 D_60040.
    zsd F_60044 D_60044 (S - 72) S ltac:(rewok W).
    zbtk F_60048 D_60048.
    zstep F_6005c D_6005c. zstep F_60060 D_60060. zstep F_60064 D_60064. zstep F_60068 D_60068. zstep F_6006c D_6006c. zstep F_60070 D_60070.
    stepn F_60074 D_60074.
    (* [comment removed for export] *)
    zstep F_67ffc D_67ffc.
    zsd F_68000 D_68000 (S - 2136) 0x60078 ltac:(rewok W). zsd F_68004 D_68004 (S - 2144) S ltac:(rewok W). zsd F_68008 D_68008 (S - 2152) p ltac:(rewok W).
    zsd F_6800c D_6800c (S - 2160) (U (0x6001c : bv 64)%bv) ltac:(rewok W). zsd F_68010 D_68010 (S - 2168) 1 ltac:(rewok W). zsd F_68014 D_68014 (S - 2176) (S - 2128) ltac:(rewok W).
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
    zcall (art_unwind_fn _ _ _ _ (S - 2208) (S - 2128) 0x6001c S top bot).
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
End FPX.
