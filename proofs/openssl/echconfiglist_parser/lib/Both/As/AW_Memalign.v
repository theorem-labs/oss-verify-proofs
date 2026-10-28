(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics F_memset
     AsDepotInv AsDepotHash AsDepotPut AsUnwind CidBits AW_Combined AW_PoisonShadow AW_Leaves AW_DepotFrame AW_AllocBase AW_Allocate AllocWalkKit.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AW_MallocBase AW_AllocBaseAl AW_AllocateAl AW_MemalignPre AW_MemalignRet AllocTacX. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import LiaGuard.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AllocStoreDj.   (* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_rx8 segs m a bs.   (* [comment removed for export] *)

Section HCWM.
  Context {HCEIL : HeapCeil}.
(* [comment removed for export] *)
Definition memalign_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (W : list ivl) (lo size MP AB U rz csz P cnt mc TH id : Z) (chunks : list Z) (d' : depot) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (j0 j1 j2 j3 : word) (b1 : Z) m1 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch W m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
    /\ stk asegs m1 lo (bv_unsigned sp)
    /\ rw_cells asegs m1 P [C4 (wz (cnt - 1)); C4 (wz mc)]
    /\ u32arr asegs m1 (P + 16) (wlist (rev (tl chunks)))
    /\ stk asegs m1 (P + 16 + 4 * (cnt - 1)) (P + 80)
    /\ rw_cells asegs m1 (TH + 208 + 2560) [C8 j0; C8 j1; C8 j2; C8 j3]
    /\ rw_cells asegs m1 (U + -16) [C1 (b8 2); C1 (b8 b1); C2 (wz 0); C4 (wz size); C8 (wz id)] /\ b1_ok b1
    /\ (rz = 16 \/ (rw_cells asegs m1 AB [C8 (wz kAllocBegMagic); C8 (wz (U + -16))] /\ stk asegs m1 (AB + 16) (U + -16)))
    /\ u8arr asegs m1 U (repeat (b8 0xbe) (Z.to_nat (Z.min size 4096)))
    /\ stk asegs m1 (U + Z.min size 4096) (AB + csz)
    /\ u8arr asegs m1 (sh AB) (alloc_shadow rz size csz)
    /\ stk asegs m1 (TH + 2800) (TH + 3168)
    /\ rw_cells asegs m1 (TH + 3168) [C1 (b8 0)]
    /\ DEPOT asegs d' m1
    (* [comment removed for export] *)
    /\ U mod 64 = 0
    /\ munch [(MP, MP + 8)]%Z m1 m' /\ wmono asegs m1 m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' MP [C8 (wz U)]
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ m' = write_to_mem m1 (wa MP) (le8 (wz U)).   (* [comment removed for export] *)
End HCWM.

Section Icpt.
  Context {HCEIL : HeapCeil}.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo size : Z) (d : depot).
  Variables (TSD CTX TH TOP BOT : Z) (CH : list (Z * Z)).
  Variables (sb cnt mc : Z) (chunks : list Z) (j0 j1 j2 j3 : word).
  Variable MP : Z. Variable pjunk : word.   (* [comment removed for export] *)
  Let CHI := icpt_chain (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned sp) TOP CH.
  Let T := utrace 0x1bfb98 (bv_unsigned sp) TOP BOT 30 CHI.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variables (rz needed c csz csz8 fl CA P cp AB U n id : Z).
  Hypothesis DEFS : hidden (rz = rz_size size /\ needed = round_up (Z.max size 8) 64 + 64 + rz /\ c = class_id needed /\ csz = class_size c
                            /\ csz8 = csz / 8 /\ fl = Z.min size 4096 /\ CA = TH + 208 /\ P = CA + 80 * c /\ cp = hd 0 chunks
                            /\ AB = sb + c * 2^32 + cp * 16 /\ U = AB + rz /\ n = Z.of_nat (length T) /\ id = d_putid d (depot_hash T)).
  Let W : list ivl := (lo, (bv_unsigned sp)) :: (P, P + 4) :: (CA + 2576, CA + 2584) :: (AB, AB + csz) :: (sh AB, sh AB + csz8)
                      :: (TH + 2800, TH + 3169) :: depot_W d.
  Let W2 : list ivl := (lo, (bv_unsigned sp)) :: (P, P + 4) :: (CA + 2576, CA + 2584) :: (AB, AB + csz) :: (sh AB, sh AB + csz8)
                      :: (TH + 2800, TH + 3169) :: nil.
  Hypothesis MPR : 0 <= MP /\ MP + 8 <= 2^64.
  Hypothesis MPDJ : hidden (forall a, MP <= a < MP + 8 -> outside W a).   (* [comment removed for export] *)
  Let POST := memalign_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m W lo size MP AB U rz csz P cnt mc TH id chunks
                          (d_put d (depot_hash T) n).

  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 2544 <= bv_unsigned sp.
  Hypothesis SPA : hidden (bv_unsigned sp mod 16 = 0).
  Hypothesis SPT : hidden (bv_unsigned sp + 16 <= 2^47).
  Hypothesis SZ : 1 <= size /\ needed <= kMaxSize.
  Hypothesis TPR : hidden (12109896 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= AIMG_TOP).
  Hypothesis RNG : hidden (12109808 <= TSD /\ TSD + 8 <= AIMG_TOP /\ aapp CTX 160 /\ CTX + 160 <= aceil /\ akobj TH 4096 /\ TH + 4096 <= aceil /\ TH mod 16 = 0).
  Hypothesis PLC : hidden ((TH + 4096 <= sb \/ sb + kSpaceSize + 4096 <= TH) /\ (CTX + 160 <= sb \/ sb + kSpaceSize + 4096 <= CTX)
                /\ (CTX + 160 <= TH \/ TH + 4096 <= CTX)).
  Hypothesis PLCD : hidden ((TH + 4096 <= d_nb d \/ d_nb d + 16 * 65536 <= TH) /\ (TH + 4096 <= d_sb d \/ d_sb d + 8 * 131072 <= TH)
                /\ (sb + kSpaceSize + 4096 <= d_nb d \/ d_nb d + 16 * 65536 <= sb) /\ (sb + kSpaceSize + 4096 <= d_sb d \/ d_sb d + 8 * 131072 <= sb)
                /\ (CTX + 160 <= d_nb d \/ d_nb d + 16 * 65536 <= CTX) /\ (CTX + 160 <= d_sb d \/ d_sb d + 8 * 131072 <= CTX)
                /\ aapp (d_nb d) (16 * 65536) /\ aapp (d_sb d) (8 * 131072)).
  Let PLACED : Prop := ((TH + 4096 <= sb \/ sb + kSpaceSize + 4096 <= TH) /\ (CTX + 160 <= sb \/ sb + kSpaceSize + 4096 <= CTX)
                /\ (CTX + 160 <= TH \/ TH + 4096 <= CTX))
               /\ ((TH + 4096 <= d_nb d \/ d_nb d + 16 * 65536 <= TH) /\ (TH + 4096 <= d_sb d \/ d_sb d + 8 * 131072 <= TH)
                /\ (sb + kSpaceSize + 4096 <= d_nb d \/ d_nb d + 16 * 65536 <= sb) /\ (sb + kSpaceSize + 4096 <= d_sb d \/ d_sb d + 8 * 131072 <= sb)
                /\ (CTX + 160 <= d_nb d \/ d_nb d + 16 * 65536 <= CTX) /\ (CTX + 160 <= d_sb d \/ d_sb d + 8 * 131072 <= CTX)
                /\ aapp (d_nb d) (16 * 65536) /\ aapp (d_sb d) (8 * 131072)).
  Hypothesis SBR : hidden (AHI_LO <= sb /\ sb + kSpaceSize <= aceil /\ sb mod 65536 = 0).
  Hypothesis CNT : cnt = zlen chunks. Hypothesis HIT : 1 <= cnt <= 16.
  Hypothesis CPS : Forall (fun cp => 0 <= cp < 2^32) chunks.
  Hypothesis ABR : hidden (sb <= AB /\ AB + csz <= sb + kSpaceSize).
  Hypothesis ABA : hidden (AB mod 64 = 0).
  Hypothesis RZ64 : hidden (rz mod 64 = 0).
  Hypothesis TBR : hidden (4096 <= TOP <= 2^47 /\ 0 <= BOT < TOP).
  Hypothesis DCAP : d_ids d + 1 < 65536 /\ d_frames d + 31 <= 131072.
  Hypothesis DLO : d_nb d + 16 * 65536 <= lo /\ d_sb d + 8 * 131072 <= lo.
  (* [comment removed for export] *)
  Hypothesis FCH : goodframe BOT (bv_unsigned sp) TOP = true -> goodframe (bv_unsigned sp) (bv_unsigned s0) TOP = true ->
                   bv_unsigned sp + 16 <= bv_unsigned s0 /\ frame_chain asegs m TOP (bv_unsigned s0) CH.
  (* [comment removed for export] *)
  Hypothesis Ha0 : a0 = wz MP. Hypothesis Ha1 : a1 = wz 64. Hypothesis Ha2 : a2 = wz size.

  Ltac prepI :=
    pose proof DEFS as DEFS'; destruct DEFS' as [(DRZ & DNEED & DC & DCSZ & DC8 & DFL & DCA & DP & DCP & DAB & DU & DN & DID)];
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64)%Z in SPR;
    pose proof (bv_unsigned_in_range _ ra) as RAR; change (bv_modulus 64) with (2^64)%Z in RAR;
    pose proof (bv_unsigned_in_range _ s0) as S0R; change (bv_modulus 64) with (2^64)%Z in S0R;
    assert (BND : aceil <= lo /\ 12109808 <= TSD /\ TSD + 8 <= 12599296 /\ 12599296 <= CTX /\ CTX + 160 <= aceil
               /\ 4096 <= TH /\ TH + 4096 <= aceil /\ 17594333495296 <= sb /\ sb + 137438953472 <= aceil
               /\ sb <= AB /\ AB + csz <= sb + 137438953472 /\ 12109896 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= 12599296
               /\ bv_unsigned sp + 16 <= 140737488355328 /\ 4096 <= TOP /\ TOP <= 140737488355328 /\ 0 <= BOT /\ BOT < TOP)
      by (clear - LO RNG SBR ABR TPR SPT TBR; try acb; destruct RNG as [RNG']; destruct SBR as [SBR']; destruct ABR as [ABR']; destruct TPR as [TPR'];
          destruct SPT as [SPT']; destruct TBR as [TBR']; unfold akobj, alow1, aapp, aapp_lo, aapp_hi, AIMG_LO, ALOWSH_LO in *; unfold AHI_LO, kSpaceSize, AIMG_TOP in *;
          acb; change (2^47)%Z with 140737488355328%Z in SPT', TBR'; lia);
        region_sides; name_bands;
    assert (HC : 1 <= c < 32)
      by (clear - SZ DC DNEED DRZ; try acb; subst c needed rz; apply class_id_range; unfold kMaxSize in SZ; pose proof (rz_size_facts size); unfold round_up in *;
          Z.div_mod_to_equations; lia);
    assert (CSZ : 32 <= csz <= 65536 /\ needed <= csz)
      by (clear - SZ HC DCSZ DNEED DRZ DC; try acb; pose proof (class_size_table_facts c ltac:(hci; lia)); subst csz;
          pose proof (class_size_ge needed ltac:(hci; unfold kMaxSize in SZ; subst needed rz; pose proof (rz_size_facts size); unfold round_up in *;
                                             Z.div_mod_to_equations; lia)); subst c; lia);
    assert (RZB : 16 <= rz <= 2048 /\ size + rz + 64 <= needed /\ 8 + rz <= needed /\ needed < size + rz + 128)
      by (clear - SZ DNEED DRZ; try acb; subst needed rz; pose proof (rz_size_facts size); unfold round_up; Z.div_mod_to_equations; lia);
    assert (ALN : exists thq sbq rzk ck nk, TH = 16 * thq /\ sb = 65536 * sbq /\ rz = 16 * rzk /\ csz = 32 * ck /\ needed - rz = 8 * nk)
      by (clear - RNG SBR HC DCSZ DNEED DRZ; try acb; destruct RNG as [RNG']; destruct SBR as [SBR']; pose proof (rz_size_facts size);
          pose proof (class_size_table_facts c ltac:(hci; lia)); subst csz needed rz; unfold round_up;
          exists (TH / 16), (sb / 65536), (rz_size size / 16), (class_size c / 32), ((size `max` 8 + 64 - 1) / 64 * 8 + 8);
          Z.div_mod_to_equations; lia);
    destruct ALN as (thq & sbq & rzk & ck & nk & ALN);
    assert (SPQ : exists spq, bv_unsigned sp = 16 * spq) by (clear - SPA; try acb; destruct SPA as [SPA']; exists (bv_unsigned sp / 16); Z.div_mod_to_equations; lia);
    destruct SPQ as [spq SPQ];
    assert (PLCh : hidden PLACED) by (destruct PLC as [PLC']; destruct PLCD as [PLCD']; exact (Hide _ (conj PLC' PLCD')));
    assert (EQS : U = AB + rz /\ P = TH + 208 + 80 * c /\ AB = sb + c * 2 ^ 32 + cp * 16 /\ n = Z.of_nat (length T) /\ CA = TH + 208)
      by (rewrite DU, DP, DAB, DN, DCA; repeat split; reflexivity);
    assert (EQh : hidden (c = class_id needed /\ csz = class_size c /\ rz = rz_size size /\ needed = round_up (Z.max size 8) 64 + 64 + rz
                       /\ cp = hd 0 chunks /\ id = d_putid d (depot_hash T) /\ T = utrace 0x1bfb98 (bv_unsigned sp) TOP BOT 30 CHI
                       /\ CHI = icpt_chain (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned sp) TOP CH /\ csz8 = csz / 8)) by (constructor; repeat split; first [assumption | reflexivity]);
    assert (C8F : 8 * csz8 = csz) by (clear - ALN DC8; try acb; subst csz8; Z.div_mod_to_equations; lia);
    assert (PB : TH + 288 <= P /\ P + 80 <= TH + 2768) by (clear - HC EQS; try acb; lia);
    assert (SHR : 2201439137792 <= sh AB /\ sh AB + csz8 <= 17594333495296) by (clear - BND C8F; try acb; unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia);
    assert (NR : 1 <= n <= 30) by (rewrite DN; unfold T; apply utrace_length; lia);
    clear DRZ DNEED DC DCSZ DC8 DFL DCA DP DCP DAB DU DN DID.

  Ltac plia :=
    first [ lia
          | match goal with H : hidden PLACED |- _ =>
              let P := fresh "PLu" in pose proof H as P; destruct P as [P]; unfold PLACED, kSpaceSize, AHI_LO in P;
              let A1 := fresh "PA" in let A2 := fresh "PA" in let A3 := fresh "PA" in
              let B1 := fresh "PB" in let B2 := fresh "PB" in let B3 := fresh "PB" in let B4 := fresh "PB" in
              let B5 := fresh "PB" in let B6 := fresh "PB" in let B7 := fresh "PB" in let B8 := fresh "PB" in
              destruct P as [[A1 [A2 A3]] [B1 [B2 [B3 [B4 [B5 [B6 [B7 B8]]]]]]]];
              first [ clear A2 A3 B1 B2 B3 B4 B5 B6; lia
                    | clear A1 A3 B1 B2 B3 B4 B5 B6; lia
                    | clear A1 A2 B1 B2 B3 B4 B5 B6; lia
                    | clear A1 A2 A3 B2 B3 B4 B5 B6; lia
                    | clear A1 A2 A3 B1 B3 B4 B5 B6; lia
                    | clear A1 A2 A3 B1 B2 B4 B5 B6; lia
                    | clear A1 A2 A3 B1 B2 B3 B5 B6; lia
                    | clear A1 A2 A3 B1 B2 B3 B4 B6; lia
                    | clear A1 A2 A3 B1 B2 B3 B4 B5; lia ]
            end ].
  Ltac solve_depot_avoid ::=
    unfold depot_avoid, avoids; rewrite ?d_nb_put, ?d_sb_put; cbn [fst snd];
    repeat split;
    repeat (first [apply Forall_nil | apply Forall_cons; [cbn beta iota delta [fst snd]; plia |]]).
  (* [comment removed for export] *)
  Ltac dlia := lazymatch goal with |- _ <= _ \/ _ <= _ => lia | |- _ \/ _ => first [ left; dlia | right; dlia ] | |- _ /\ _ => split; dlia | |- _ => lia end.
  Ltac splia := lazymatch goal with |- _ /\ _ => split; splia | |- _ => plia end.
  Ltac slia ::= first [ exact I | dlia | splia ].

  (* [comment removed for export] *)
  Theorem memalign_spec :
    IENV tp TSD CTX TH sb TOP BOT m -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) ->
    rw_cells asegs m P [C4 (wz cnt); C4 (wz mc)] -> rw_cells asegs m (P + 8) [C8 (wz csz)] -> u32arr asegs m (P + 16) (wlist (rev chunks)) ->
    stk asegs m (P + 16 + 4 * cnt) (P + 80) -> rw_cells asegs m (TH + 208 + 2560) [C8 j0; C8 j1; C8 j2; C8 j3] ->
    stk asegs m AB (AB + csz) ->
    u8arr asegs m (sh AB) (repeat (b8 0xfa) (Z.to_nat csz8)) ->
    stk asegs m (TH + 2800) (TH + 3168) -> rw_cells asegs m (TH + 3168) [C1 (b8 0)] ->
    DEPOT asegs d m ->
    rw_cells asegs m MP [C8 pjunk] ->
    evt asegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1bfaf8) fc None m (seg_rom asegs)).
  Proof.
    intros ENV MI ST QC1 QC2 QC3 QC4 QST CHUNK SHK TST UNW DEP PW.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold W in MU. prepI.
    assert (LENC : Z.of_nat (length (wlist (rev chunks))) = cnt) by (clear - CNT; try acb; unfold wlist; rewrite length_map, length_rev; unfold zlen in CNT; lia).
    assert (SHKL : Z.of_nat (length (repeat (b8 250) (Z.to_nat csz8))) = csz8) by (rewrite repeat_length; lia).
    (* [comment removed for export] *)
    assert (PWh : hidden (rw_cells asegs m MP [C8 pjunk])) by (constructor; exact PW). clear PW.
    (* [comment removed for export] *)
    callD (memalign_pre ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo size d TSD CTX TH TOP BOT CH sb MP).
    all: rewrite ?unsigned_lit by lia.
    all: try first [exact LO | exact HI | exact SPA | exact SPT | exact TPR | exact RNG | exact PLC | exact PLCD | exact TBR | exact DLO | exact FCH
                    | exact Ha0 | exact Ha1 | exact Ha2 | exact ENV | exact MI | exact ST | exact UNW | exact DEP].
    all: try (clear - SZ; try acb; unfold kMaxSize in SZ; lia).
    all: try (clear - MPR; try acb; lia).
    repeat match goal with H : context [utrace 0x1bfb98 _ _ _ _ _] |- _ => progress (fold CHI in H; fold T in H) end.
    lazymatch goal with H : IENV _ _ _ _ _ _ _ ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into ENV1 end.
    lazymatch goal with H : munch _ m ?mm, H2 : wmono asegs m ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into MU1; rename H2 into WM1 end.
    (* [comment removed for export] *)
    pose proof ENV1 as E. open_ienv E.
    lazymatch goal with H : u64arr asegs ?mm (bv_unsigned sp + -2144 + 16) (map wz T ++ ?rest) |- _ =>
      assert (AE : AENV tp TSD CTX TH sb (bv_unsigned sp + -2144) T rest mm)
        by (econstructor; try eassumption) end.
    clear Etsdi Etp Etsd Ectx Elsan Egot2 Ethr Etid Einit Eafl Ecan Egot Eshb Ehme Ethresh Erms Efill Epart Ehooks Einst1 Einst2 Emcs Epsc Ecfu Estk Et40.
    (* [comment removed for export] *)
    unfold depot_W in MU1.
    lazymatch goal with H : AENV tp TSD CTX TH sb _ T ?rest ?mm |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut; [ eapply (allocate_spec _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mm lo size (bv_unsigned sp + -2144)
         T rest d TSD CTX TH sb cnt mc chunks j0 j1 j2 j3 rz needed c csz csz8 fl CA P cp AB U n id) | post_callA segs mm ] end.
    all: rewrite ?unsigned_lit by (first [clear - BND HI; lia | lia]).
    all: try exact DEFS. all: try exact ABA. all: try exact RZ64. all: try eassumption. all: try reflexivity. all: try (lia_guard; lia).
    all: try (constructor; (first [clear - SPQ BND HI; lia | lia])).
    destruct EQS as (EU & EP & EAB & En & ECA).
    assert (UR : 1 <= U < 2^64) by (clear - EU BND CSZ RZB; try acb; lia).
    assert (UA : U mod 64 = 0) by (clear - EU ABA RZ64; destruct ABA as [ABA'], RZ64 as [RZ64']; rewrite EU; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    lazymatch goal with MUq : munch _ m ?mm, WMq : wmono asegs m ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct PWh as [PW];
      assert (PW' : rw_cells asegs mm MP [C8 pjunk])
        by (assert (AGq : agree_on (outside W) m mm) by (intros xa Pa Ra; unfold W, depot_W in Pa; pose proof (MUq (wa xa)) as E; rewrite wa_unsigned in E by exact Ra; exact (E Pa));
            eapply (rw_cells_transport_pt _ _ _ AGq WMq); [exact PW|]; change (Z.of_nat (cells_size [C8 pjunk])) with 8;
            destruct MPDJ as [MPDJ']; exact MPDJ');
      clear PW end.
    (* [comment removed for export] *)
    destruct SPT as [SPT'].
    try lazymatch goal with |- evt ?segs _ (MS _ _ (ret_pc ?r) _ _ ?mm _) =>
      replace (ret_pc r) with (Z_to_bv 64 0x197ac4) by (apply bv_eq; vm_compute; reflexivity) end.
    lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut; [ eapply (memalign_ret sp ra s0 s1 s2 s3 s4 s5 s6 s7); try eassumption; try exact UR; try exact UA |] end.
    all: try (clear - HI; try acb; lia).
    all: try (destruct MPDJ as [MPDJ']; pose proof (MPDJ' MP ltac:(clear - MPR; lia)) as D0; pose proof (MPDJ' (MP + 7) ltac:(clear - MPR; lia)) as D7;
              unfold W in D0, D7; cbn [outside] in D0, D7; clear - MPR D0 D7 HI; try acb; lia).
    { clear - PC10 POST0; split; assumption. }
    cbv beta. intros ms' PO3. destruct PO3 as (m' & -> & MU3 & WM3 & MI3 & PW3 & ST3 & ST1 & EQM).
    apply evt_done. unfold POST, memalign_post.
    lazymatch goal with H : rw_cells asegs ?m1 (TH + 208 + 2560) [C8 ?a; C8 ?b; C8 ?cc; C8 ?dd], H1 : b1_ok ?e |- _ =>
      do 14 eexists; exists a, b, cc, dd, e, m1, m' end.
    split; [reflexivity|].
    split. { lazymatch goal with MUq : munch _ m _ |- _ => unfold depot_W; exact MUq end. }
    repeat match goal with |- _ /\ _ => split end; try assumption.
  Qed.
End Icpt.
