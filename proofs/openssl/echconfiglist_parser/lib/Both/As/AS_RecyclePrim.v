(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import SReach AllocSim MmapSim LazyRestrict LazyLedger LazySR LazyNodes AsanAllocModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics F_memset
     AW_PoisonShadow AW_Leaves AllocWalkKit AW_MmapFixed AW_Efs AW_Populate AW_Gfa AW_LargeAlloc1 SecLazy AS_Refill1 AS_Refill2 AS_Refill3
     AW_Rta1 AW_MaybeRelease AW_Rta2 AS_Rta AW_LcDealloc AS_LcDealloc AW_RecyclePrim AllocTacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import PerfLia. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import LiaGuard.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

(* [comment removed for export] *)
Definition rp_W (lo sp p mhdr u nu TH : Z) : list ivl :=
  [(lo, sp); (p, p + 8); (mhdr, mhdr + 4); (sh u, sh u + round_up nu 8 / 8); (TH + 2840, TH + 2856)]%Z.

(* [comment removed for export] *)
Definition recycle_prim_post (L S Zr : list (word * word)) (mo : Model)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo c P CA R rbeg FAB TH TSD CTX sb ARI p mhdr u rz nu actx b1 cnt mc nf mfa au mu : Z) (chunks fl : list Z) (q0 q1 q3 : word) (drained : bool)
    (msF' : machine_state) (mo' : Model) : Prop :=
  let n := mc / 2 in
  let k := (if drained then n else 0) in
  let cnt1 := cnt - k in
  let nf' := nf + k in
  let mfa' := (if drained then rta_mfa nf n mfa else mfa) in
  let kept := skipn (Z.to_nat k) chunks in
  let moved := firstn (Z.to_nat k) chunks in
  exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 q2 : word) m' L' S',
     lzok asegs L' S' Zr (mkCfg msF' mo')
  /\ restrict L' S' msF'
     = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom asegs)
  /\ rf_ledger mo L S rbeg FAB mu mu mfa mfa' L' S' mo'
  /\ munch (rp_W lo (bv_unsigned sp) p mhdr u nu TH ++ lcd_W lo (bv_unsigned sp) P CA cnt1 R FAB TH nf mfa mfa') m m' /\ wmono asegs m m' /\ mem_inv asegs m'
  /\ RENV tp TSD CTX TH sb ARI m'
  /\ stk asegs m' lo (bv_unsigned sp)
  (* [comment removed for export] *)
  /\ rw_cells asegs m' mhdr [C1 (b8 0); C1 (b8 b1); C2 (wz 0); C4 (wz nu); C8 (wz actx)]
  /\ (rz = 16 \/ (32 <= rz /\ rw_cells asegs m' p [C8 (wz 0); C8 (wz mhdr)]))
  /\ poisoned m' u (Z.to_nat (round_up nu 8 / 8)) kAsanHeapLeftRedzoneMagic
  (* [comment removed for export] *)
  /\ rw_cells asegs m' P [C4 (wz (cnt1 + 1)); C4 (wz mc)]
  /\ u32arr asegs m' (P + 16) (wlist (rev (Z.shiftr (p - rbeg) kCompactPtrScale :: kept)))
  /\ stk asegs m' (P + 16 + 4 * (cnt1 + 1)) (P + 80)
  /\ rw_cells asegs m' (TH + 2768) [C8 q0; C8 q1; C8 q2; C8 q3] /\ stk asegs m' (TH + 2800) (TH + 3168)
  (* [comment removed for export] *)
  /\ rw_cells asegs m' R [C8 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz nf'); C8 (wz mfa'); C8 (wz au); C8 (wz 0); C8 (wz mu); C8 (wz 0)]
  /\ stk asegs m' (R + 69) (R + 128)
  /\ u32arr asegs m' FAB (wlist (rev (moved ++ fl))) /\ stk asegs m' (FAB + 4 * nf') (FAB + mfa')
  /\ poisoned m' (FAB + mfa) (Z.to_nat ((mfa' - mfa) / 8)) 0xfa.
End HCW.

Section RecyclePrim.
  Context {HCEIL : HeapCeil}.
  Local Unset Keyed Unification.
  Variables (L S Zr : list (word * word)) (msF : machine_state) (mo : Model) (Q : config -> Prop).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  (* [comment removed for export] *)
  Variables (lo sb c TH CTX TSD cb : Z).
  (* [comment removed for export] *)
  Variables (idx rz nu actx b1 : Z).
  (* [comment removed for export] *)
  Variables (cnt mc csz : Z) (chunks : list Z) (q0 q1 q2 q3 : word).
  Variables (nf mfa au mu : Z) (fl : list Z).
  Let CA := TH + 208.
  Let P := CA + PCLASS_SIZE * c.
  Let ARI := sb + kSpaceSize.
  Let R := ARI + REGIONINFO_SIZE * c.
  Let rbeg := sb + c * 2^32.
  Let FAB := rbeg + kFreeArrayOffset.
  Let p := rbeg + idx * class_size c.
  Let u := p + rz.
  Let mhdr := u - 16.
  Let n := mc / 2.

  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 688 <= bv_unsigned sp. Hypothesis SPT : bv_unsigned sp + 16 <= 2^47.
  Hypothesis SPA : hidden (bv_unsigned sp mod 16 = 0).
  Hypothesis HC : 1 <= c < kNumClasses.
  Hypothesis SBR : AHI_LO <= sb /\ sb + kSpaceSize + kPageSize <= aceil. Hypothesis SBA : hidden (sb mod 65536 = 0).
  Hypothesis TPR : 12109896 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= AIMG_TOP.
  Hypothesis RNG : 12109808 <= TSD /\ TSD + 8 <= AIMG_TOP /\ aapp CTX 160 /\ CTX + 160 <= aceil /\ akobj TH 4096 /\ TH + 4096 <= aceil.
  Hypothesis THA : hidden (TH mod 16 = 0).
  Hypothesis PLC : hidden ((TH + 4096 <= sb \/ sb + kSpaceSize + 4096 <= TH) /\ (CTX + 160 <= sb \/ sb + kSpaceSize + 4096 <= CTX)
                           /\ (CTX + 160 <= TH \/ TH + 4096 <= CTX)).
  (* [comment removed for export] *)
  Hypothesis IDX : 0 <= idx /\ (idx + 1) * class_size c <= mu /\ mu <= kFreeArrayOffset - kUserMapSize.
  Hypothesis RZA : hidden (rz mod 16 = 0).
  Hypothesis NUR : 1 <= nu /\ rz + round_up nu 8 <= class_size c.
  Hypothesis B1 : b1 = 17 \/ b1 = 145 \/ b1 = 65 \/ b1 = 193.
  (* [comment removed for export] *)
  Hypothesis CBR : bv_unsigned sp <= cb /\ cb + 8 <= 2^63.
  (* [comment removed for export] *)
  Hypothesis MCR : 2 <= mc <= 16. Hypothesis CNT : cnt = zlen chunks. Hypothesis CB : 0 <= cnt <= mc. Hypothesis CSZ : 0 <= csz < 2^64.
  (* [comment removed for export] *)
  Hypothesis NFR : 0 <= nf /\ 4 * nf <= mfa /\ mfa <= kFreeArraySize /\ 4 * (nf + n) <= kFreeArraySize. Hypothesis MFAA : hidden (mfa mod kFreeArrayMapSize = 0).
  Hypothesis AUR : 0 <= au <= mu /\ mu + kUserMapSize <= kFreeArrayOffset.
  Hypothesis FLL : length fl = Z.to_nat nf.
  (* [comment removed for export] *)
  Hypothesis OK : lzok asegs L S Zr (mkCfg msF mo).
  Hypothesis VISE : restrict L S msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz cb) (wz mhdr) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                        F (Z_to_bv 64 0x199214) fc None m (seg_rom asegs).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis ENV : RENV tp TSD CTX TH sb ARI m.
  Hypothesis CBC : rw_cells asegs m cb [C8 (wz CA)].
  Hypothesis HDR : rw_cells asegs m mhdr [C1 (b8 3); C1 (b8 b1); C2 (wz 0); C4 (wz nu); C8 (wz actx)].
  Hypothesis MAG : rz = 16 \/ (32 <= rz /\ rw_cells asegs m p [C8 (wz 0xCC6E96B9CC6E96B9); C8 (wz mhdr)]).
  Hypothesis SHU : poisoned m u (Z.to_nat (round_up nu 8 / 8)) kAsanHeapFreeMagic.
  Hypothesis PC1 : rw_cells asegs m P [C4 (wz cnt); C4 (wz mc)].
  Hypothesis PC2 : rw_cells asegs m (P + 8) [C8 (wz csz)].
  Hypothesis PC3 : u32arr asegs m (P + 16) (wlist (rev chunks)).
  Hypothesis PC4 : stk asegs m (P + 16 + 4 * cnt) (P + 80).
  Hypothesis QST : rw_cells asegs m (TH + 2768) [C8 q0; C8 q1; C8 q2; C8 q3].
  Hypothesis TST : stk asegs m (TH + 2800) (TH + 3168).
  Hypothesis RI : rw_cells asegs m R [C8 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz nf); C8 (wz mfa); C8 (wz au); C8 (wz 0); C8 (wz mu); C8 (wz 0)].
  Hypothesis RST : stk asegs m (R + 69) (R + 128).
  Hypothesis FARR : u32arr asegs m FAB (wlist (rev fl)).
  Hypothesis FAJ : stk asegs m (FAB + 4 * nf) (FAB + mfa).
  (* [comment removed for export] *)
  Hypothesis RESF : forall (a k : word), AHI_LO <= bv_unsigned a -> region_free (vm_reserved (m_vmmaps mo)) a k = true.
  Hypothesis PRIM : forall (a k : word), rbeg <= bv_unsigned a -> bv_unsigned a + bv_unsigned k <= rbeg + 2^32 -> map_contains (vm_maps (m_vmmaps mo)) a k = true.
  Hypothesis NW : entries_nowrap (vm_maps (m_vmmaps mo)). Hypothesis NWA : entries_nowrap (vm_noaccess (m_vmmaps mo)).
  Hypothesis NOV : nooverlap (vm_maps (m_vmmaps mo)).
  Hypothesis ZRP : forall x : word, rbeg <= bv_unsigned x < rbeg + 2^32 -> in_rangesb x Zr = false.
  Hypothesis ZRSH : forall x : word, sh AHI_LO <= bv_unsigned x < sh aceil -> in_rangesb x Zr = true.
  Hypothesis LSH : forall x : word, sh AHI_LO <= bv_unsigned x < sh aceil -> in_rangesb x L = true.
  Hypothesis SVIS : forall x : word, in_rangesb x S = true -> wview asegs m x <> None.
  Hypothesis BUD : cnt < mc \/ 4 * (nf + n) <= mfa \/ eager_used mo + pages_total S * 4096 + 303104 <= vm_limit (m_vmmaps mo).
  (* [comment removed for export] *)
  Hypothesis ATOP : alloc_top (m_vmmaps mo) = hceil.

  Theorem recycle_prim_sreach :
    (forall msF' mo', recycle_prim_post L S Zr mo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo c P CA R rbeg FAB TH TSD CTX sb ARI p mhdr u rz nu actx b1
                        cnt mc nf mfa au mu chunks fl q0 q1 q3 (cnt =? mc) msF' mo' -> sreach asegs Q (mkCfg msF' mo')) ->
    sreach asegs Q (mkCfg msF mo).
  Proof.
    intros K.
    unfold kFreeArraySize, kFreeArrayMapSize, kUserMapSize, kFreeArrayOffset, kNumClasses in NFR, AUR, HC, IDX.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
    pose proof (class_size_table_facts c ltac:(hci; clear - HC; try acb; tlia)) as CST. destruct CST as (CS1 & CS2 & CS3 & _).
    assert (LFL : length (wlist (rev fl)) = Z.to_nat nf) by (rewrite wlist_length, length_rev; exact FLL).
    assert (LCH : length (wlist (rev chunks)) = Z.to_nat cnt) by (rewrite wlist_length, length_rev; unfold zlen in CNT; clear - CNT; try acb; tlia).
    assert (BND : aceil <= lo /\ 12109808 <= TSD /\ TSD + 8 <= 12599296 /\ 12599296 <= CTX /\ CTX + 160 <= aceil
               /\ 4096 <= TH /\ TH + 4096 <= aceil /\ 17594333495296 <= sb /\ sb + 137438953472 + 4096 <= aceil
               /\ 12109896 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= 12599296 /\ bv_unsigned sp + 16 <= 140737488355328)
      by (clear - LO RNG SBR TPR SPT; try acb; unfold akobj, alow1, aapp, aapp_lo, aapp_hi, AIMG_LO, ALOWSH_LO in *; unfold AHI_LO, kSpaceSize, kPageSize, AIMG_TOP in *; acb; aunf; tlia).
    region_sides. name_bands.
    assert (GEO : R = sb + 137438953472 + 128 * c /\ rbeg = sb + c * 4294967296 /\ FAB = rbeg + 3758096384 /\ ARI = sb + 137438953472 /\ P = CA + 80 * c /\ CA = TH + 208
                  /\ p = rbeg + idx * class_size c /\ u = p + rz /\ mhdr = u - 16)
      by (subst R rbeg FAB ARI P CA p u mhdr; unfold kSpaceSize, REGIONINFO_SIZE, kFreeArrayOffset, PCLASS_SIZE; repeat split; reflexivity).
    destruct GEO as (ER & ERB & EFAB & EARI & EP & ECA & EPP & EU & EM).
    assert (ICZ : 0 <= idx * class_size c) by (clear - IDX CS1; try acb; nia).
    assert (IDX' : idx * class_size c + class_size c <= mu) by (clear - IDX; try acb; nia).
    assert (RU8 : nu <= round_up nu 8 < nu + 8 /\ round_up nu 8 mod 8 = 0) by (unfold round_up; clear - NUR; try acb; Z.div_mod_to_equations; tlia).
    assert (RZ : rz = 16 \/ 32 <= rz) by (clear - MAG; try acb; tauto).
    assert (PB : sb + c * 4294967296 <= p /\ p + class_size c <= sb + c * 4294967296 + mu /\ p + 16 <= u /\ u + round_up nu 8 <= p + class_size c)
      by (rewrite EU, EPP, ERB; clear - IDX IDX' ICZ NUR RZ CS1 HC; try acb; repeat split; tlia).
    assert (BNDC : 17594333495296 <= p /\ p + 32 <= aceil /\ 17594333495296 <= mhdr /\ mhdr + 16 <= aceil /\ 17594333495296 <= u /\ u + 8 <= aceil
                   /\ bv_unsigned sp <= cb /\ cb + 8 <= 2^63 /\ sb + 137438953472 + 128 <= R /\ R + 128 <= sb + 137438953472 + 4096 /\ TH + 288 <= P /\ P + 80 <= TH + 2768
                   /\ p + 32 <= sb + c * 4294967296 + mu /\ c * 4294967296 + 4294967296 <= 137438953472)
      by (rewrite EM; clear - PB BND HC CS1 CS3 CBR RU8 NUR IDX ER EP ECA; try acb; rewrite ER, EP, ECA; repeat split; (first [clear - HC BND PB ACEILB IDX CS3 NUR RU8 CBR; nia | nia])).
    assert (SHR : 2148314624 <= sh u /\ sh u + round_up nu 8 / 8 + 8 <= 17594333495296) by (unfold sh, ASHADOW_BASE; clear - BNDC PB RU8 NUR HC CS1; try acb; Z.div_mod_to_equations; tlia).
    pose proof (I : region_rank (sh u) 1) as RXRsh.
    pose proof (re_senv _ _ _ _ _ _ _ ENV) as SEN. pose proof (re_isb _ _ _ _ _ _ _ ENV) as ISB. pose proof (re_iri _ _ _ _ _ _ _ ENV) as IRI.
    (* [comment removed for export] *)
    eapply (evt_sreach_lazy_at asegs L S Zr _ msF _ mo Q OK VISE).
    { eapply (recycle_prim1 ra sp gp tp t0 t1 t2 s0 s1 _ _ a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                lo sb c CA cb p rz nu actx b1 idx au mu TSD CTX TH ARI nf mfa MI ST LO); try reflexivity; try eassumption.
      all: try (clear - HI; try acb; tlia). destruct SBA as [S64]. split. clear - S64; try acb. Z.div_mod_to_equations. tlia. }
    clear OK VISE. cbv beta. intros msF1 mo1 OK1 SBM1 HS1 P1.
    destruct P1 as (x5 & x6 & x7 & y4 & y5 & y6 & y7 & x28 & x29 & x30 & x31 & m1 & VIS1 & MU1 & WM1 & MI1 & ST1 & HDR1 & MAG1 & POI1 & TST1).
    change (p + rz - 16) with mhdr in MU1, HDR1, MAG1. change (p + rz) with u in MU1, POI1.
    clear MI ST HDR MAG SHU TST CBC SEN ISB IRI.
    (* [comment removed for export] *)
    assert (DJ : forall A len, A + len <= aceil -> (17594333495296 <= A \/ A + len <= 2147446784) -> (A + len <= p \/ p + class_size c <= A) ->   (* [comment removed for export] *)
                 (A + len <= TH + 2840 \/ TH + 2856 <= A) ->
                 disjoint_from [(bv_unsigned sp - 112, bv_unsigned sp); (p, p + 8); (mhdr, mhdr + 4); (sh u, sh u + round_up nu 8 / 8); (TH + 2840, TH + 2856)]%Z A len).
    { intros A len D3 D4 D2 D5. cbn [disjoint_from]. clear - D2 D3 D4 D5 BNDC SHR BND HI PB CS3 HC EM EU RU8 NUR; try acb. repeat split; (first [clear - HI HC BND D3 ACEILB CS3 D2 NUR RU8 PB SHR D4 D5; tlia | tlia]). }
    Ltac trm H DJ MU1 WM1 :=
      first [ eapply rw_cells_transport in H; [| exact MU1| exact WM1| apply DJ; cbn [cells_size csize length Nat.add Nat.mul]]
            | eapply u32arr_transport in H; [| exact MU1| exact WM1| apply DJ]
            | eapply stk_transport_disjoint in H; [| exact MU1| exact WM1| apply DJ] ].
    pose proof PLC as PLCx. destruct PLCx as [PLCq]. unfold kSpaceSize in PLCq.
    trm PC1 DJ MU1 WM1. all: try lazymatch goal with |- sreach _ _ _ => fail | |- _ => (rewrite ?LCH, ?LFL; match goal with TB : akobj TH 4096 |- _ => clear - BND BNDC HC PLCq PB CS1 CS3 IDX CB MCR NFR ER EFAB ERB EP ECA EM EU TB end; try acb; aunf; (first [clear - HC MCR BND EP BNDC PLCq ACEILB IDX THB ER CS3; tlia | tlia])) end.
    trm PC2 DJ MU1 WM1. all: try lazymatch goal with |- sreach _ _ _ => fail | |- _ => (rewrite ?LCH, ?LFL; match goal with TB : akobj TH 4096 |- _ => clear - BND BNDC HC PLCq PB CS1 CS3 IDX CB MCR NFR ER EFAB ERB EP ECA EM EU TB end; try acb; aunf; tlia) end.
    trm PC3 DJ MU1 WM1. all: try lazymatch goal with |- sreach _ _ _ => fail | |- _ => (rewrite ?LCH, ?LFL; match goal with TB : akobj TH 4096 |- _ => clear - BND BNDC HC PLCq PB CS1 CS3 IDX CB MCR NFR ER EFAB ERB EP ECA EM EU TB end; try acb; aunf; (first [clear - HC MCR CB BND EP BNDC PLCq ACEILB IDX THB ER CS3; tlia | tlia])) end.
    trm PC4 DJ MU1 WM1. all: try lazymatch goal with |- sreach _ _ _ => fail | |- _ => (rewrite ?LCH, ?LFL; match goal with TB : akobj TH 4096 |- _ => clear - BND BNDC HC PLCq PB CS1 CS3 IDX CB MCR NFR ER EFAB ERB EP ECA EM EU TB end; try acb; aunf; tlia) end.
    trm QST DJ MU1 WM1. all: try lazymatch goal with |- sreach _ _ _ => fail | |- _ => (rewrite ?LCH, ?LFL; match goal with TB : akobj TH 4096 |- _ => clear - BND BNDC HC PLCq PB CS1 CS3 IDX CB MCR NFR ER EFAB ERB EP ECA EM EU TB end; try acb; aunf; tlia) end.
    trm RI DJ MU1 WM1. all: try lazymatch goal with |- sreach _ _ _ => fail | |- _ => (rewrite ?LCH, ?LFL; match goal with TB : akobj TH 4096 |- _ => clear - BND BNDC HC PLCq PB CS1 CS3 IDX CB MCR NFR ER EFAB ERB EP ECA EM EU TB end; try acb; aunf; tlia) end.
    trm RST DJ MU1 WM1. all: try lazymatch goal with |- sreach _ _ _ => fail | |- _ => (rewrite ?LCH, ?LFL; match goal with TB : akobj TH 4096 |- _ => clear - BND BNDC HC PLCq PB CS1 CS3 IDX CB MCR NFR ER EFAB ERB EP ECA EM EU TB end; try acb; aunf; tlia) end.
    trm FARR DJ MU1 WM1. all: try lazymatch goal with |- sreach _ _ _ => fail | |- _ => (rewrite ?LCH, ?LFL; match goal with TB : akobj TH 4096 |- _ => clear - BND BNDC HC PLCq PB CS1 CS3 IDX CB MCR NFR ER EFAB ERB EP ECA EM EU TB end; try acb; aunf; (first [clear - HC MCR NFR BND EFAB BNDC PLCq ACEILB IDX ER; tlia | tlia])) end.
    trm FAJ DJ MU1 WM1. all: try lazymatch goal with |- sreach _ _ _ => fail | |- _ => (rewrite ?LCH, ?LFL; match goal with TB : akobj TH 4096 |- _ => clear - BND BNDC HC PLCq PB CS1 CS3 IDX CB MCR NFR ER EFAB ERB EP ECA EM EU TB end; try acb; aunf; tlia) end.
    assert (ENV1 : RENV tp TSD CTX TH sb ARI m1).
    { eapply (renv_transport tp TSD CTX TH sb ARI m m1 _ ENV MU1 WM1); apply DJ; match goal with TB : akobj TH 4096, TC : aapp CTX 160 |- _ => clear - BND BNDC HC PLCq PB CS1 IDX TB TC end; try acb; aunf; (first [clear - ACEILB BNDC THB BND ACEILB0 CTB HC IDX CS1 PLCq; tlia | tlia]). }
    clear ENV.
    eapply (munch_weaken _ (rp_W lo (bv_unsigned sp) p mhdr u nu TH ++ lcd_W lo (bv_unsigned sp) P CA (cnt - (if cnt =? mc then n else 0)) R FAB TH nf mfa (if cnt =? mc then rta_mfa nf n mfa else mfa)))
      in MU1; [| unfold rp_W, lcd_W; cbn [app]; rx_sub_fp_struct].
    (* [comment removed for export] *)
    eapply (cache_dealloc_sreach L S Zr msF1 mo1 Q ra sp gp tp _ _ _ s0 s1 _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 lo sb c TH CTX TSD p cnt mc csz chunks q0 q1 q2 q3 nf mfa au mu fl);
      try exact OK1; try exact VIS1; try eassumption.
    all: try (rewrite (same_but_materialized_vmmaps _ _ SBM1)). all: try (rewrite (same_but_materialized_eager _ _ SBM1)). all: try eassumption.
    { clear - PB BNDC IDX CS3 HC; try acb; tlia. }
    { intros x Hx. apply WM1. apply SVIS. exact Hx. }
    cbv beta. intros msF2 mo2 P2. unfold cache_dealloc_post in P2. cbv zeta in P2.
    destruct P2 as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & q2' & m2 & L2 & S2
                    & OK2 & VIS2 & LED2 & MU2 & WM2 & MI2 & ENV2 & ST2 & PC1' & PC3' & PC4' & QST' & TST2 & RI2 & RST2 & FARR2 & FAJ2 & POI2).
    fold n in MU2, LED2, PC1', PC3', PC4', RI2, FARR2, FAJ2, POI2 |- *.
    (* [comment removed for export] *)
    assert (DK : forall A len, 17594333495296 <= A -> A + len <= p + class_size c -> sb <= A ->
                 disjoint_from (lcd_W lo (bv_unsigned sp) P CA (cnt - (if cnt =? mc then n else 0)) R FAB TH nf mfa (if cnt =? mc then rta_mfa nf n mfa else mfa)) A len).
    { intros A len D1 D2 D3. unfold lcd_W, rta_mfa, efs_new, round_up, kFreeArrayMapSize. cbn [disjoint_from].
      clear - D1 D2 D3 BND BNDC HC PLCq PB CS1 CS3 IDX CB MCR NFR ER EFAB ERB EP ECA; try acb.
      destruct (cnt =? mc); [destruct (4 * (nf + n) <=? mfa)|]; repeat split; try (lia_guard; first [clear - HC IDX MCR BND BNDC PLCq D2 ACEILB EP D3 CB NFR ER EFAB; tlia | tlia]).
      all: right; unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; (first [clear - HC MCR NFR BND EFAB BNDC D1 D3 H H0 H4 H5 H9 H10; tlia | tlia]). }
    assert (HDR2 : rw_cells asegs m2 mhdr [C1 (b8 0); C1 (b8 b1); C2 (wz 0); C4 (wz nu); C8 (wz actx)]).
    { eapply rw_cells_transport; [exact HDR1| exact MU2| exact WM2|]. apply DK; cbn [cells_size csize length Nat.add]; clear - BNDC PB EM EU RU8 NUR HC; try acb; tlia. }
    assert (MAG2 : rz = 16 \/ (32 <= rz /\ rw_cells asegs m2 p [C8 (wz 0); C8 (wz mhdr)])).
    { destruct MAG1 as [RZ16 | [RZ32 MC]]; [left; exact RZ16| right; split; [exact RZ32|]].
      eapply rw_cells_transport; [exact MC| exact MU2| exact WM2|]. apply DK; cbn [cells_size csize length Nat.add]; clear - BNDC PB CS3 HC; try acb; tlia. }
    assert (POI3 : poisoned m2 u (Z.to_nat (round_up nu 8 / 8)) kAsanHeapLeftRedzoneMagic).
    { eapply poisoned_carry; [exact POI1| exact MU2| exact WM2|]. unfold lcd_W. cbn [disjoint_from].
      match goal with TB : akobj TH 4096 |- _ => clear - SHR BND BNDC HC PLCq PB CS1 CS3 IDX NFR ER EFAB ERB EP ECA RU8 NUR EU CB MCR TB end; try acb. aunf.   (* [comment removed for export] *)
      (* [comment removed for export] *)
      assert (Q0 : 0 <= round_up nu 8 / 8) by (clear - RU8 NUR; apply Z.div_pos; tlia). rewrite Z2Nat.id by exact Q0.
      destruct (cnt =? mc); repeat split; try (left; clear - SHR Q0 BND BNDC HC ER EFAB ERB EP ECA; (lia_guard; first [clear - BND SHR BNDC; tlia | tlia])); try (lia_guard; first [clear - HC IDX MCR BND THB ER EP BNDC SHR PLCq ACEILB CB NFR EFAB; tlia | tlia]).
      all: left; unfold sh, ASHADOW_BASE in *; Z.div_mod_to_equations; (first [clear - HC IDX NUR MCR NFR EFAB RU8 PLCq H H0 H4 H9 H10; tlia | tlia]). }
    apply K. unfold recycle_prim_post. cbv zeta. fold n.
    do 16 eexists. exists m2, L2, S2.
    split; [exact OK2|]. split; [exact VIS2|].
    split. { clear - LED2 SBM1; try acb. unfold rf_ledger in *.
             rewrite (same_but_materialized_vmmaps _ _ SBM1), (same_but_materialized_eager _ _ SBM1) in LED2.
             destruct LED2 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
             split; [exact A1|]. split; [exact A2|]. split; [eapply nonvm_same_trans; [apply nonvm_same_mat; exact SBM1| exact A3]|].
             split; [exact A4|]. split; [exact A5|]. split; [exact A6|]. split; [exact A7|]. split; [exact A8|]. split; [exact A9| exact A10]. }
    split. { eapply munch_trans; [exact MU1|]. eapply munch_weaken; [| exact MU2]. unfold rp_W, lcd_W. cbn [app]. rx_sub_fp_struct. }
    split; [eapply wmono_trans; [exact WM1| exact WM2]|]. split; [exact MI2|]. split; [exact ENV2|]. split; [exact ST2|].
    split; [exact HDR2|]. split; [exact MAG2|]. split; [exact POI3|].
    split; [exact PC1'|]. split; [exact PC3'|]. split; [exact PC4'|]. split; [exact QST'|]. split; [exact TST2|].
    split; [exact RI2|]. split; [exact RST2|]. split; [exact FARR2|]. split; [exact FAJ2| exact POI2].
  Qed.
End RecyclePrim.

