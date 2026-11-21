(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Bytes.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed AsanProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW Require Import AImg RtCells AProto ABase AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState Inftrees InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import U2AArr ItAPure.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.U1A Require Import U2AObj U2AIface ItA_base.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import DrvAgree RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Definition ITABLE_STACK : Z := 256 + 4096.   (* [comment removed for export] *)
Definition IFAST_STACK : Z := 240.

Section Stmts.
Variable AI : AMallocIface.
Notation CI := (aci AI).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition itable_post (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (S lo : Z) (m : amem)
    (ty : codetype) (lf cf wf : Z -> Z) (lens_ofs codes nx bits : Z) (isd : bool)
    (strm mode last wrap havedict flags dmax check total head wbits wsize whave wnext window hold bits_ length_ offset extra
     lencode distcode lenbits distbits ncode nlen ndist have : word) : machine_state -> Prop :=
  fun ms' => let r := resA ty lf lens_ofs codes nx bits cf wf in
    exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (it_ret r)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ AHEAP AI L RNG st LB m'
    /\ client_agree AI LB (bv_unsigned sp) [(S + 136, S + 144); (S + 160, S + 168); (S + 808, S + 7160)] m m'
    /\ rw_cells asegs m' S (istate_cells strm mode last wrap havedict flags dmax check total head wbits wsize whave wnext window hold bits_
                              length_ offset extra lencode distcode
                              (if isd then lenbits else Z_to_bv 64 (it_bits r)) (if isd then Z_to_bv 64 (it_bits r) else distbits)
                              ncode nlen ndist have (Z_to_bv 64 (S + 1384 + 4 * it_table r)))
    /\ f16arr asegs m' (S + 168) 320 lf
    /\ f16arr asegs m' (S + 808) 288 (arr_get (it_work r))
    /\ f32arr asegs m' (S + 1384) 1444 (arr_get (it_tbl r))
    /\ (it_ret r = 0 \/ it_ret r = 1 \/ it_ret r = -1).

(* [comment removed for export] *)
Definition itabs_client : Prop := exists iv, In iv CI /\ fst iv <= 149216 /\ 149568 <= snd iv.

Definition inflate_table_stmtA (rng_fs : alayout -> footprint -> Prop) : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (ps : AsanCtrl.aptr) (S lo : Z)
         (ty : codetype) (lf cf wf : Z -> Z) (lens_ofs codes nx bits : Z) (isd : bool)
         (strm mode last wrap havedict flags dmax check total head wbits wsize whave wnext window hold bits_ length_ offset extra
          lencode distcode lenbits distbits ncode nlen ndist have : word),
  AHEAP AI L RNG st LB m ->
  atmost1_c2 LB ->
  (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->     (* [comment removed for export] *)
  In (HB ps S 7176) LB ->
  itabs_client -> it_tabsh m -> u2_img m ->
  rw_cells asegs m S (istate_cells strm mode last wrap havedict flags dmax check total head wbits wsize whave wnext window hold bits_
                        length_ offset extra lencode distcode lenbits distbits ncode nlen ndist have (Z_to_bv 64 (S + 1384 + 4 * nx))) ->
  (if isd then distbits else lenbits) = Z_to_bv 64 bits ->
  f16arr asegs m (S + 168) 320 lf -> f16arr asegs m (S + 808) 288 wf -> f32arr asegs m (S + 1384) 1444 cf ->
  itc ty lf lens_ofs codes nx bits cf wf ->
  a0 = Z_to_bv 64 (cty ty) -> a1 = Z_to_bv 64 (S + 168 + 2 * lens_ofs) -> a2 = Z_to_bv 64 codes ->
  a3 = Z_to_bv 64 (S + 160) -> a4 = Z_to_bv 64 (if isd then S + 140 else S + 136) (* [U14] a worker 2026-11-11 (proposed to a worker): distbits is S+140 at 1.4 (1.3.1: 124; lenbits 120 was moved, distbits was not) *) -> a5 = Z_to_bv 64 (S + 808) ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - ITABLE_STACK ->
  bv_unsigned sp mod 16 = 0 -> bv_unsigned sp + 16 < al_top L ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_fs L RNG ->
  evtF asegs RNG
       (itable_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB S lo m ty lf cf wf lens_ofs codes nx bits isd
                    strm mode last wrap havedict flags dmax check total head wbits wsize whave wnext window hold bits_ length_ offset extra
                    lencode distcode lenbits distbits ncode nlen ndist have)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 A_ITABLE) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ctab_at (RNG : footprint) (m : amem) (A n : Z) (rd : Z -> Z) : Prop :=
  bytes_at asegs m A (u32s (fws rd (Z.to_nat n))) /\ A mod 4 = 0 /\ 0 < A /\ 0 <= n /\ rng RNG A (4 * n)
  /\ (forall i, 0 <= i < n -> 0 <= rd i < 4294967296)
  /\ exists s1 s2, shadow_bytes m s1 s2 (fun _ => 0) /\ rng RNG s1 (s2 - s1)
                   /\ 2147446784 <= s1 /\ s2 <= 17594333495296
                   /\ s1 <= Z.shiftr A 3 + 2147450880 /\ Z.shiftr (A + 4 * n - 1) 3 + 2147450880 < s2.
(* [comment removed for export] *)
Definition app_band (X k : Z) : Prop := X + k <= 2147446784 \/ 17594333495296 <= X.

Definition ifast_W (SP Zs S OB osz : Z) : list (Z * Z) :=
  [(SP - IFAST_STACK, SP); (Zs, Zs + 56); (S + 8, S + 12); (S + 96, S + 108); (OB, OB + osz)].

Definition ifast_post (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (Zs S D n OB osz lo : Z) (m : amem) (cin cout hold bits : Z)
    (zti zto zmsg zalloc zfree zopq zdt zadl zres zp1 zp2 zp3 : word)
    (strm last wrap havedict flags dmax check total head wbits wsize whave wnext window length_ offset extra
     lencode distcode lenbits distbits ncode nlen ndist have next : word) : machine_state -> Prop :=
  fun ms' => exists (cin' cout' hold' bits' mode' : Z) (fo' : Z -> Z) (zmsg' : word)
                    (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : amem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (ifast_W (bv_unsigned sp) Zs S OB osz) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ 0 <= cin' <= n /\ cout <= cout' <= osz
    /\ 0 <= bits' <= 7 /\ 0 <= hold' < 2 ^ bits' /\ bits' <= 8 * cin'
    /\ 8 * (n - cin') + bits' + (osz - cout') < 8 * (n - cin) + bits + (osz - cout)
    /\ 8 * (n - cin') + bits' <= 8 * (n - cin) + bits
    /\ (mode' = LEN \/ mode' = TYPE \/ mode' = BAD)
    /\ rw_cells asegs m' Zs (strm_cells (Z_to_bv 64 (D + cin')) (Z_to_bv 64 (n - cin')) zti (Z_to_bv 64 (OB + cout'))
                                        (Z_to_bv 64 (osz - cout')) zto zmsg' (Z_to_bv 64 S) zalloc zfree zopq zdt zadl zres zp1 zp2 zp3)
    /\ rw_cells asegs m' S (istate_cells strm (Z_to_bv 64 mode') last wrap havedict flags dmax check total head wbits wsize whave wnext
                                         window (Z_to_bv 64 hold') (Z_to_bv 64 bits') length_ offset extra lencode distcode lenbits distbits
                                         ncode nlen ndist have next)
    /\ f8arr asegs m' OB (Z.to_nat osz) fo' /\ (forall i, 0 <= i < osz -> 0 <= fo' i < 256).

Definition inflate_fast_stmtA : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem) (Zs S D n OB osz Wd lo : Z)
         (cin cout hold bits out whave wnext lb db la na da nd : Z) (rdL rdD fo fw : Z -> Z) (payload : list Z)
         (zti zto zmsg zalloc zfree zopq zdt zadl zres zp1 zp2 zp3 : word)
         (strm last wrap havedict flags dmax check total head wbits length_ offset extra ncode nlen ndist have next : word)
         (back was pad : word),
  mem_inv asegs m -> rt_got m -> rt_shbase m ->
  stk asegs m lo (bv_unsigned sp) -> KHIGH <= lo -> lo <= bv_unsigned sp - IFAST_STACK -> bv_unsigned sp + 16 < KEND ->
  a0 = Z_to_bv 64 Zs -> a1 = Z_to_bv 64 out ->
  (* [comment removed for export] *)
  rw_cells asegs m Zs (strm_cells (Z_to_bv 64 (D + cin)) (Z_to_bv 64 (n - cin)) zti (Z_to_bv 64 (OB + cout)) (Z_to_bv 64 (osz - cout))
                                  zto zmsg (Z_to_bv 64 S) zalloc zfree zopq zdt zadl zres zp1 zp2 zp3) ->
  rw_cells asegs m S (istate_cells strm (Z_to_bv 64 LEN) last wrap havedict flags dmax check total head wbits
                                   (Z_to_bv 64 (if Wd =? 0 then 0 else 32768)) (Z_to_bv 64 whave) (Z_to_bv 64 wnext) (Z_to_bv 64 Wd)
                                   (Z_to_bv 64 hold) (Z_to_bv 64 bits) length_ offset extra (Z_to_bv 64 la) (Z_to_bv 64 da)
                                   (Z_to_bv 64 lb) (Z_to_bv 64 db) ncode nlen ndist have next) ->
  rw_cells asegs m (S + 7160) (itail_cells (Z_to_bv 64 1) back was pad) ->
  Zs mod 8 = 0 -> S mod 16 = 0 ->
  shadow_bytes m (Z.shiftr Zs 3 + 2147450880) (Z.shiftr Zs 3 + 2147450880 + 14) (fun _ => 0) -> rng RNG Zs 112 ->
  rng RNG (Z.shiftr Zs 3 + 2147450880) 14 ->
  state_sh RNG m S ->
  ctab_at RNG m la na rdL -> ctab_at RNG m da nd rdD ->
  1 <= lb <= 15 -> 1 <= db <= 15 -> tab_ok LENS rdL lb na = true -> tab_ok DISTS rdD db nd = true ->
  bytes_at asegs m D (map (Z_to_bv 8) payload) -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = n ->
  1 <= D -> D mod 8 = 0 -> 0 <= n < 67108864 -> unpoisoned m D (D + n) -> rng RNG D n -> rng RNG (Z.shiftr D 3 + 2147450880) (n / 8 + 1) ->
  f8arr asegs m OB (Z.to_nat osz) fo -> (forall i, 0 <= i < osz -> 0 <= fo i < 256) -> OB mod 8 = 0 -> 1 <= osz <= 262144 ->
  shadow_bytes m (Z.shiftr OB 3 + 2147450880) (Z.shiftr OB 3 + 2147450880 + (osz + 7) / 8) (fun _ => 0) ->
  rng RNG OB osz -> rng RNG (Z.shiftr OB 3 + 2147450880) ((osz + 7) / 8) ->
  (Wd = 0 \/ (f8arr asegs m Wd 32768 fw /\ Wd mod 16 = 0 /\ rng RNG Wd 32768 /\ rng RNG (Z.shiftr Wd 3 + 2147450880) 4096
              /\ shadow_bytes m (Z.shiftr Wd 3 + 2147450880) (Z.shiftr Wd 3 + 2147450880 + 4096) (fun _ => 0))) ->
  (forall i, 0 <= i < 32768 -> 0 <= fw i < 256) ->
  (* [comment removed for export] *)
  0 < Zs -> Zs + 112 <= lo -> 0 < S -> S + 7176 <= lo -> D + n <= lo -> 0 < OB -> OB + osz <= lo -> la + 4 * na <= lo -> da + 4 * nd <= lo ->
  (Wd = 0 \/ (0 < Wd /\ Wd + 32768 <= lo)) ->
  disjoint_from (ifast_W (bv_unsigned sp) Zs S OB osz) la (4 * na) -> disjoint_from (ifast_W (bv_unsigned sp) Zs S OB osz) da (4 * nd) ->
  disjoint_from (ifast_W (bv_unsigned sp) Zs S OB osz) D n ->
  (Wd = 0 \/ disjoint_from (ifast_W (bv_unsigned sp) Zs S OB osz) Wd 32768) ->
  (Zs + 112 <= S \/ S + 7176 <= Zs) -> (Zs + 112 <= OB \/ OB + osz <= Zs) -> (S + 7176 <= OB \/ OB + osz <= S) ->
  app_band Zs 112 -> app_band S 7176 -> app_band OB osz ->
  (* [comment removed for export] *)
  0 <= cin <= n -> 6 <= n - cin -> 0 <= cout <= osz -> 258 <= osz - cout ->
  0 <= bits <= 40 -> 0 <= hold < 2 ^ bits -> bits <= 8 * cin ->
  osz - cout <= out <= osz -> out - (osz - cout) <= cout ->
  0 <= whave -> 0 <= wnext -> (Wd = 0 -> whave = 0 /\ wnext = 0) ->
  (Wd <> 0 -> whave <= 32768 /\ wnext < 32768 /\ (whave < 32768 -> wnext = whave)) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG
       (ifast_post RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc Zs S D n OB osz lo m cin cout hold bits
                   zti zto zmsg zalloc zfree zopq zdt zadl zres zp1 zp2 zp3
                   strm last wrap havedict flags dmax check total head wbits (Z_to_bv 64 (if Wd =? 0 then 0 else 32768))
                   (Z_to_bv 64 whave) (Z_to_bv 64 wnext) (Z_to_bv 64 Wd) length_ offset extra (Z_to_bv 64 la) (Z_to_bv 64 da)
                   (Z_to_bv 64 lb) (Z_to_bv 64 db) ncode nlen ndist have next)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 A_IFAST) fc None m (seg_rom asegs)).

End Stmts.
End CANSEC1.
