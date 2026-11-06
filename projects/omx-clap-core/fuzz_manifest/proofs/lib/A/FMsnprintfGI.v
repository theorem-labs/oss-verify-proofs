(* fm's snprintf glue, interface: the contracts of the walks above printf_core at fm.asan addresses, in FMsnprintfI's
   frame (sp0 = musl vfprintf's entry sp). MEASURED from the unstripped twin of fm.asan:
     __wrap_snprintf 0x41314: j 0x45c90
     __interceptor_snprintf 0x45c90: frame 0x60; a3..a7 spilled at sp + 0x38 (the va area P); TryAsanInitFromRtl 0x59a78;
       jal __interceptor_vsnprintf 0x458a0 (ra 0x45ce8)
     __interceptor_vsnprintf 0x458a0: frame 0x7f0 + 0x80; TryAsanInitFromRtl; common_flags ()->check_printf (slot 0x999a0
       -> 0x1338a8, byte + 0x54); printf_common 0x44d24 (ra 0x45918); REAL (vsnprintf) from slot 0x9b748 (ra 0x45934);
       res >= 0 and size >= res + 1: WRITE_RANGE (str, res + 1) from 0x45a18 to 0x4599c; epilogue
     musl vsnprintf 0x91f0c: frame 0x130; canary; memset (sp, 0, 0xe8) through __wrap_memset 0x51a60 (ra 0x91f70); FILE
       fields; *c.s = 0; jal __wrap_vfprintf 0x41308 = j 0x457ec (ra 0x91fac); canary check
     __interceptor_vfprintf 0x457ec: frame 0x30; TryAsanInitFromRtl; check_printf; printf_common (ra 0x45844);
       REAL (vfprintf) from slot 0x9b740 (ra 0x4585c)
     musl vfprintf 0x8ede0: frame 0x170 (the walks below it are FMsnprintfI's)
   Entry sps from sp0: vfprintf sp0, its interceptor sp0 + 0x30, vsnprintf sp0 + 0x160, its interceptor sp0 + 0x9d0, the
   snprintf interceptor sp0 + 0xa30; the va area P = sp0 + 0xa08. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC20 YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v FMupoison FMH_Base FMH_Rt FMsnprintfI.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- fm.asan addresses ---- *)
Definition A_TRY : Z := 0x59a78.        (* __asan::TryAsanInitFromRtl *)
Definition RA_VSNI : Z := 0x45ce8.      (* __interceptor_snprintf: return from the vsnprintf interceptor *)
Definition RA_PCOM_VSNI : Z := 0x45918. (* __interceptor_vsnprintf: return from printf_common *)
Definition RA_VSN : Z := 0x45934.       (* __interceptor_vsnprintf: return from REAL (vsnprintf) *)
Definition WRC_ENTRY : Z := 0x45a18.    (* __interceptor_vsnprintf: WRITE_RANGE (str, res + 1), size >= res + 1 *)
Definition WRC_END : Z := 0x4599c.
Definition RA_MSET : Z := 0x91f70.      (* musl vsnprintf: return from memset *)
Definition RA_VFPI : Z := 0x91fac.      (* musl vsnprintf: return from __wrap_vfprintf *)
Definition RA_PCOM_VFPI : Z := 0x45844. (* __interceptor_vfprintf: return from printf_common *)
Definition RA_VFP : Z := 0x4585c.       (* __interceptor_vfprintf: return from REAL (vfprintf) *)
Definition SLOT_VSN : Z := 0x9b748.     (* REAL (vsnprintf) = A_VSN *)
Definition SLOT_VFP : Z := 0x9b740.     (* REAL (vfprintf) = A_VFP *)
Definition SLOT_CFLAGS : Z := 0x999a0.  (* -> common_flags 0x1338a8; check_printf at + 0x54 *)
Definition A_CHECK_PRINTF : Z := 0x1338fc.
Definition A_ASAN_INITED : Z := 0xa2a58.

(* ---- entry sps of the walks, from sp0 ---- *)
Definition OSP_VFPI : Z := 0x30.
Definition OSP_VSN : Z := 0x160.
Definition OSP_VSNI : Z := 0x9d0.
Definition OSP_SNI : Z := 0xa30.
Definition OP_VA : Z := 0xa08.

Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
#[local] Abbreviation segs := tfibsegs.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* the destination bytes the whole snprintf writes, and with them musl vsnprintf's FILE and cookie *)
Definition dst_xw (D M a : Z) : Prop := D <= a < D + M.
Definition vf_xw (sp0 D M a : Z) : Prop := (sp0 + FO <= a < sp0 + CKO + 16) \/ dst_xw D M a.

(* what every walk above printf_core starts from: FMsnprintfI's snk_base at sp0, the image facts printf_core reads, the
   format and its arguments in 8-byte slots at P, the output, the destination *)
Definition gl_pre (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world segs) (mem : word -> option byte)
  (md : Model) (sp0 D N M f : Z) (ps : list fpiece) (P : Z) (args out : list Z) : Prop :=
  snk_base B ly S U W mem md sp0 /\ rom_viewN segs B W mem /\
  (exists cval, val_mem segs (rdW W mem) FM_GOT_canary 8 FM_canary /\ val_mem segs (rdW W mem) FM_canary 8 cval /\
     0 <= cval < 2 ^ 64) /\
  In (f, ps) FM_SN_FMTS /\ cstr_ok segs W mem f (fmt_bytes ps) /\
  sp0 + 0x200 <= P /\ P + 8 * Z.of_nat (length args) <= ly_stk_hi ly /\ slots_at W mem P args /\
  frender segs W mem D N ps args out /\ Z.of_nat (length out) + 1 <= M <= N /\ N <= 2 ^ 30 /\
  snk_dest B ly S W mem D M.

(* the post of each walk: back at ra, FMsnprintfI's frame below top and XW, callee-saved registers kept, a0 = len out,
   out and its NUL at D *)
Definition gl_post (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world segs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (sp0 top : Z) (XW : Z -> Prop) (D : Z) (out : list Z)
  : world segs -> config -> Prop :=
  fun W' c' => W' = W /\ exists regs' mem' md',
    c' = cfg_at segs (raZ regs) regs' mem' md' /\ snk_frame B ly S U W mem md sp0 top XW mem' md' /\
    aregs_preserved regs regs' /\ getr regs' 10 = w64 (Z.of_nat (length out)) /\
    (forall i, 0 <= i <= Z.of_nat (length out) ->
       aview segs (w_H W) mem' (D + i) = Some (nth (Z.to_nat i) (out ++ [0]) 0)).

(* musl vsnprintf's FILE (memset to 0, then write, buf, lock, lbf, cookie) and its cookie {s = D, n = N - 1} at
   sp0 + FO, and *c.s = 0, as vfprintf finds them *)
Definition vsn_fields (sp0 D N : Z) : list (Z * nat * Z) :=
  [(0, 8%nat, 0); (8, 8%nat, 0); (16, 8%nat, 0); (24, 8%nat, 0); (32, 8%nat, 0); (40, 8%nat, 0); (48, 8%nat, 0);
   (56, 8%nat, 0); (64, 8%nat, 0); (72, 8%nat, A_SNW); (80, 8%nat, 0); (88, 8%nat, sp0 + FO + 0xff); (96, 8%nat, 0);
   (104, 8%nat, 0); (112, 8%nat, 0); (120, 8%nat, 0); (128, 8%nat, 0); (136, 4%nat, 0); (140, 4%nat, 0xffffffff);
   (144, 4%nat, 0xffffffff); (148, 4%nat, 0); (152, 8%nat, sp0 + CKO); (160, 8%nat, 0); (168, 8%nat, 0);
   (176, 8%nat, 0); (184, 8%nat, 0); (192, 8%nat, 0); (200, 8%nat, 0); (208, 8%nat, 0); (216, 8%nat, 0);
   (224, 8%nat, 0); (232, 8%nat, D); (240, 8%nat, N - 1)].
Definition vsn_file (W : world segs) (mem : word -> option byte) (sp0 D N : Z) : Prop :=
  Forall (fun c => val_mem segs (rdW W mem) (sp0 + FO + fst (fst c)) (snd (fst c)) (snd c)) (vsn_fields sp0 D N) /\
  aview segs (w_H W) mem D = Some 0.

(* musl vfprintf (f = the FILE, fmt, ap = P) *)
Definition avfp_realizes (pc : Z) : Prop :=
  forall ly S U W regs mem md sp0 D N M f ps P args out,
  gl_pre ly S U W mem md sp0 D N M f ps P args out -> snk_regs B regs sp0 ->
  getr regs 10 = w64 (sp0 + FO) -> getr regs 11 = w64 f -> getr regs 12 = w64 P ->
  vsn_file W mem sp0 D N ->
  SRr segs W (cfg_at segs pc regs mem md) (gl_post ly S U W regs mem md sp0 sp0 (vf_xw sp0 D M) D out).
(* __interceptor_vfprintf, the same arguments, entered at sp0 + 0x30 *)
Definition avfpi_realizes (pc : Z) : Prop :=
  forall ly S U W regs mem md sp0 D N M f ps P args out,
  gl_pre ly S U W mem md sp0 D N M f ps P args out -> snk_regs B regs (sp0 + OSP_VFPI) ->
  getr regs 10 = w64 (sp0 + FO) -> getr regs 11 = w64 f -> getr regs 12 = w64 P ->
  vsn_file W mem sp0 D N ->
  SRr segs W (cfg_at segs pc regs mem md)
    (gl_post ly S U W regs mem md sp0 (sp0 + OSP_VFPI) (vf_xw sp0 D M) D out).
(* musl vsnprintf (s = D, n = N, fmt, ap = P), entered at sp0 + 0x160 *)
Definition avsn_realizes (pc : Z) : Prop :=
  forall ly S U W regs mem md sp0 D N M f ps P args out,
  gl_pre ly S U W mem md sp0 D N M f ps P args out -> snk_regs B regs (sp0 + OSP_VSN) ->
  getr regs 10 = w64 D -> getr regs 11 = w64 N -> getr regs 12 = w64 f -> getr regs 13 = w64 P ->
  SRr segs W (cfg_at segs pc regs mem md)
    (gl_post ly S U W regs mem md sp0 (sp0 + OSP_VSN) (dst_xw D M) D out).
(* __interceptor_vsnprintf (str = D, size = N, format, ap = P), entered at sp0 + 0x9d0: its frame above the band is
   present too, and the va area lies above it *)
Definition avsni_realizes (pc : Z) : Prop :=
  forall ly S U W regs mem md sp0 D N M f ps P args out,
  gl_pre ly S U W mem md sp0 D N M f ps P args out -> snk_regs B regs (sp0 + OSP_VSNI) ->
  sp0 + OSP_VSNI <= P -> sp0 + OSP_VSNI <= ly_stk_hi ly ->
  (forall a, sp0 + 0x200 <= a < sp0 + OSP_VSNI -> apresent (w_H W) mem a) ->
  getr regs 10 = w64 D -> getr regs 11 = w64 N -> getr regs 12 = w64 f -> getr regs 13 = w64 P ->
  SRr segs W (cfg_at segs pc regs mem md)
    (gl_post ly S U W regs mem md sp0 (sp0 + OSP_VSNI) (dst_xw D M) D out).
End i.
