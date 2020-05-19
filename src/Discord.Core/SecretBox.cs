using System;
using System.Buffers.Binary;
using System.Runtime.CompilerServices;

namespace Discord.Audio
{
    public static class SecretBox
    {
        public static int Encrypt(byte[] input, int inputOffset, int inputLength, byte[] output, int outputOffset, byte[] nonce, byte[] secret)
        {
            // crypto_secretbox_easy
            var @in = input.AsSpan(inputOffset, inputLength);
            var @out = output.AsSpan(outputOffset, inputLength + 16);

            crypto_secretbox_detached(@out.Slice(16), @out.Slice(0, 16), @in, nonce.AsSpan(0, 24), secret.AsSpan(0, 32));

            return inputLength + 16;
        }

        public static int Decrypt(byte[] input, int inputOffset, int inputLength, byte[] output, int outputOffset, byte[] nonce, byte[] secret)
        {
            // crypto_secretbox_open_easy
            var @in = input.AsSpan(inputOffset, inputLength);
            var @out = output.AsSpan(outputOffset, inputLength - 16);

            crypto_secretbox_open_detached(@out, @in.Slice(16), @in.Slice(0, 16), nonce.AsSpan(0, 24), secret.AsSpan(0, 32));

            return inputLength - 16;
        }

        #region secretbox

        private static void crypto_secretbox_detached(Span<byte> c, Span<byte> mac, ReadOnlySpan<byte> m, ReadOnlySpan<byte> n, ReadOnlySpan<byte> k)
        {
            Span<byte> block0 = stackalloc byte[64];
            Span<byte> subkey = stackalloc byte[32];

            crypto_core_hsalsa20(subkey, n, k);

            int mlen0 = m.Length;
            if (mlen0 > 32) mlen0 = 32;
            m.Slice(0, mlen0).CopyTo(block0.Slice(32, mlen0));

            crypto_stream_salsa20_xor_ic(block0, block0.Slice(0, mlen0 + 32), n.Slice(16), 0, subkey);

            block0.Slice(32, mlen0).CopyTo(c.Slice(0, mlen0));

            if (m.Length > mlen0)
            {
                crypto_stream_salsa20_xor_ic(c.Slice(mlen0), m.Slice(mlen0), n.Slice(16), 1, subkey);
            }

            crypto_onetimeauth_poly1305(mac, c.Slice(0, m.Length), block0);
        }

        private static void crypto_secretbox_open_detached(Span<byte> m, ReadOnlySpan<byte> c, ReadOnlySpan<byte> mac, ReadOnlySpan<byte> n, ReadOnlySpan<byte> k)
        {
            Span<byte> block0 = stackalloc byte[64];
            Span<byte> subkey = stackalloc byte[32];

            crypto_core_hsalsa20(subkey, n, k);
            crypto_stream_salsa20(block0.Slice(0, 32), n.Slice(16), subkey);
            if (!crypto_onetimeauth_poly1305_verify(mac, c, block0))
                throw new ArgumentException(nameof(mac));

            int mlen0 = m.Length;
            if (mlen0 > 32) mlen0 = 32;
            c.Slice(0, mlen0).CopyTo(block0.Slice(32));

            crypto_stream_salsa20_xor_ic(block0, block0.Slice(0, mlen0 + 32), n.Slice(16), 0, subkey);

            block0.Slice(32, mlen0).CopyTo(m.Slice(0, mlen0));

            if (c.Length > mlen0)
            {
                crypto_stream_salsa20_xor_ic(m.Slice(mlen0), c.Slice(mlen0), n.Slice(16), 1, subkey);
            }
        }

        #endregion

        #region poly1305

        static void crypto_onetimeauth_poly1305(Span<byte> mac, ReadOnlySpan<byte> m, ReadOnlySpan<byte> k)
        {
            uint r0 = (LOAD32(k, 0) >> 0) & 0x3ffffffU;
            uint r1 = (LOAD32(k, 3) >> 2) & 0x3ffff03U;
            uint r2 = (LOAD32(k, 6) >> 4) & 0x3ffc0ffU;
            uint r3 = (LOAD32(k, 9) >> 6) & 0x3f03fffU;
            uint r4 = (LOAD32(k, 12) >> 8) & 0x00fffffU;

            uint s1 = r1 * 5;
            uint s2 = r2 * 5;
            uint s3 = r3 * 5;
            uint s4 = r4 * 5;

            uint h0 = 0;
            uint h1 = 0;
            uint h2 = 0;
            uint h3 = 0;
            uint h4 = 0;

            while (m.Length > 0)
            {
                uint hibit = 0x01000000;
                if (m.Length < 16)
                {
                    hibit = 0;
                    mac.Fill(0);
                    m.CopyTo(mac);
                    mac[m.Length] = 1;
                    m = mac;
                }

                /* h += m[i] */
                h0 += (LOAD32(m, 0) >> 0) & 0x3ffffff;
                h1 += (LOAD32(m, 3) >> 2) & 0x3ffffff;
                h2 += (LOAD32(m, 6) >> 4) & 0x3ffffff;
                h3 += (LOAD32(m, 9) >> 6) & 0x3ffffff;
                h4 += (LOAD32(m, 12) >> 8) | hibit;

                /* h *= r */
                ulong d0 = (ulong)h0 * r0 + (ulong)h1 * s4 + (ulong)h2 * s3 + (ulong)h3 * s2 + (ulong)h4 * s1;
                ulong d1 = (ulong)h0 * r1 + (ulong)h1 * r0 + (ulong)h2 * s4 + (ulong)h3 * s3 + (ulong)h4 * s2;
                ulong d2 = (ulong)h0 * r2 + (ulong)h1 * r1 + (ulong)h2 * r0 + (ulong)h3 * s4 + (ulong)h4 * s3;
                ulong d3 = (ulong)h0 * r3 + (ulong)h1 * r2 + (ulong)h2 * r1 + (ulong)h3 * r0 + (ulong)h4 * s4;
                ulong d4 = (ulong)h0 * r4 + (ulong)h1 * r3 + (ulong)h2 * r2 + (ulong)h3 * r1 + (ulong)h4 * r0;

                /* (partial) h %= p */
                h0 = (uint)d0 & 0x3ffffff; d1 += (d0 >> 26);
                h1 = (uint)d1 & 0x3ffffff; d2 += (d1 >> 26);
                h2 = (uint)d2 & 0x3ffffff; d3 += (d2 >> 26);
                h3 = (uint)d3 & 0x3ffffff; d4 += (d3 >> 26);
                h4 = (uint)d4 & 0x3ffffff;
                h0 += (uint)(d4 >> 26) * 5;
                h1 += (h0 >> 26);
                h0 &= 0x3ffffff;

                m = m.Slice(16);
            }

            /* fully carry h */
            h2 += (h1 >> 26); h1 = h1 & 0x3ffffffU;
            h3 += (h2 >> 26); h2 = h2 & 0x3ffffffU;
            h4 += (h3 >> 26); h3 = h3 & 0x3ffffffU;
            h0 += (h4 >> 26) * 5; h4 = h4 & 0x3ffffffU;
            h1 += (h0 >> 26); h0 = h0 & 0x3ffffffU;

            /* compute h + -p */
            uint g0 = h0 + 5;
            uint g1 = h1 + (g0 >> 26); g0 &= 0x3ffffff;
            uint g2 = h2 + (g1 >> 26); g1 &= 0x3ffffff;
            uint g3 = h3 + (g2 >> 26); g2 &= 0x3ffffff;
            uint g4 = h4 + (g3 >> 26) - 0x04000000; g3 &= 0x3ffffff;

            /* select h if h < p, or h + -p if h >= p */
            uint mask = (g4 >> 31) - 1;
            g0 &= mask;
            g1 &= mask;
            g2 &= mask;
            g3 &= mask;
            g4 &= mask;
            mask = ~mask;

            h0 = (h0 & mask) | g0;
            h1 = (h1 & mask) | g1;
            h2 = (h2 & mask) | g2;
            h3 = (h3 & mask) | g3;
            h4 = (h4 & mask) | g4;

            /* h = h % (2^128) */
            h0 = ((h0) | (h1 << 26)) & 0xffffffffU;
            h1 = ((h1 >> 6) | (h2 << 20)) & 0xffffffffU;
            h2 = ((h2 >> 12) | (h3 << 14)) & 0xffffffffU;
            h3 = ((h3 >> 18) | (h4 << 8)) & 0xffffffffU;

            /* mac = (h + pad) % (2^128) */
            ulong f0 = (ulong)h0 + LOAD32(k, 16);
            ulong f1 = (ulong)h1 + LOAD32(k, 20);
            ulong f2 = (ulong)h2 + LOAD32(k, 24);
            ulong f3 = (ulong)h3 + LOAD32(k, 28);
            STORE32(mac, 0, (uint)f0);
            f1 += (f0 >> 32);
            STORE32(mac, 4, (uint)f1);
            f2 += (f1 >> 32);
            STORE32(mac, 8, (uint)f2);
            f3 += (f2 >> 32);
            STORE32(mac, 12, (uint)f3);
        }

        static bool crypto_onetimeauth_poly1305_verify(ReadOnlySpan<byte> mac, ReadOnlySpan<byte> m, ReadOnlySpan<byte> k)
        {
            Span<byte> correct = stackalloc byte[16];
            crypto_onetimeauth_poly1305(correct, m, k);
            return correct.SequenceEqual(mac);
        }

        #endregion

        #region salsa20

        static void crypto_stream_salsa20(Span<byte> c, ReadOnlySpan<byte> n, ReadOnlySpan<byte> k)
        {
            Span<byte> @in = stackalloc byte[16];
            Span<byte> block = stackalloc byte[64];
            Span<byte> kcopy = stackalloc byte[32];

            k.Slice(0, 32).CopyTo(kcopy);
            n.Slice(0, 8).CopyTo(@in);
            //@in.Slice(8, 8).Fill(0);

            while (c.Length > 64)
            {
                crypto_core_salsa20(c, @in, kcopy);
                uint u = 1;
                for (int i = 8; i < 16; i++)
                {
                    u += @in[i];
                    @in[i] = (byte)u;
                    u >>= 8;
                }
                c = c.Slice(64);
            }
            crypto_core_salsa20(block, @in, kcopy);
            for (int i = 0; i < c.Length; i++)
            {
                c[i] = block[i];
            }
        }

        static void crypto_stream_salsa20_xor_ic(Span<byte> c, ReadOnlySpan<byte> m, ReadOnlySpan<byte> n, ulong ic, ReadOnlySpan<byte> k)
        {
            Span<byte> @in = stackalloc byte[16];
            Span<byte> block = stackalloc byte[64];
            Span<byte> kcopy = stackalloc byte[32];

            k.Slice(0, 32).CopyTo(kcopy);
            n.Slice(0, 8).CopyTo(@in);
            STORE64(@in, 8, ic);

            while (m.Length > 64)
            {
                crypto_core_salsa20(block, @in, kcopy);
                for (int i = 0; i < 64; i++)
                {
                    c[i] = (byte)(m[i] ^ block[i]);
                }
                uint u = 1;
                for (int i = 8; i < 16; i++)
                {
                    u += @in[i];
                    @in[i] = (byte)u;
                    u >>= 8;
                }
                c = c.Slice(64);
                m = m.Slice(64);
            }
            crypto_core_salsa20(block, @in, kcopy);
            for (int i = 0; i < m.Length; i++)
            {
                c[i] = (byte)(m[i] ^ block[i]);
            }
        }

        static void crypto_core_salsa20(Span<byte> @out, ReadOnlySpan<byte> @in, ReadOnlySpan<byte> k)
        {
            uint x00 = 0x61707865U;
            uint x05 = 0x3320646eU;
            uint x10 = 0x79622d32U;
            uint x15 = 0x6b206574U;

            uint x01 = LOAD32(k, 0);
            uint x02 = LOAD32(k, 4);
            uint x03 = LOAD32(k, 8);
            uint x04 = LOAD32(k, 12);
            uint x11 = LOAD32(k, 16);
            uint x12 = LOAD32(k, 20);
            uint x13 = LOAD32(k, 24);
            uint x14 = LOAD32(k, 28);

            uint x06 = LOAD32(@in, 0);
            uint x07 = LOAD32(@in, 4);
            uint x08 = LOAD32(@in, 8);
            uint x09 = LOAD32(@in, 12);

            uint j00 = x00, j01 = x01, j02 = x02, j03 = x03, j04 = x04, j05 = x05, j06 = x06, j07 = x07;
            uint j08 = x08, j09 = x09, j10 = x10, j11 = x11, j12 = x12, j13 = x13, j14 = x14, j15 = x15;

            for (int i = 20; i > 0; i -= 2)
            {
                x04 ^= ROTL32(x00 + x12, 7);
                x08 ^= ROTL32(x04 + x00, 9);
                x12 ^= ROTL32(x08 + x04, 13);
                x00 ^= ROTL32(x12 + x08, 18);
                x09 ^= ROTL32(x05 + x01, 7);
                x13 ^= ROTL32(x09 + x05, 9);
                x01 ^= ROTL32(x13 + x09, 13);
                x05 ^= ROTL32(x01 + x13, 18);
                x14 ^= ROTL32(x10 + x06, 7);
                x02 ^= ROTL32(x14 + x10, 9);
                x06 ^= ROTL32(x02 + x14, 13);
                x10 ^= ROTL32(x06 + x02, 18);
                x03 ^= ROTL32(x15 + x11, 7);
                x07 ^= ROTL32(x03 + x15, 9);
                x11 ^= ROTL32(x07 + x03, 13);
                x15 ^= ROTL32(x11 + x07, 18);

                x01 ^= ROTL32(x00 + x03, 7);
                x02 ^= ROTL32(x01 + x00, 9);
                x03 ^= ROTL32(x02 + x01, 13);
                x00 ^= ROTL32(x03 + x02, 18);
                x06 ^= ROTL32(x05 + x04, 7);
                x07 ^= ROTL32(x06 + x05, 9);
                x04 ^= ROTL32(x07 + x06, 13);
                x05 ^= ROTL32(x04 + x07, 18);
                x11 ^= ROTL32(x10 + x09, 7);
                x08 ^= ROTL32(x11 + x10, 9);
                x09 ^= ROTL32(x08 + x11, 13);
                x10 ^= ROTL32(x09 + x08, 18);
                x12 ^= ROTL32(x15 + x14, 7);
                x13 ^= ROTL32(x12 + x15, 9);
                x14 ^= ROTL32(x13 + x12, 13);
                x15 ^= ROTL32(x14 + x13, 18);
            }

            STORE32(@out, 0, x00 + j00);
            STORE32(@out, 4, x01 + j01);
            STORE32(@out, 8, x02 + j02);
            STORE32(@out, 12, x03 + j03);
            STORE32(@out, 16, x04 + j04);
            STORE32(@out, 20, x05 + j05);
            STORE32(@out, 24, x06 + j06);
            STORE32(@out, 28, x07 + j07);
            STORE32(@out, 32, x08 + j08);
            STORE32(@out, 36, x09 + j09);
            STORE32(@out, 40, x10 + j10);
            STORE32(@out, 44, x11 + j11);
            STORE32(@out, 48, x12 + j12);
            STORE32(@out, 52, x13 + j13);
            STORE32(@out, 56, x14 + j14);
            STORE32(@out, 60, x15 + j15);
        }

        static void crypto_core_hsalsa20(Span<byte> @out, ReadOnlySpan<byte> @in, ReadOnlySpan<byte> k)
        {
            uint x00 = 0x61707865U;
            uint x05 = 0x3320646eU;
            uint x10 = 0x79622d32U;
            uint x15 = 0x6b206574U;

            uint x01 = LOAD32(k, 0);
            uint x02 = LOAD32(k, 4);
            uint x03 = LOAD32(k, 8);
            uint x04 = LOAD32(k, 12);
            uint x11 = LOAD32(k, 16);
            uint x12 = LOAD32(k, 20);
            uint x13 = LOAD32(k, 24);
            uint x14 = LOAD32(k, 28);

            uint x06 = LOAD32(@in, 0);
            uint x07 = LOAD32(@in, 4);
            uint x08 = LOAD32(@in, 8);
            uint x09 = LOAD32(@in, 12);

            for (int i = 20; i > 0; i -= 2)
            {
                x04 ^= ROTL32(x00 + x12, 7);
                x08 ^= ROTL32(x04 + x00, 9);
                x12 ^= ROTL32(x08 + x04, 13);
                x00 ^= ROTL32(x12 + x08, 18);
                x09 ^= ROTL32(x05 + x01, 7);
                x13 ^= ROTL32(x09 + x05, 9);
                x01 ^= ROTL32(x13 + x09, 13);
                x05 ^= ROTL32(x01 + x13, 18);
                x14 ^= ROTL32(x10 + x06, 7);
                x02 ^= ROTL32(x14 + x10, 9);
                x06 ^= ROTL32(x02 + x14, 13);
                x10 ^= ROTL32(x06 + x02, 18);
                x03 ^= ROTL32(x15 + x11, 7);
                x07 ^= ROTL32(x03 + x15, 9);
                x11 ^= ROTL32(x07 + x03, 13);
                x15 ^= ROTL32(x11 + x07, 18);

                x01 ^= ROTL32(x00 + x03, 7);
                x02 ^= ROTL32(x01 + x00, 9);
                x03 ^= ROTL32(x02 + x01, 13);
                x00 ^= ROTL32(x03 + x02, 18);
                x06 ^= ROTL32(x05 + x04, 7);
                x07 ^= ROTL32(x06 + x05, 9);
                x04 ^= ROTL32(x07 + x06, 13);
                x05 ^= ROTL32(x04 + x07, 18);
                x11 ^= ROTL32(x10 + x09, 7);
                x08 ^= ROTL32(x11 + x10, 9);
                x09 ^= ROTL32(x08 + x11, 13);
                x10 ^= ROTL32(x09 + x08, 18);
                x12 ^= ROTL32(x15 + x14, 7);
                x13 ^= ROTL32(x12 + x15, 9);
                x14 ^= ROTL32(x13 + x12, 13);
                x15 ^= ROTL32(x14 + x13, 18);
            }

            STORE32(@out, 0, x00);
            STORE32(@out, 4, x05);
            STORE32(@out, 8, x10);
            STORE32(@out, 12, x15);
            STORE32(@out, 16, x06);
            STORE32(@out, 20, x07);
            STORE32(@out, 24, x08);
            STORE32(@out, 28, x09);
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        static uint ROTL32(uint x, int y)
        {
            return (x << y) | (x >> (32 - y));
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        static uint LOAD32(ReadOnlySpan<byte> x, int y)
        {
            return BinaryPrimitives.ReadUInt32LittleEndian(x.Slice(y, 4));
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        static void STORE32(Span<byte> x, int y, uint z)
        {
            BinaryPrimitives.WriteUInt32LittleEndian(x.Slice(y, 4), z);
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        static void STORE64(Span<byte> x, int y, ulong z)
        {
            BinaryPrimitives.WriteUInt64LittleEndian(x.Slice(y, 8), z);
        }

        #endregion
    }
}
