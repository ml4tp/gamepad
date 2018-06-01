# Copyright 2018 The GamePad Authors. All Rights Reserved.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
# ==============================================================================


class MyFile(object):
    """
    Wrapper around Python file for parsing purposes.
    """
    def __init__(self, filename):
        self.filename = filename
        self.f_head = open(filename, 'r')
        self.lines = self._raw_gen_count()
        self.line = 0

    def __del__(self):
        self.f_head.close()

    def progress(self):
        return (100.0 * self.line) / self.lines

    def raw_consume_line(self):
        self.line += 1
        return self.f_head.readline()

    def consume_line(self):
        self.line += 1
        return self.f_head.readline().rstrip()

    def raw_peek_line(self):
        pos = self.f_head.tell()
        line = self.f_head.readline()
        self.f_head.seek(pos)
        return line

    def peek_line(self):
        pos = self.f_head.tell()
        line = self.f_head.readline().rstrip()
        self.f_head.seek(pos)
        return line

    def advance_line(self):
        self.raw_consume_line()
        return self.peek_line()

    def _raw_gen_count(self):
        def _make_gen(reader):
            b = reader(1024 * 1024)
            while b:
                yield b
                b = reader(1024 * 1024)

        f = open(self.filename, 'rb')
        f_gen = _make_gen(f.raw.read)
        lines = sum(buf.count(b'\n') for buf in f_gen)
        f.close()
        return lines
