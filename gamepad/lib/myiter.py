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


class MyIter(object):
    """
    Iterator wrapper.
    """
    def __init__(self, data):
        self.data = data
        self.idx = 0

    def __iter__(self):
        return self

    def __next__(self):
        if self.idx < len(self.data):
            elem = self.data[self.idx]
            self.idx += 1
            return elem
        else:
            raise StopIteration

    def has_next(self):
        return self.idx < len(self.data)

    def peek(self):
        return self.data[self.idx]

    def lookahead(self, n):
        return self.data[self.idx + n]
